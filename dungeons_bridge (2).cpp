// dungeons_bridge.cpp - v3
//
// FIXES THE THREADING BUG: ProcessEvent crashed (access violation) when
// called directly from our pipe-server thread, with BOTH the vtable-slot
// guess (64) and the direct RVA from the real Dumper-7 Basic.hpp
// (0x01244C30) - both identical crashes. That rules out "wrong address"
// and points at thread affinity: ProcessEvent drives full Blueprint VM
// execution, which (unlike a simple utility like AppendString, which DID
// work fine off-thread) has real thread-safety requirements tied to the
// game's own thread.
//
// FIX: hook IDXGISwapChain::Present (via MinHook) - guaranteed to run on
// the correct thread every frame. The pipe thread queues a call request
// and blocks (with a timeout) on a condition variable; the Present hook
// drains the queue and does the actual ProcessEvent call safely, then
// signals the waiting pipe thread with the result.
//
// REQUIRES MinHook (https://github.com/TsudaKageyu/minhook):
//   Option A (vcpkg, easiest):
//     vcpkg install minhook:x64-windows-static
//     cl /LD /EHsc dungeons_bridge.cpp /I <vcpkg>\installed\x64-windows-static\include ^
//        /link d3d11.lib dxgi.lib <vcpkg>\installed\x64-windows-static\lib\libMinHook.lib ^
//        /OUT:dungeons_bridge.dll
//   Option B (build from source):
//     Clone https://github.com/TsudaKageyu/minhook, build libMinHook.x64.lib
//     with its own project/CMake, then:
//     cl /LD /EHsc dungeons_bridge.cpp /I <minhook>\include ^
//        /link d3d11.lib dxgi.lib <minhook>\build\libMinHook.x64.lib ^
//        /OUT:dungeons_bridge.dll
//
// Both from "x64 Native Tools Command Prompt for VS 2022".

#include <windows.h>
#include <d3d11.h>
#include <dxgi.h>
#include <string>
#include <thread>
#include <mutex>
#include <condition_variable>
#include <queue>
#include <vector>
#include <set>
#include <unordered_set>
#include <algorithm>
#include <cctype>
#include <memory>
#include <cstdint>
#include <sstream>
#include <functional>
#include <atomic>

#include "MinHook.h"

#pragma comment(lib, "d3d11.lib")
#pragma comment(lib, "dxgi.lib")

// A fixed pipe name only works for a SINGLE injected game process at a
// time: CreateNamedPipeW below is called with nMaxInstances=1, so a
// second Dungeons.exe (two clients open at once, e.g. two players on the
// same machine) gets its own DLL instance trying to create a pipe of the
// SAME name, which fails outright (the first process's instance already
// holds the only slot) and just retries forever, never establishing a
// channel Python can talk to - looks exactly like "doesn't work" for
// whichever process lost the race. Making the name unique per process
// (its own PID, resolved once here at load time) means each game
// process's DLL gets its own independent pipe, and Python's side (see
// dungeons_reader.py's _pipe_name_for) computes the matching name from
// pm.process_id when connecting, so it always reaches the right one.
static std::wstring g_pipeName;

static const wchar_t* GetPipeName()
{
    if (g_pipeName.empty())
    {
        g_pipeName = L"\\\\.\\pipe\\dungeons_bridge_" + std::to_wstring(GetCurrentProcessId());
    }
    return g_pipeName.c_str();
}

// ---- Copied directly from the real Dumper-7 Basic.hpp - not guessed ----
namespace Offsets
{
    struct OffsetSet
    {
        int32_t GObjects;
        int32_t AppendString;
        int32_t ProcessEvent;
        int32_t GWorld;
    };

    // "steam" received a game update that moved these RVAs - confirmed via
    // a fresh Dumper-7 dump of the updated binary. "microsoft_store" and
    // "minecraft_launcher" are both still on the OLDER, pre-update build
    // (the values this whole namespace used to hardcode unconditionally),
    // confirmed via their own separate Dumper-7 dumps.
    constexpr OffsetSet Steam         = { 0x04696848, 0x010C19A0, 0x01246E10, 0x04795230 };
    constexpr OffsetSet MinecraftLauncher = { 0x046556C8, 0x010BF7C0, 0x01244C30, 0x047540B0 };
    constexpr OffsetSet MsStore       = { 0x046556C8, 0x010BF7C0, 0x01244C30, 0x047540B0 };

    // Mutable at runtime - set once by ReadGameStoreConfig() during
    // SetupHookThread, before any of these offsets are actually used.
    // Defaults to Steam; ReadGameStoreConfig overwrites this from
    // game_store.json (the same file dungeons_reader.py's
    // load_game_store()/save_game_store() read and write) if present.
    // This DLL previously hardcoded a single OffsetSet unconditionally
    // (matching only Microsoft Store/Minecraft Launcher) while
    // dungeons_reader.py already had full per-store support - meaning a
    // Steam player's Python side correctly selected Steam's offsets while
    // this DLL silently kept using the wrong ones regardless, hooking
    // ProcessEvent/AppendString/GObjects at addresses that don't
    // correspond to Steam's actual binary layout at all. That mismatch is
    // a strong candidate for crashes on any storefront other than the one
    // these values happened to be hardcoded for.
    static OffsetSet Active = Steam;
}



struct FUObjectItem
{
    void* Object;          // 0x0000
    uint8_t Pad_8[0x10];   // 0x0008
};

class TUObjectArray
{
public:
    static constexpr int32_t ElementsPerChunk = 0x10000;

    FUObjectItem** Objects;
    uint8_t Pad_8[0x8];
    int32_t MaxElements;
    int32_t NumElements;
    int32_t MaxChunks;
    int32_t NumChunks;

    int32_t Num() const { return NumElements; }

    void* GetByIndex(int32_t Index) const
    {
        const int32_t ChunkIndex = Index / ElementsPerChunk;
        const int32_t InChunkIdx = Index % ElementsPerChunk;

        if (Index < 0 || ChunkIndex >= NumChunks || Index >= NumElements)
            return nullptr;

        FUObjectItem* ChunkPtr = Objects[ChunkIndex];
        if (!ChunkPtr)
            return nullptr;

        return ChunkPtr[InChunkIdx].Object;
    }
};

struct SimpleFName
{
    int32_t ComparisonIndex;
    int32_t Number;
};

struct SimpleFString
{
    wchar_t* Data;
    int32_t Num;
    int32_t Max;
};

typedef void(*AppendStringFn)(const SimpleFName*, SimpleFString&);
typedef void(*ProcessEventFn)(void* self, void* function, void* params);

// UE4's own NAME_SIZE is 1024 TCHARs - the max length of a single FName's
// PLAIN string alone, before any "_N" instance-number suffix is appended
// on top of that. Our resolve buffer needs real headroom past NAME_SIZE,
// not exactly NAME_SIZE, because SimpleFString is a stack-backed stand-in
// for a real (heap-backed) FString: if AppendString ever decides the
// result doesn't fit in Max, it tries to grow the array through the
// engine's own allocator on our (non-heap) pointer - undefined behavior.
// Sized well past any realistic "PlainName_2147483647"-style worst case.
static constexpr int32_t NAME_RESOLVE_BUFFER_SIZE = 4096;

// ---- Debug logging - file-based since the pipe isn't always connected
// when something goes wrong at startup, and this needs to capture info
// from very early in the DLL's life. Written next to the DLL itself,
// via its own module handle - a bare relative filename would resolve
// against the HOST PROCESS's working directory (the game's own install
// folder), not wherever this DLL physically sits, since an injected DLL
// inherits the host's cwd rather than having one of its own.

static std::mutex g_logMutex;
static HMODULE g_ownModule = nullptr;

static std::string GetLogPath()
{
    char path[MAX_PATH] = {};
    if (g_ownModule && GetModuleFileNameA(g_ownModule, path, MAX_PATH))
    {
        std::string s(path);
        size_t slash = s.find_last_of("\\/");
        if (slash != std::string::npos)
            return s.substr(0, slash + 1) + "dungeons_bridge_debug.log";
    }
    return "dungeons_bridge_debug.log";  // fallback - better than nothing
}

static void LogLine(const std::string& line)
{
    std::lock_guard<std::mutex> lock(g_logMutex);
    FILE* f = nullptr;
    fopen_s(&f, GetLogPath().c_str(), "a");
    if (f)
    {
        // PID + timestamp on every single line - this file accumulates
        // across every launch/relaunch forever (never rotated/cleared),
        // and correlating a specific crash dump's PID/SecondsSinceStart
        // against "which of these many SetupHookThread sessions was it"
        // has repeatedly cost real diagnostic time this project. Cheap
        // to always include, so no reason it should ever be optional.
        SYSTEMTIME st;
        GetLocalTime(&st);
        fprintf(f, "[PID=%lu %04d-%02d-%02d %02d:%02d:%02d.%03d] %s\n",
                GetCurrentProcessId(), st.wYear, st.wMonth, st.wDay,
                st.wHour, st.wMinute, st.wSecond, st.wMilliseconds,
                line.c_str());
        fclose(f);
    }
}

// Same absolute path dungeons_ap_client.py's DATA_DIR and
// dungeons_reader.py's GAME_STORE_FILE both resolve to
// (%LOCALAPPDATA%\MCDungeonsAP\game_store.json). Only ever READS this
// file - it's written by dungeons_reader.py's save_game_store()/the
// /set_store client command. Must run before ANY Offsets::Active usage.
static void ReadGameStoreConfig()
{
    char localAppData[MAX_PATH] = {};
    DWORD len = GetEnvironmentVariableA("LOCALAPPDATA", localAppData, MAX_PATH);
    std::string path = (len > 0 && len < MAX_PATH)
        ? std::string(localAppData) + "\\MCDungeonsAP\\game_store.json"
        : "";
    std::string store = "steam";
    if (!path.empty())
    {
        FILE* f = nullptr;
        fopen_s(&f, path.c_str(), "rb");
        if (f)
        {
            char buf[256] = {};
            size_t n = fread(buf, 1, sizeof(buf) - 1, f);
            fclose(f);
            std::string content(buf, n);
            // Minimal hand-rolled parse - avoids pulling in a JSON library
            // for one string field. Looks for "store": "<value>".
            size_t keyPos = content.find("\"store\"");
            if (keyPos != std::string::npos)
            {
                size_t colonPos = content.find(':', keyPos);
                size_t firstQuote = content.find('"', colonPos + 1);
                size_t secondQuote = (firstQuote != std::string::npos)
                    ? content.find('"', firstQuote + 1) : std::string::npos;
                if (firstQuote != std::string::npos && secondQuote != std::string::npos)
                    store = content.substr(firstQuote + 1, secondQuote - firstQuote - 1);
            }
        }
    }
    LogLine("Game store: '" + store + "'");
    if (store == "minecraft_launcher")
        Offsets::Active = Offsets::MinecraftLauncher;
    else if (store == "microsoft_store")
        Offsets::Active = Offsets::MsStore;
    else
        Offsets::Active = Offsets::Steam;
}

static uintptr_t GetImageBase()
{
    return reinterpret_cast<uintptr_t>(GetModuleHandle(0));
}

static uint64_t GetCurrentWorldPtr()
{
    // Read directly - this code runs INSIDE the target process (injected),
    // so no cross-process ReadProcessMemory is needed, unlike pymem's
    // out-of-process reads of this exact same global on the Python side.
    return *reinterpret_cast<uint64_t*>(GetImageBase() + Offsets::Active.GWorld);
}

static TUObjectArray* GetGObjects()
{
    return reinterpret_cast<TUObjectArray*>(GetImageBase() + Offsets::Active.GObjects);
}

static AppendStringFn GetAppendStringFn()
{
    return reinterpret_cast<AppendStringFn>(GetImageBase() + Offsets::Active.AppendString);
}

static ProcessEventFn GetProcessEventFn()
{
    return reinterpret_cast<ProcessEventFn>(GetImageBase() + Offsets::Active.ProcessEvent);
}

// ---- name resolution (unchanged from v2 - AppendString works fine off-thread) ----

static bool TryResolveName(int32_t comparisonIndex, wchar_t* outBuffer, int32_t bufferSize, int32_t& outLen)
{
    // Preventive sanity check added after a crash traced (via a symbolized
    // dump - see this function's __try below, which is confirmed NOT
    // sufficient on its own) to this exact call into the game's own
    // AppendString. Root cause unconfirmed - comparisonIndex is a plain
    // int32_t that arrived over the pipe from a class_name_index gathered
    // during an earlier GObjects scan, so a corrupted read anywhere
    // upstream (the very kind of thing the zone-transition GObjects-walk
    // hardening elsewhere in this file targets) could hand this function
    // outright garbage. What IS confirmed: when the game's own crash
    // reporter (the "UE4CC" dumps) intercepts an exception raised inside
    // Unreal's own code before this function's local __except gets a
    // chance, the __except below cannot prevent the crash - it can only
    // catch exceptions that are still live by the time SEH unwinding
    // reaches this frame. A garbage index is exactly the kind of input
    // that should never reach AppendString in the first place, independent
    // of whether __except could have caught its consequences - this bound
    // is deliberately generous (FNamePool blocks cap at FNAME_MAX_BLOCKS
    // shifted by FNAME_BLOCK_OFFSET_BITS elsewhere in this file), just
    // enough to reject obviously-impossible values.
    if (comparisonIndex < 0 || comparisonIndex >= (8192 << 16))
        return false;

    __try
    {
        SimpleFName name{ comparisonIndex, 0 };
        SimpleFString str{ outBuffer, 0, bufferSize };
        GetAppendStringFn()(&name, str);
        outLen = str.Num;
        return true;
    }
    __except (EXCEPTION_EXECUTE_HANDLER)
    {
        return false;
    }
}

static bool TryReadOuterAndCount(void* objPtr, uintptr_t& outOuter, int32_t& outCount)
{
    __try
    {
        uintptr_t obj = reinterpret_cast<uintptr_t>(objPtr);
        outOuter = *reinterpret_cast<uintptr_t*>(obj + 0x20);
        outCount = *reinterpret_cast<int32_t*>(obj + 0x1FC);
        return true;
    }
    __except (EXCEPTION_EXECUTE_HANDLER)
    {
        return false;
    }
}

// Added after a beta tester's crash during a full-GObjects scan
// (FindObjectsWithOuter, used by find_function_on_class's class-hierarchy
// walk) - the per-object dereference inside the scan loop
// (TryReadOuterAndCount above) was already protected, but the array-walk
// machinery itself (GetGObjects()->Num(), ->GetByIndex()) was not. During a
// zone transition, this engine tears down and recreates a large chunk of
// its object graph in one burst (see the earlier discussion of loading-
// screen instability) - the chunk array TUObjectArray::Objects can itself
// be mid-reallocation/resize at exactly the moment a full scan is walking
// it, and unlike an individual object's fields, that's not something a
// per-element __try alone protects against.
static bool TryGetGObjectsCount(TUObjectArray* arr, int32_t& outNum)
{
    __try
    {
        outNum = arr->Num();
        return true;
    }
    __except (EXCEPTION_EXECUTE_HANDLER)
    {
        return false;
    }
}

// Sentinel-aware plausibility check - a bare `if (ptr)` truthy check
// misses -1/all-0xFF sentinel values (confirmed as a real, recurring
// failure mode of GWorld and similar globals during zone transitions),
// since -1 is truthy. Also rejects tiny values that are never real heap/
// image pointers (catches 0/1/2/etc-style garbage without needing a
// real address-range check).
static bool IsPlausiblePointer(uint64_t ptr)
{
    return ptr > 0x10000 && ptr != static_cast<uint64_t>(-1);
}

// PersistentLevel check (UWorld+0x30, confirmed offset - same chain
// dungeons_reader.py documents and uses for the same purpose). Added
// for a crash confirmed occurring even before the main menu appears,
// when GObjects is already large (the engine loads huge numbers of
// internal classes during boot, long before showing anything) and
// GWorld/Pawn can individually look plausible without representing a
// genuinely playable world. A real UWorld always has a PersistentLevel;
// an early boot-time placeholder is a much safer bet not to.
static bool HasPersistentLevel()
{
    __try
    {
        uint64_t world = GetCurrentWorldPtr();
        if (!IsPlausiblePointer(world))
            return false;
        uint64_t persistentLevel = *reinterpret_cast<uint64_t*>(world + 0x30);
        return IsPlausiblePointer(persistentLevel);
    }
    __except (EXCEPTION_EXECUTE_HANDLER)
    {
        return false;
    }
}

// GWorld -> GameInstance -> LocalPlayers[0] -> PlayerController -> Pawn,
// same chain and same confirmed-working offsets as dungeons_reader.py's
// get_pawn() (0x160/0x38/0x30/0x360) - not a new lookup, just porting an
// already-proven chain natively. Added for a crash occurring specifically
// at the main-menu/character-select screen: that screen already has
// plenty of its own UI UObjects loaded (past any GObjects-count floor)
// and its own valid (if not gameplay-relevant) UWorld+PersistentLevel,
// so neither check above catches that window on its own - both pass
// happily before a character is even picked. __try-wrapped as a whole
// (POD-only) so an unmapped read at any hop returns "no Pawn" cleanly.
static bool HasLocalPawn()
{
    __try
    {
        uint64_t world = GetCurrentWorldPtr();
        if (!IsPlausiblePointer(world))
            return false;
        uint64_t gameInstance = *reinterpret_cast<uint64_t*>(world + 0x160);
        if (!IsPlausiblePointer(gameInstance))
            return false;
        uint64_t localPlayersData = *reinterpret_cast<uint64_t*>(gameInstance + 0x38);
        if (!IsPlausiblePointer(localPlayersData))
            return false;
        uint64_t localPlayer = *reinterpret_cast<uint64_t*>(localPlayersData);
        if (!IsPlausiblePointer(localPlayer))
            return false;
        uint64_t playerController = *reinterpret_cast<uint64_t*>(localPlayer + 0x30);
        if (!IsPlausiblePointer(playerController))
            return false;
        uint64_t pawn = *reinterpret_cast<uint64_t*>(playerController + 0x360);
        return IsPlausiblePointer(pawn);
    }
    __except (EXCEPTION_EXECUTE_HANDLER)
    {
        return false;
    }
}

static std::atomic<bool> g_loggedGObjectsCount{ false };

static bool IsEngineReadyForClassification()
{
    TUObjectArray* gObjects = GetGObjects();
    int32_t count = 0;
    if (!gObjects || !TryGetGObjectsCount(gObjects, count))
        return false;

    bool expected = false;
    if (count > 0 && g_loggedGObjectsCount.compare_exchange_strong(expected, true))
    {
        LogLine("IsEngineReadyForClassification: first nonzero GObjects count seen = " +
                std::to_string(count) + " (threshold is currently 50000)");
    }

    // 50000: real data showed GObjects reaching ~250000-600000 during
    // ordinary gameplay - comfortably past this floor, while a genuine
    // pre-boot splash-screen moment (the original crash this gate was
    // added for) sits far below it.
    if (count <= 50000)
        return false;

    if (!HasLocalPawn())
        return false;

    if (!HasPersistentLevel())
        return false;

    return true;
}

static bool TryGetByIndexSafe(TUObjectArray* arr, int32_t index, void*& outPtr)
{
    __try
    {
        outPtr = arr->GetByIndex(index);
        return true;
    }
    __except (EXCEPTION_EXECUTE_HANDLER)
    {
        return false;
    }
}

static bool TryReadComparisonIndex(void* objPtr, int32_t& outIndex)
{
    __try
    {
        uintptr_t obj = reinterpret_cast<uintptr_t>(objPtr);
        outIndex = *reinterpret_cast<int32_t*>(obj + 0x18);
        return true;
    }
    __except (EXCEPTION_EXECUTE_HANDLER)
    {
        return false;
    }
}

static bool TryReadClassPtr(void* objPtr, void*& outClassPtr)
{
    __try
    {
        uintptr_t obj = reinterpret_cast<uintptr_t>(objPtr);
        outClassPtr = *reinterpret_cast<void**>(obj + 0x10);   // UObject::ClassPrivate
        return true;
    }
    __except (EXCEPTION_EXECUTE_HANDLER)
    {
        return false;
    }
}

static bool TryReadOuterPtr(void* objPtr, void*& outOuterPtr)
{
    __try
    {
        uintptr_t obj = reinterpret_cast<uintptr_t>(objPtr);
        outOuterPtr = *reinterpret_cast<void**>(obj + 0x20);   // UObject::OuterPrivate
        return true;
    }
    __except (EXCEPTION_EXECUTE_HANDLER)
    {
        return false;
    }
}

static bool TryGetObjectName(void* objPtr, std::string& outName)
{
    int32_t comparisonIndex = 0;
    if (!TryReadComparisonIndex(objPtr, comparisonIndex))
        return false;

    wchar_t buffer[NAME_RESOLVE_BUFFER_SIZE];
    int32_t len = 0;
    if (!TryResolveName(comparisonIndex, buffer, NAME_RESOLVE_BUFFER_SIZE, len))
        return false;

    if (len <= 0)
        return false;

    int utf8Len = WideCharToMultiByte(CP_UTF8, 0, buffer, len, nullptr, 0, nullptr, nullptr);
    if (utf8Len <= 0)
        return false;

    std::string result(utf8Len, '\0');
    WideCharToMultiByte(CP_UTF8, 0, buffer, len, &result[0], utf8Len, nullptr, nullptr);
    // strip a trailing null terminator if AppendString's Num included it
    // (same reason the Python side does .rstrip("\x00") on resolve_name results)
    while (!result.empty() && result.back() == '\0')
        result.pop_back();
    outName = result;
    return true;
}

static bool TryGetClassName(void* objPtr, std::string& outName)
{
    void* classPtr = nullptr;
    if (!TryReadClassPtr(objPtr, classPtr) || !classPtr)
        return false;
    return TryGetObjectName(classPtr, outName);
}

// Forward-declared: defined further below, but HandleResolveName (right
// here) needs it before that point in the file - same forward-reference
// situation as GetGObjects() hit earlier in this project's history.
static void QueueAndWaitForRenderThread(const std::function<void()>& work);

std::string HandleResolveName(const std::string& hexIndex)
{
    int32_t comparisonIndex = 0;
    try
    {
        comparisonIndex = static_cast<int32_t>(std::stoul(hexIndex, nullptr, 16));
    }
    catch (...)
    {
        return "ERROR:could not parse index";
    }

    // MUST run on the game's own thread, same constraint HandleFindByName
    // already respects for its GObjects walk (see that function and
    // QueueAndWaitForRenderThread's own comment) - AppendString is the
    // real engine function TryResolveName calls into, and this handler
    // used to call it DIRECTLY from PipeServerThread (a thread the
    // engine never expected to call into its own FName/AppendString
    // machinery from at all), unlike every other AppendString-calling
    // path in this file. resolve_fname_via_pipe (dungeons_reader.py)
    // routes through this handler hundreds of times per session via
    // resolve_gamebp_class_index alone (15 calls/tick, accumulating into
    // the hundreds) - repeated off-thread corruption of internal engine
    // name-resolution state is a strong match for a crash that recurs
    // with an identical signature regardless of what specifically
    // triggered it, only after several minutes of accumulated calls.
    auto result = std::make_shared<std::string>("ERROR:did not run");
    QueueAndWaitForRenderThread([comparisonIndex, result]()
    {
        wchar_t buffer[NAME_RESOLVE_BUFFER_SIZE];
        int32_t len = 0;
        if (!TryResolveName(comparisonIndex, buffer, NAME_RESOLVE_BUFFER_SIZE, len))
        {
            *result = "ERROR:AppendString call faulted";
            return;
        }
        if (len <= 0)
        {
            *result = "ERROR:empty result (invalid index?)";
            return;
        }
        int utf8Len = WideCharToMultiByte(CP_UTF8, 0, buffer, len, nullptr, 0, nullptr, nullptr);
        if (utf8Len <= 0)
        {
            *result = "ERROR:UTF8 conversion failed";
            return;
        }
        std::string utf8(utf8Len, '\0');
        WideCharToMultiByte(CP_UTF8, 0, buffer, len, &utf8[0], utf8Len, nullptr, nullptr);
        *result = "NAME:" + utf8;
    });
    return *result;
}

// ---- generic thread-hopped work (for anything besides ProcessEvent that
// also needs to run on the game's own thread - the GObjects walk/AppendString
// loop turned out to need this too, same root cause as ProcessEvent did) ----

static std::mutex g_genericQueueMutex;
static std::queue<std::function<void()>> g_pendingGenericWork;

static void QueueAndWaitForRenderThread(const std::function<void()>& work)
{
    auto localMutex = std::make_shared<std::mutex>();
    auto localCv = std::make_shared<std::condition_variable>();
    auto done = std::make_shared<bool>(false);

    std::function<void()> wrapped = [work, localMutex, localCv, done]()
    {
        work();
        {
            std::lock_guard<std::mutex> lock(*localMutex);
            *done = true;
        }
        localCv->notify_all();
    };

    {
        std::lock_guard<std::mutex> lock(g_genericQueueMutex);
        g_pendingGenericWork.push(wrapped);
    }

    std::unique_lock<std::mutex> lock(*localMutex);
    localCv->wait_for(lock, std::chrono::seconds(10), [&] { return *done; });
}

static void DrainGenericWork()
{
    std::queue<std::function<void()>> localQueue;
    {
        std::lock_guard<std::mutex> lock(g_genericQueueMutex);
        std::swap(localQueue, g_pendingGenericWork);
    }
    while (!localQueue.empty())
    {
        localQueue.front()();
        localQueue.pop();
    }
}

std::string HandleFindByName(const std::string& targetName)
{
    auto result = std::make_shared<std::string>("ERROR:did not run");

    QueueAndWaitForRenderThread([targetName, result]()
    {
        TUObjectArray* gObjects = GetGObjects();
        if (!gObjects)
        {
            *result = "ERROR:could not resolve GObjects";
            return;
        }

        std::ostringstream matches;
        int matchCount = 0;
        int32_t total = 0;
        if (!TryGetGObjectsCount(gObjects, total))
        {
            *result = "ERROR:GObjects count read faulted (likely mid zone-transition) - retry later";
            return;
        }

        for (int32_t i = 0; i < total; ++i)
        {
            void* objPtr = nullptr;
            if (!TryGetByIndexSafe(gObjects, i, objPtr))
                continue;  // this slot's chunk faulted - skip it, don't abort the whole scan
            if (!objPtr)
                continue;

            std::string name;
            if (!TryGetObjectName(objPtr, name))
                continue;

            if (name == targetName)
            {
                if (matchCount > 0)
                    matches << ",";
                matches << std::hex << reinterpret_cast<uintptr_t>(objPtr);
                matchCount++;
            }
        }

        std::ostringstream out;
        out << "FOUND:" << matchCount;
        if (matchCount > 0)
            out << "|" << matches.str();
        *result = out.str();
    });

    return *result;
}

// Finds every live instance of a given CLASS (by class name, e.g.
// "UMG_MissionLockedPanel_C") - unlike HandleFindByName above, which
// matches an individual object's own instance name. Modeled directly on
// HandleFindByName's structure (same GObjects-walk safety, same render-
// thread requirement - TryGetClassName below calls TryGetObjectName on
// the class pointer, which goes through TryResolveName/AppendString, so
// this has the exact same off-thread-AppendString hazard HandleFindByName
// and HandleResolveName both already guard against via
// QueueAndWaitForRenderThread).
std::string HandleFindByClass(const std::string& targetClassName)
{
    auto result = std::make_shared<std::string>("ERROR:did not run");

    QueueAndWaitForRenderThread([targetClassName, result]()
    {
        TUObjectArray* gObjects = GetGObjects();
        if (!gObjects)
        {
            *result = "ERROR:could not resolve GObjects";
            return;
        }

        std::ostringstream matches;
        int matchCount = 0;
        int32_t total = 0;
        if (!TryGetGObjectsCount(gObjects, total))
        {
            *result = "ERROR:GObjects count read faulted (likely mid zone-transition) - retry later";
            return;
        }

        for (int32_t i = 0; i < total; ++i)
        {
            void* objPtr = nullptr;
            if (!TryGetByIndexSafe(gObjects, i, objPtr))
                continue;  // this slot's chunk faulted - skip it, don't abort the whole scan
            if (!objPtr)
                continue;

            std::string className;
            if (!TryGetClassName(objPtr, className))
                continue;

            if (className == targetClassName)
            {
                if (matchCount > 0)
                    matches << ",";
                matches << std::hex << reinterpret_cast<uintptr_t>(objPtr);
                matchCount++;
            }
        }

        std::ostringstream out;
        out << "FOUND:" << matchCount;
        if (matchCount > 0)
            out << "|" << matches.str();
        *result = out.str();
    });

    return *result;
}

std::string FindObjectsWithOuter(uintptr_t targetOuter)
{
    auto result = std::make_shared<std::string>("ERROR:did not run");

    QueueAndWaitForRenderThread([targetOuter, result]()
    {
        TUObjectArray* gObjects = GetGObjects();
        if (!gObjects)
        {
            *result = "ERROR:could not resolve GObjects";
            return;
        }

        std::ostringstream matches;
        int matchCount = 0;
        int32_t total = 0;
        if (!TryGetGObjectsCount(gObjects, total))
        {
            *result = "ERROR:GObjects count read faulted (likely mid zone-transition) - retry later";
            return;
        }

        for (int32_t i = 0; i < total; ++i)
        {
            void* objPtr = nullptr;
            if (!TryGetByIndexSafe(gObjects, i, objPtr))
                continue;  // this slot's chunk faulted - skip it, don't abort the whole scan
            if (!objPtr)
                continue;

            uintptr_t outer = 0;
            int32_t countAsItemSlot = 0;
            if (!TryReadOuterAndCount(objPtr, outer, countAsItemSlot))
                continue;

            if (outer == targetOuter)
            {
                if (matchCount > 0)
                    matches << ",";
                matches << std::hex << reinterpret_cast<uintptr_t>(objPtr) << ":" << std::dec << countAsItemSlot;
                matchCount++;
            }
        }

        std::ostringstream out;
        out << "FOUND:" << matchCount;
        if (matchCount > 0)
            out << "|" << matches.str();
        *result = out.str();
    });

    return *result;
}

// ---- NEW: thread-hopped ProcessEvent calling ----

struct CallRequest
{
    uintptr_t objectAddr;
    uintptr_t functionAddr;
    size_t parmsSize;
    std::vector<uint8_t> parms;   // in/out - filled by the caller, overwritten in place by ProcessEvent
    bool done = false;
    bool faulted = false;
    DWORD exceptionCode = 0;
};

static std::mutex g_queueMutex;
static std::queue<std::shared_ptr<CallRequest>> g_pendingCalls;

static std::mutex g_resultMutex;
static std::condition_variable g_resultCv;

// Isolated POD-only helper - no C++ objects with destructors in scope,
// same MSVC restriction as everywhere else __try is used in this file.
// Uses the comma-operator trick in the filter expression to actually
// capture the exception code (GetExceptionCode() is only valid inside
// the filter expression itself, not the __except body).
static bool TryProcessEventCall(uintptr_t objectAddr, uintptr_t functionAddr, uint8_t* parms, DWORD& outExceptionCode)
{
    DWORD code = 0;
    __try
    {
        GetProcessEventFn()(reinterpret_cast<void*>(objectAddr), reinterpret_cast<void*>(functionAddr), parms);
        return true;
    }
    __except ((code = GetExceptionCode()), EXCEPTION_EXECUTE_HANDLER)
    {
        outExceptionCode = code;
        return false;
    }
}

// Runs INSIDE the Present hook - i.e. on the correct thread. Drains
// whatever's queued and services each one synchronously before letting
// the frame continue.
static void DrainPendingCalls()
{
    std::queue<std::shared_ptr<CallRequest>> localQueue;
    {
        std::lock_guard<std::mutex> lock(g_queueMutex);
        std::swap(localQueue, g_pendingCalls);
    }

    while (!localQueue.empty())
    {
        auto req = localQueue.front();
        localQueue.pop();

        DWORD exceptionCode = 0;
        bool ok = TryProcessEventCall(req->objectAddr, req->functionAddr, req->parms.data(), exceptionCode);

        {
            std::lock_guard<std::mutex> lock(g_resultMutex);
            req->done = true;
            req->faulted = !ok;
            req->exceptionCode = exceptionCode;
        }
        g_resultCv.notify_all();
    }
}

// Called from the pipe thread - queues the request, then blocks (with a
// timeout, in case the game is paused/minimized and Present stops
// firing) until the render thread services it.
std::string HandleCall(const std::string& args)
{
    std::istringstream iss(args);
    std::string objHex, funcHex, sizeHex;
    if (!(iss >> objHex >> funcHex >> sizeHex))
        return "ERROR bad request format (expected: CALL <obj_hex> <func_hex> <size_hex>)";

    uintptr_t objectAddr, functionAddr;
    size_t parmsSize;
    try
    {
        objectAddr = static_cast<uintptr_t>(std::stoull(objHex, nullptr, 16));
        functionAddr = static_cast<uintptr_t>(std::stoull(funcHex, nullptr, 16));
        parmsSize = static_cast<size_t>(std::stoull(sizeHex, nullptr, 16));
    }
    catch (...)
    {
        return "ERROR could not parse request";
    }

    if (parmsSize == 0 || parmsSize > 0x10000)
        return "ERROR parms_size out of sane range";

    auto req = std::make_shared<CallRequest>();
    req->objectAddr = objectAddr;
    req->functionAddr = functionAddr;
    req->parmsSize = parmsSize;
    req->parms.resize(parmsSize, 0);

    {
        std::lock_guard<std::mutex> lock(g_queueMutex);
        g_pendingCalls.push(req);
    }

    std::unique_lock<std::mutex> lock(g_resultMutex);
    bool serviced = g_resultCv.wait_for(lock, std::chrono::seconds(5), [&] { return req->done; });

    if (!serviced)
        return "ERROR timed out waiting for render thread (is the game minimized/frozen?)";

    if (req->faulted)
    {
        std::ostringstream err;
        err << "ERROR exception during call (code 0x" << std::hex << req->exceptionCode << ")";
        return err.str();
    }

    std::ostringstream out;
    out << "OK ";
    for (uint8_t b : req->parms)
    {
        char buf[3];
        sprintf_s(buf, "%02X", b);
        out << buf;
    }
    return out.str();
}

// CALLDATA <obj_hex> <func_hex> <parms_hex> - same as CALL, but the parms
// buffer starts as the ACTUAL BYTES given instead of zeros. Needed for
// functions that take real input (like ClientAddItem's FInventoryItemData
// parameter), as opposed to GetDisplayNameText-style calls that only need
// a zeroed buffer for an out-parameter.
std::string HandleCallData(const std::string& args)
{
    std::istringstream iss(args);
    std::string objHex, funcHex, parmsHex;
    if (!(iss >> objHex >> funcHex >> parmsHex))
        return "ERROR bad request format (expected: CALLDATA <obj_hex> <func_hex> <parms_hex>)";

    uintptr_t objectAddr, functionAddr;
    try
    {
        objectAddr = static_cast<uintptr_t>(std::stoull(objHex, nullptr, 16));
        functionAddr = static_cast<uintptr_t>(std::stoull(funcHex, nullptr, 16));
    }
    catch (...)
    {
        return "ERROR could not parse request";
    }

    if (parmsHex.size() % 2 != 0)
        return "ERROR parms_hex must have an even number of hex digits";

    size_t parmsSize = parmsHex.size() / 2;
    if (parmsSize == 0 || parmsSize > 0x10000)
        return "ERROR parms_size out of sane range";

    auto req = std::make_shared<CallRequest>();
    req->objectAddr = objectAddr;
    req->functionAddr = functionAddr;
    req->parmsSize = parmsSize;
    req->parms.resize(parmsSize, 0);

    for (size_t i = 0; i < parmsSize; ++i)
    {
        std::string byteStr = parmsHex.substr(i * 2, 2);
        req->parms[i] = static_cast<uint8_t>(std::stoul(byteStr, nullptr, 16));
    }

    {
        std::lock_guard<std::mutex> lock(g_queueMutex);
        g_pendingCalls.push(req);
    }

    std::unique_lock<std::mutex> lock(g_resultMutex);
    bool serviced = g_resultCv.wait_for(lock, std::chrono::seconds(5), [&] { return req->done; });

    if (!serviced)
        return "ERROR timed out waiting for render thread (is the game minimized/frozen?)";

    if (req->faulted)
    {
        std::ostringstream err;
        err << "ERROR exception during call (code 0x" << std::hex << req->exceptionCode << ")";
        return err.str();
    }

    std::ostringstream out;
    out << "OK ";
    for (uint8_t b : req->parms)
    {
        char buf[3];
        sprintf_s(buf, "%02X", b);
        out << buf;
    }
    return out.str();
}

// ---- Chest-open detection via a global ProcessEvent hook ----
// Confirmed via live logging (dungeons_bridge_debug.log): OnOpenLootChest
// never actually fires - it's a reflected UFunction that exists in the
// SDK but isn't wired to any real code path in this build. What DOES
// fire, confirmed against real opens of a Fancy chest and a Supply
// station: an "OnInteracted"-suffixed bound-event function (there are
// several distinct ones per interactable-component type - "Clicky",
// "InteractableComp", "ClickyComponent" all seen), with `self` resolving
// directly to the real actor class - BP_FancyChest_C, BP_SupplyStation_C,
// confirmed via the SAME name-resolution machinery already proven
// reliable all session. No memory-offset guessing, no polling, no
// heuristic byte-shape matching - just the game's own class identity,
// straight from GNames.
//
// Since there are MULTIPLE distinct "OnInteracted" function pointers
// (one per component type), a single cached pointer (like the old
// OnOpenLootChest attempt) doesn't work - this classifies and caches
// PER function pointer instead, both positive and negative results, so
// after the first time any given function is seen, every future call
// through it is an O(1) hash lookup instead of a name resolve.
//
// Filtering WHICH actor classes count as "a chest" happens on the
// PYTHON side, not here - class names differ per class (Chest vs
// SupplyStation) and will differ further for Wooden/Deluxe once
// confirmed, and keeping that list in Python means updating it never
// requires recompiling/reinjecting this DLL again.

struct InteractEvent
{
    uint64_t actorAddr;
    std::string className;
    uint64_t worldPtr;  // GWorld at the exact moment of this interact - the Python side
                         // resolves this into a zone name via get_zone_name_index(pm, worldPtr),
                         // instead of relying on its own separately-polled "current zone"
                         // tracking, which could race a zone transition happening between
                         // this event firing and the event queue being drained.
};

static std::mutex g_interactEventsMutex;
static std::vector<InteractEvent> g_interactEvents;   // drained by the pipe thread via get_chest_events

// Matches the WHOLE interact family, including "OnInteract" (no "ed")
// and "OnInteracted". Confirmed live this matters for pickup BLOCKING: a Food pickup's healing effect still applied even
// though its "OnInteracted" call was correctly blocked, because the
// actual effect gets applied during the EARLIER "OnInteract" call,
// which the narrow match never saw at all. Used specifically for the
// pickup-tier blocking check - NOT for chest-open reporting, which uses
// the even narrower IsChestReportFunction below instead.
static std::mutex g_interactFamilyClassifyMutex;
static std::unordered_set<void*> g_interactFamilyFunctionPtrs;
static std::unordered_set<void*> g_nonInteractFamilyFunctionPtrs;

static bool IsInteractFamilyFunction(void* function)
{
    {
        std::lock_guard<std::mutex> lock(g_interactFamilyClassifyMutex);
        if (g_interactFamilyFunctionPtrs.count(function))
            return true;
        if (g_nonInteractFamilyFunctionPtrs.count(function))
            return false;
    }

    std::string name;
    bool isMatch = TryGetObjectName(function, name) &&
                   name.find("Interact") != std::string::npos;

    std::lock_guard<std::mutex> lock(g_interactFamilyClassifyMutex);
    if (isMatch)
    {
        g_interactFamilyFunctionPtrs.insert(function);
        LogLine("Classified new Interact-family function (blocking-eligible): " + name);
    }
    else
    {
        g_nonInteractFamilyFunctionPtrs.insert(function);
    }
    return isMatch;
}

// Narrow match for CHEST-OPEN EVENT REPORTING specifically - "OnInteract"
// but explicitly NOT "OnInteracted". Chests can fire "OnInteracted"
// multiple times per single physical open (confirmed live - e.g. once
// per item that spawns from the chest), which would double/triple-
// report one open if used for counting. "OnInteract" (the earlier
// trigger, no "ed") fires exactly once per genuine interaction attempt,
// which is what chest-open counting actually needs.
static std::mutex g_chestReportClassifyMutex;
static std::unordered_set<void*> g_chestReportFunctionPtrs;
static std::unordered_set<void*> g_nonChestReportFunctionPtrs;

static bool IsChestReportFunction(void* function)
{
    {
        std::lock_guard<std::mutex> lock(g_chestReportClassifyMutex);
        if (g_chestReportFunctionPtrs.count(function))
            return true;
        if (g_nonChestReportFunctionPtrs.count(function))
            return false;
    }

    std::string name;
    bool isMatch = TryGetObjectName(function, name) &&
                   name.find("OnInteract") != std::string::npos &&
                   name.find("OnInteracted") == std::string::npos;

    std::lock_guard<std::mutex> lock(g_chestReportClassifyMutex);
    if (isMatch)
    {
        g_chestReportFunctionPtrs.insert(function);
        LogLine("Classified new OnInteract-only (chest-reporting) function: " + name);
    }
    else
    {
        g_nonChestReportFunctionPtrs.insert(function);
    }
    return isMatch;
}

static std::string ToLowerCopy(const std::string& s)
{
    std::string out = s;
    std::transform(out.begin(), out.end(), out.begin(),
                    [](unsigned char c) { return static_cast<char>(std::tolower(c)); });
    return out;
}

static void CaptureInteractEvent(uint64_t actorAddr, const std::string& className)
{
    InteractEvent evt;
    evt.actorAddr = actorAddr;
    evt.className = className;
    evt.worldPtr = GetCurrentWorldPtr();

    std::lock_guard<std::mutex> lock(g_interactEventsMutex);
    g_interactEvents.push_back(evt);
}

// ---- Progressive pickup gating ----
// Three tiers, unlocked in order as the player receives copies of a
// progressive AP item (client-side logic, not this DLL's concern - this
// DLL just enforces whatever tier Python currently says is unlocked):
//   tier 1 = Health items (food) pickable
//   tier 2 = + Potions pickable
//   tier 3 = + TNT pickable
// Weapons, armor, artifacts, tokens, eye of ender, arrows, and any
// non-pickup interactable (UI objects like BP_MapTable_C) are NEVER
// gated, regardless of tier - returned as tier -1, meaning "not
// gateable at all, never block". Tier 3 intentionally gates ONLY TNT,
// not the broad "everything else" it used to - weapon/armor/artifact
// names vary too much to enumerate or pattern-match reliably, so
// instead of guessing which of them to gate, none of them are.
//
// Classified by NAME PATTERN, not an enumerated class list - this
// covers every pickup class in the game automatically, including ones
// never directly observed in testing yet, same philosophy as
// classify_interactable_class on the Python side. Confirmed real
// examples from live testing: BP_Food1/2/3Storable_C (health),
// BP_StrengthPotionStorable_C / BP_SwiftnessPotionStorable_C /
// BP_BackstabbersBrewStorable_C (potion - "brew" matched too, since
// Backstabber's Brew doesn't literally contain "Potion"),
// BP_TNTBoxStorable_C (TNT).
static int ClassifyPickupTier(const std::string& className)
{
    std::string lower = ToLowerCopy(className);

    if (lower.find("storable_c") == std::string::npos)
        return -1;  // not a pickup at all
    if (lower.find("food") != std::string::npos)
        return 1;
    if (lower.find("potion") != std::string::npos || lower.find("brew") != std::string::npos)
        return 2;
    if (lower.find("tnt") != std::string::npos)
        return 3;
    return -1;  // weapons, armor, artifacts, tokens, eye of ender, arrows, etc - never gated
}

// Defaults LOCKED (tier 0 - nothing beyond arrows pickable) rather than
// unlocked, so the gate fails safe: if Python's watcher hasn't connected
// yet or crashes, pickups stay blocked instead of silently becoming
// unrestricted and defeating the whole progression rule.
static std::atomic<int> g_pickupUnlockTier{ 0 };

typedef void(*ProcessEventHookFn)(void*, void*, void*);
static ProcessEventHookFn oProcessEvent = nullptr;

static std::atomic<uint64_t> g_processEventCallCount{ 0 };

// ---- Character-death detection. Same classify-and-cache pattern as
// IsChestReportFunction above, checking for the exact reflected name
// "OnCharacterDeath" (Dumper-7 SDK, ABaseCharacter::OnCharacterDeath(),
// no params - `self` is the dying actor).
//
// IMPORTANT: OnOpenLootChest looked exactly this solid on paper too - a
// genuine reflected UFunction the SDK confirms exists - and turned out to
// never actually fire via ProcessEvent in this build. Don't repeat that
// mistake blind: alongside the exact-name check, this also logs the
// first-ever sighting of ANY function whose name contains "death"
// case-insensitively, matched or not, so if OnCharacterDeath is also
// SDK-only and something differently-named is what actually fires on a
// real kill, it shows up in dungeons_bridge_debug.log instead of another
// silent dead end.
struct CharacterDeathEvent
{
    uint64_t actorAddr;
};

static std::mutex g_deathEventsMutex;
static std::vector<CharacterDeathEvent> g_deathEvents;   // drained by the pipe thread via get_death_events

static std::mutex g_deathClassifyMutex;
static std::unordered_set<void*> g_deathFunctionPtrs;       // confirmed exact "OnCharacterDeath"
static std::unordered_set<void*> g_nonDeathFunctionPtrs;    // confirmed NOT - avoids re-resolving every call
static std::unordered_set<void*> g_loggedDeathLikeFunctionPtrs;  // already logged as a "death"-ish name, don't spam

// ---- Secret-mission-unlock detection. Same classify-and-cache pattern as
// IsDeathFunction above. Confirmed via the SDK dump (Dungeons_functions.cpp):
// USecretComponent::SecretFound(AActor* SecretFinder) - fires on the
// component attached to whatever physical trigger (lever, hidden wall,
// etc) reveals a secret mission. USecretComponent::ExecuteSecretFound is
// ALSO a real UFunction in the dump (Dumper-7's wrapper-call name for the
// same BlueprintImplementableEvent, or possibly a distinct entry point) -
// classify on EITHER exact name, since it's not certain from the dump
// alone which one actually fires via ProcessEvent at runtime. Same
// unmatched-but-"secret"-ish diagnostic logging fallback as the death
// classifier, in case neither name is what really fires.
struct SecretFoundEvent
{
    uint64_t actorAddr;
    std::string className;
};

static std::mutex g_secretEventsMutex;
static std::vector<SecretFoundEvent> g_secretEvents;   // drained by the pipe thread via get_secret_events

static std::mutex g_secretClassifyMutex;
static std::unordered_set<void*> g_secretFunctionPtrs;      // confirmed exact "SecretFound" or "ExecuteSecretFound"
static std::unordered_set<void*> g_nonSecretFunctionPtrs;   // confirmed NOT - avoids re-resolving every call
static std::unordered_set<void*> g_loggedSecretLikeFunctionPtrs;  // already logged as a "secret"-ish name, don't spam

static bool IsSecretFoundFunction(void* function)
{
    {
        std::lock_guard<std::mutex> lock(g_secretClassifyMutex);
        if (g_secretFunctionPtrs.count(function))
            return true;
        if (g_nonSecretFunctionPtrs.count(function))
            return false;
    }

    std::string name;
    bool resolved = TryGetObjectName(function, name);
    bool isExactMatch = resolved && (name == "SecretFound" || name == "ExecuteSecretFound");

    if (resolved && !isExactMatch && ToLowerCopy(name).find("secret") != std::string::npos)
    {
        std::lock_guard<std::mutex> lock(g_secretClassifyMutex);
        if (!g_loggedSecretLikeFunctionPtrs.count(function))
        {
            g_loggedSecretLikeFunctionPtrs.insert(function);
            LogLine("Secret-like (but not exact 'SecretFound'/'ExecuteSecretFound') function seen: " + name);
        }
    }

    std::lock_guard<std::mutex> lock(g_secretClassifyMutex);
    if (isExactMatch)
    {
        g_secretFunctionPtrs.insert(function);
        LogLine("Classified exact SecretFound-pattern function pointer: " + name);
    }
    else
    {
        g_nonSecretFunctionPtrs.insert(function);
    }
    return isExactMatch;
}

static void CaptureSecretFoundEvent(void* self)
{
    std::string className;
    if (!TryGetClassName(self, className))
        return;

    SecretFoundEvent evt;
    evt.actorAddr = reinterpret_cast<uint64_t>(self);
    evt.className = className;

    std::lock_guard<std::mutex> lock(g_secretEventsMutex);
    g_secretEvents.push_back(evt);
}

// ---- Currency widget hook: OnValueChanged / OnCurrencyTypeChanged on
// UMG_CurrencyCounterBase_C (and its Blueprint children - UMG_EmeraldCounter_C,
// etc). Unlike the native p_currency getter defined further below (which
// needs hand-confirmed fixed offsets, and got Gold/Eyes of Ender swapped
// once already), these are real reflected UFUNCTIONs the game calls with
// the value it's ABOUT to display, directly as a parameter - no offset
// guessing at all. Useful as a cross-check against CURRENCY_OFFSETS, or
// as a fallback read path when the HUD widget is on-screen.
//
// Only fires while the relevant currency counter widget actually exists
// (HUD visible) - NOT a replacement for the always-available
// p_currency-based read/write path, just a second, offset-free source of
// truth to validate against.
//
// Defined here (before hkProcessEvent, which calls into these classifiers)
// rather than down by hkCurrencyGetter - these have nothing to do with the
// native p_currency pointer capture and don't need to sit next to it; they
// DO need to be declared before hkProcessEvent uses them below.

struct CurrencyValueEvent
{
    uint64_t widgetAddr;
    int32_t newValue;
    int32_t previousValue;
};

struct CurrencyTypeEvent
{
    uint64_t widgetAddr;
    uint32_t serializedIdIndex;  // FSerializableItemId::SerializedId's FName
                                  // ComparisonIndex - same name_index space
                                  // used everywhere else (items, zones, etc),
                                  // so the Python side can label it via the
                                  // usual name-lookup workflow.
};

static std::mutex g_currencyValueEventsMutex;
static std::vector<CurrencyValueEvent> g_currencyValueEvents;

static std::mutex g_currencyTypeEventsMutex;
static std::vector<CurrencyTypeEvent> g_currencyTypeEvents;

// Exact-name match (not a substring family match like IsInteractFamilyFunction) -
// "OnValueChanged" and "OnCurrencyTypeChanged" are specific, unambiguous event
// names, but ARE generic enough that some unrelated widget elsewhere in the
// game could coincidentally share the name "OnValueChanged" (a slider, a
// settings widget, etc). Gated additionally on the INSTANCE's class name
// containing "Counter" (case-insensitive) below, at the call site - covers
// UMG_CurrencyCounterBase_C itself plus every Blueprint child
// (UMG_EmeraldCounter_C, UMG_GoldCounter_C, UMG_EyeOfEnderCounter_C, ...)
// without needing to enumerate them by name.
static std::mutex g_currencyValueClassifyMutex;
static std::unordered_set<void*> g_currencyValueFunctionPtrs;
static std::unordered_set<void*> g_nonCurrencyValueFunctionPtrs;

static bool IsCurrencyValueChangedFunction(void* function)
{
    {
        std::lock_guard<std::mutex> lock(g_currencyValueClassifyMutex);
        if (g_currencyValueFunctionPtrs.count(function))
            return true;
        if (g_nonCurrencyValueFunctionPtrs.count(function))
            return false;
    }

    std::string name;
    bool isMatch = TryGetObjectName(function, name) && name == "OnValueChanged";

    std::lock_guard<std::mutex> lock(g_currencyValueClassifyMutex);
    if (isMatch)
    {
        g_currencyValueFunctionPtrs.insert(function);
        LogLine("Classified new OnValueChanged function (currency-widget candidate): " + name);
    }
    else
    {
        g_nonCurrencyValueFunctionPtrs.insert(function);
    }
    return isMatch;
}

static std::mutex g_currencyTypeClassifyMutex;
static std::unordered_set<void*> g_currencyTypeFunctionPtrs;
static std::unordered_set<void*> g_nonCurrencyTypeFunctionPtrs;

static bool IsCurrencyTypeChangedFunction(void* function)
{
    {
        std::lock_guard<std::mutex> lock(g_currencyTypeClassifyMutex);
        if (g_currencyTypeFunctionPtrs.count(function))
            return true;
        if (g_nonCurrencyTypeFunctionPtrs.count(function))
            return false;
    }

    std::string name;
    bool isMatch = TryGetObjectName(function, name) && name == "OnCurrencyTypeChanged";

    std::lock_guard<std::mutex> lock(g_currencyTypeClassifyMutex);
    if (isMatch)
    {
        g_currencyTypeFunctionPtrs.insert(function);
        LogLine("Classified new OnCurrencyTypeChanged function (currency-widget candidate): " + name);
    }
    else
    {
        g_nonCurrencyTypeFunctionPtrs.insert(function);
    }
    return isMatch;
}

static void CaptureCurrencyValueEvent(uint64_t widgetAddr, void* params)
{
    // Params layout: two plain (non-out) int32 parms in declared order -
    // int32 newValue @ +0x00, int32 previousValue @ +0x04. Standard UE
    // ProcessEvent params blob layout for two consecutive by-value int32s.
    CurrencyValueEvent evt;
    evt.widgetAddr = widgetAddr;
    evt.newValue = *reinterpret_cast<int32_t*>(reinterpret_cast<uint8_t*>(params) + 0x00);
    evt.previousValue = *reinterpret_cast<int32_t*>(reinterpret_cast<uint8_t*>(params) + 0x04);

    std::lock_guard<std::mutex> lock(g_currencyValueEventsMutex);
    g_currencyValueEvents.push_back(evt);
}

static void CaptureCurrencyTypeEvent(uint64_t widgetAddr, void* params)
{
    // Params layout: single FSerializableItemId (0x14 bytes) at offset 0.
    // Its SerializedId FName sits at +0x0C within that struct (see
    // Dungeons_structs.hpp's FSerializableItemId - Pad_0[0xC] then FName
    // SerializedId @ 0x0C). An FName's first 4 bytes are ComparisonIndex,
    // which is the same "name_index" numbering used for items/zones/etc
    // elsewhere in this DLL and in dungeons_reader.py.
    CurrencyTypeEvent evt;
    evt.widgetAddr = widgetAddr;
    evt.serializedIdIndex = *reinterpret_cast<uint32_t*>(reinterpret_cast<uint8_t*>(params) + 0x0C);

    std::lock_guard<std::mutex> lock(g_currencyTypeEventsMutex);
    g_currencyTypeEvents.push_back(evt);
}

static bool IsDeathFunction(void* function)
{
    {
        std::lock_guard<std::mutex> lock(g_deathClassifyMutex);
        if (g_deathFunctionPtrs.count(function))
            return true;
        if (g_nonDeathFunctionPtrs.count(function))
            return false;
    }

    std::string name;
    bool resolved = TryGetObjectName(function, name);
    bool isExactMatch = resolved && name == "OnCharacterDeath";

    if (resolved && !isExactMatch && ToLowerCopy(name).find("death") != std::string::npos)
    {
        std::lock_guard<std::mutex> lock(g_deathClassifyMutex);
        if (!g_loggedDeathLikeFunctionPtrs.count(function))
        {
            g_loggedDeathLikeFunctionPtrs.insert(function);
            LogLine("Death-like (but not exact 'OnCharacterDeath') function seen: " + name);
        }
    }

    std::lock_guard<std::mutex> lock(g_deathClassifyMutex);
    if (isExactMatch)
    {
        g_deathFunctionPtrs.insert(function);
        LogLine("Classified exact OnCharacterDeath function pointer.");
    }
    else
    {
        g_nonDeathFunctionPtrs.insert(function);
    }
    return isExactMatch;
}

static void CaptureDeathEvent(void* self)
{
    std::lock_guard<std::mutex> lock(g_deathEventsMutex);
    g_deathEvents.push_back({ reinterpret_cast<uint64_t>(self) });
}

// ---- Mission-outcome trigger detection. Same classify-and-cache pattern
// as IsDeathFunction/IsSecretFoundFunction above, but this is NOT a
// source of truth by itself - it's just a wake-up signal telling the
// Python side "a mission run just concluded somehow, go make one
// authoritative IsMissionCompleted() call right now" instead of polling
// that call every tick forever. Classifies on ANY of three exact
// reflected names, since it isn't confirmed which one(s) actually fire
// via ProcessEvent in this build:
//   - MulticastMissionFinished / MulticastGameOver: both flagged
//     (Native, Event, NetMulticast) in the SDK dump - RPC dispatch is
//     structurally guaranteed to route through ProcessEvent, same reason
//     OnCharacterDeath works.
//   - OnShowMissionVictory: flagged (Event, BlueprintEvent) - same
//     ProcessEvent guarantee via a different mechanism (blueprint-event
//     thunk instead of RPC dispatch).
// All three are OR'd together rather than picked in advance, because
// OnOpenLootChest looked exactly this solid on paper too and never
// fired. Whichever name(s) actually show up in dungeons_bridge_debug.log
// is the real answer; the other two cost nothing to leave classified.
//
// Deliberately does NOT try to guess win/loss from the trigger name or
// parse any of its parameters (FMissionFinishedSummary, ELevelNames,
// etc.) - a totem-loss failure may fire the exact same trigger as a real
// win, and guessing wrong here is exactly how a false positive gets
// reported to the AP server. The trigger only ever causes ONE
// IsMissionCompleted() confirm call on the Python side; that call is the
// only thing allowed to decide "completed or not."
struct MissionOutcomeEvent
{
    uint64_t actorAddr;
    std::string triggerName;   // which of the three fired - debug log only
};

static std::mutex g_missionOutcomeEventsMutex;
static std::vector<MissionOutcomeEvent> g_missionOutcomeEvents;   // drained by the pipe thread via get_mission_outcome_events

static std::mutex g_missionOutcomeClassifyMutex;
static std::unordered_set<void*> g_missionOutcomeFunctionPtrs;
static std::unordered_set<void*> g_nonMissionOutcomeFunctionPtrs;
static std::unordered_set<void*> g_loggedMissionOutcomeLikeFunctionPtrs;

static bool IsMissionOutcomeFunction(void* function, std::string& outMatchedName)
{
    {
        std::lock_guard<std::mutex> lock(g_missionOutcomeClassifyMutex);
        if (g_missionOutcomeFunctionPtrs.count(function))
        {
            TryGetObjectName(function, outMatchedName);  // cheap - just for the event payload
            return true;
        }
        if (g_nonMissionOutcomeFunctionPtrs.count(function))
            return false;
    }

    std::string name;
    bool resolved = TryGetObjectName(function, name);
    bool isExactMatch = resolved && (name == "MulticastMissionFinished" ||
                                      name == "OnShowMissionVictory" ||
                                      name == "MulticastGameOver");

    if (resolved && !isExactMatch)
    {
        std::string lower = ToLowerCopy(name);
        bool missionish = lower.find("mission") != std::string::npos &&
            (lower.find("finish") != std::string::npos || lower.find("complet") != std::string::npos ||
             lower.find("victory") != std::string::npos || lower.find("gameover") != std::string::npos);
        if (missionish)
        {
            std::lock_guard<std::mutex> lock(g_missionOutcomeClassifyMutex);
            if (!g_loggedMissionOutcomeLikeFunctionPtrs.count(function))
            {
                g_loggedMissionOutcomeLikeFunctionPtrs.insert(function);
                LogLine("Mission-outcome-like (but not one of the three exact names) function seen: " + name);
            }
        }
    }

    std::lock_guard<std::mutex> lock(g_missionOutcomeClassifyMutex);
    if (isExactMatch)
    {
        g_missionOutcomeFunctionPtrs.insert(function);
        LogLine("Classified exact mission-outcome trigger function pointer: " + name);
        outMatchedName = name;
    }
    else
    {
        g_nonMissionOutcomeFunctionPtrs.insert(function);
    }
    return isExactMatch;
}

static void CaptureMissionOutcomeEvent(void* self, const std::string& triggerName)
{
    std::lock_guard<std::mutex> lock(g_missionOutcomeEventsMutex);
    g_missionOutcomeEvents.push_back({ reinterpret_cast<uint64_t>(self), triggerName });
}

// hkProcessEvent itself is now a thin __try/__except wrapper (below) -
// all the actual classification/detection logic that used to live directly
// in hkProcessEvent was moved, unchanged, into this _Impl function. This is
// purely a crash-containment measure: MSVC's __try/__except can't wrap a
// scope that also does C++ object unwinding/destructors directly (same
// restriction noted elsewhere in this file, e.g. around TryProcessEventCall),
// so the real logic needed to move into its own function callable from
// inside a plain __try block, rather than annotating hkProcessEvent in place.
// blockedOut is an out-param since __except's filter can't see local
// variables declared inside the __try'd call in the caller's scope.
void hkProcessEvent_Impl(void* self, void* function, void* params, bool* blockedOut)
{
    // Services queued CALL/CALLDATA requests (see HandleCall/HandleCallData)
    // here instead of from a Present hook. Present hooking required creating
    // a second, throwaway D3D11 device via D3D11CreateDeviceAndSwapChain at
    // startup just to read Present's address off its vtable - concurrent
    // with the game's own real device/swapchain creation. That's the
    // strongest suspect for a crash seen consistently at game startup
    // ("during connection, on construction", 3 identical crash dumps, zero
    // dungeons_bridge frames on any of them - consistent with a GPU-driver-
    // level fault, not our own code). ProcessEvent is already confirmed
    // firing reliably and immediately once the game is running, whether or
    // not a real Present address was ever found, so it's a strictly safer
    // place to drain from - see SetupHookThread's own comment for why the
    // Present hook attempt itself was removed entirely, not just made
    // optional.
    DrainPendingCalls();
    DrainGenericWork();

    uint64_t callNum = g_processEventCallCount.fetch_add(1, std::memory_order_relaxed);
    if (callNum == 0)
        LogLine("hkProcessEvent: first call received - hook is definitely firing.");

    // Engine-readiness gate: every classification path below eventually
    // resolves an FName via AppendString, which walks internal engine
    // name-table/GObjects state - unsafe during early boot/menu windows
    // even though DrainPendingCalls/DrainGenericWork above (a deliberate,
    // user-triggered CALL/CALLDATA request) already ran regardless, since
    // those don't depend on this classification machinery at all.
    if (!IsEngineReadyForClassification())
    {
        *blockedOut = false;
        return;
    }

    bool blocked = false;

    // Blocking check: broad match (whole Interact family, not just
    // "OnInteracted") - the actual pickup effect can apply during the
    // EARLIER "OnInteract" call, so only blocking "OnInteracted" let it
    // through too late to matter. See IsInteractFamilyFunction's comment.
    //
    // EXCLUDING "Highlight" events specifically (OnHighlightBegin/End) -
    // IsInteractFamilyFunction's "Interact" substring match is on the
    // COMPONENT name prefix in the auto-generated delegate binding (e.g.
    // "BndEvt__InteractableComponent_..._OnHighlightBegin__DelegateSignature"
    // matches on "Interact**able**Component", not on the actual event),
    // so it nets highlight/hover callbacks that fire constantly just from
    // a player walking near or looking at a blocked-tier item - far more
    // often than real pickup attempts - and have nothing to do with
    // picking anything up. Skipping oProcessEvent for those means
    // silently dropping a call the engine's own highlight bookkeeping
    // (a paired begin/end ref-count or similar) likely expects to always
    // complete; doing that repeatedly over a real session is a plausible
    // way to progressively corrupt engine-internal state without an
    // immediate, deterministic crash.
    if (IsInteractFamilyFunction(function))
    {
        std::string funcName;
        bool isHighlightEvent = TryGetObjectName(function, funcName) &&
                                 funcName.find("Highlight") != std::string::npos;
        if (!isHighlightEvent)
        {
            std::string className;
            if (TryGetClassName(self, className))
            {
                int tier = ClassifyPickupTier(className);
                int unlocked = g_pickupUnlockTier.load(std::memory_order_relaxed);
                if (tier > 0 && tier > unlocked)
                {
                    blocked = true;
                    LogLine("BLOCKED pickup (tier " + std::to_string(tier) + " > unlocked " +
                             std::to_string(unlocked) + "): " + className);
                }
            }
        }
    }

    // Per-actor dedupe for Supply Station reporting - see the comment at the
    // call site below for why this exists even though supply uses the same
    // trigger filter as regular chests.
    static std::mutex g_reportedSupplyActorsMutex;
    static std::unordered_set<uint64_t> g_reportedSupplyActors;

    // Chest-open event reporting: both regular chests AND Supply Stations
    // use IsChestReportFunction - "OnInteract" present, "OnInteracted"
    // absent. OnInteract fires exactly once per interaction attempt;
    // OnInteracted fires once per spawned item, which would over-count if
    // used for reporting.
    //
    // g_reportedSupplyActors (dedup by actor address) is a defensive
    // safety net for Supply specifically - a Supply Station is destroyed
    // on open rather than flipping a bOpened-style flag the way
    // AChestActor gives regular chests, so there's no other state
    // available to double-check against if OnInteract were ever to fire
    // more than once for the same station. Regular chests don't need it.
    // Clicky/ClickyComponent-family bound events (confirmed via
    // dungeons_bridge_debug.log to be what Supply Station's interact
    // button routes through - see the log's "Classified new Interact-
    // family function" lines, which only ever show Clicky/ClickyComponent
    // as broad Interact-family, never as the narrow chest-reporting
    // match) apparently never produce a bare "OnInteract" ProcessEvent
    // call the way InteractableComp/ReplicatedInteractable do - only
    // "OnInteracted" ever fires for them. IsChestReportFunction's narrow
    // match can therefore never see them at all, meaning a Supply
    // Station's open was never reaching CaptureInteractEvent - not
    // misclassified, just structurally unreachable via that path. Falling
    // back to the broader Interact-family match for this, but ONLY when
    // the actor's own class name contains "supply" (never for arbitrary
    // Interact-family hits - that would badly over-report on doors, NPCs,
    // popups, etc., all of which are also Interact-family), and ONLY when
    // the narrow match didn't already claim it. The existing per-actor
    // dedup (originally added as a defensive safety net) is what makes
    // this safe to widen: OnInteracted can fire more than once per open,
    // but each actor address can only ever report once.
    bool isNarrowChestReport = IsChestReportFunction(function);
    bool isSupplyFallback = !isNarrowChestReport && IsInteractFamilyFunction(function);
    if (!blocked && (isNarrowChestReport || isSupplyFallback))
    {
        std::string className;
        if (TryGetClassName(self, className))
        {
            if (ToLowerCopy(className).find("supply") != std::string::npos)
            {
                uint64_t addr = reinterpret_cast<uint64_t>(self);
                bool alreadyReported;
                {
                    std::lock_guard<std::mutex> lock(g_reportedSupplyActorsMutex);
                    alreadyReported = !g_reportedSupplyActors.insert(addr).second;
                }
                if (!alreadyReported)
                    CaptureInteractEvent(addr, className);
            }
            else if (isNarrowChestReport)
            {
                CaptureInteractEvent(reinterpret_cast<uint64_t>(self), className);
            }
        }
    }

    if (IsDeathFunction(function))
        CaptureDeathEvent(self);

    if (IsSecretFoundFunction(function))
        CaptureSecretFoundEvent(self);

    // Currency widget cross-check (see the block above g_currencyPtr's
    // section for why this exists). Gated on the INSTANCE's class name
    // containing "counter" - the function name alone ("OnValueChanged")
    // is too generic to trust by itself game-wide.
    if (IsCurrencyValueChangedFunction(function) || IsCurrencyTypeChangedFunction(function))
    {
        std::string className;
        if (TryGetClassName(self, className) &&
            ToLowerCopy(className).find("counter") != std::string::npos)
        {
            uint64_t widgetAddr = reinterpret_cast<uint64_t>(self);
            if (IsCurrencyValueChangedFunction(function))
                CaptureCurrencyValueEvent(widgetAddr, params);
            else
                CaptureCurrencyTypeEvent(widgetAddr, params);
        }
    }

    {
        std::string matchedTriggerName;
        if (IsMissionOutcomeFunction(function, matchedTriggerName))
            CaptureMissionOutcomeEvent(self, matchedTriggerName);
    }

    if (!blocked)
        *blockedOut = false;
    else
        *blockedOut = true;
    // Deliberately does NOT call oProcessEvent itself - see hkProcessEvent
    // below, which calls it exactly once, unconditionally, OUTSIDE this
    // function's __try wrapper. Keeping the real engine call out of the
    // SEH-guarded region is intentional: if an exception is ever caught
    // below, we must be certain oProcessEvent hasn't already run (and so
    // is still safe/necessary to call) rather than risk calling the
    // original engine function twice for the same event.
}

// Theoretical/preventive hardening, added after a beta tester's crash dump
// showed the fault happening directly inside this DLL's own frames (not the
// game's) - most likely our classification code (TryGetClassName, the various
// IsXFunction matchers, resolve_fname-style GObjects/FName walks) touching an
// object that's still mid-construction, whose vtable/class pointer isn't
// valid yet. Not confirmed against a repro - we don't have the exact source
// that produced the crashing .dll, so this can't be verified against that
// specific build. What this DOES guarantee: an access violation raised
// anywhere inside classification/detection no longer takes the whole game
// down - it's caught, logged once, and oProcessEvent (the actual engine
// call the player's action depends on) still runs exactly once regardless,
// unmodified, exactly as if detection had been skipped entirely for that call.
static std::atomic<uint64_t> g_hkProcessEventExceptionCount{0};

// Pulled out of hkProcessEvent on purpose: it builds std::string temporaries
// (std::to_string, concatenation), and a function containing a __try/__except
// can't also contain any C++ object requiring destructor/unwind handling
// under /EHsc (MSVC C2712) - including temporaries created inside the
// __except block itself, not just named locals. Keeping hkProcessEvent's own
// body free of any such object is what lets it use __try at all.
void LogProcessEventException()
{
    uint64_t n = g_hkProcessEventExceptionCount.fetch_add(1, std::memory_order_relaxed);
    if (n < 20)  // cap - a fast, repeating crash-and-catch loop shouldn't spam the log file unbounded
        LogLine("hkProcessEvent: caught an exception in classification/detection code "
                 "(#" + std::to_string(n + 1) + ") - object was likely mid-construction. "
                 "Treating this call as not-blocked and calling the original function unmodified.");
}

void hkProcessEvent(void* self, void* function, void* params)
{
    bool blocked = false;
    __try
    {
        hkProcessEvent_Impl(self, function, params, &blocked);
    }
    __except (EXCEPTION_EXECUTE_HANDLER)
    {
        LogProcessEventException();
        blocked = false;  // classification never completed, so there's nothing
                           // to justify blocking this call - fail open, not closed.
    }
    // Called exactly once, always, regardless of whether classification
    // above succeeded or was caught - see the comment on hkProcessEvent_Impl
    // for why the real engine call had to move out here.
    if (!blocked)
    {
        oProcessEvent(self, function, params);
        return;
    }

    // Skipping the real call above leaves `params` untouched - for a
    // UFunction with a return value, that's whatever garbage the caller's
    // stack/buffer already had there, not the zero/false a "this call was
    // blocked" outcome should read as. If the calling Blueprint branches on
    // or dereferences that return value, it's reading garbage - this is
    // the exact same root cause already found and fixed in the newer
    // per-function ExecFunction-hook version of this project (see
    // ExecFunctionBlockCommon's g_execReturnSize there): a real UE4Minidump
    // crash traced back to a blocked native call whose Result slot was
    // never initialized. Same fix, applied here: zero the return-value
    // portion of `params` using UFunction::ParmsSize (+0x9E) and
    // UFunction::ReturnValueOffset (+0xA0) - standard UE4.22 layout,
    // confirmed via Dumper-7's Pad_9C[0x24] between FunctionFlags (0x98)
    // and ExecFunction (0xC0) lining up exactly with this field layout.
    __try
    {
        uint16_t parmsSize = *reinterpret_cast<uint16_t*>(reinterpret_cast<uint8_t*>(function) + 0x9E);
        uint16_t returnValueOffset = *reinterpret_cast<uint16_t*>(reinterpret_cast<uint8_t*>(function) + 0xA0);
        if (returnValueOffset != 0xFFFF && parmsSize > returnValueOffset)
        {
            uint16_t returnSize = parmsSize - returnValueOffset;
            memset(reinterpret_cast<uint8_t*>(params) + returnValueOffset, 0, returnSize);
        }
    }
    __except (EXCEPTION_EXECUTE_HANDLER)
    {
        // function/params pointers turned out not to be safely readable
        // here - nothing more we can do; the block itself still holds.
    }
}


// ---- Currency pointer capture, via the exact technique confirmed working
// in a real Cheat Engine table (Dungeons_Master_Table_v3_70.CT) ----
// The real Emeralds/Gold/Eyes of Ender getter is a tiny NATIVE (non-
// reflected) function: `mov eax,[rcx+8]; ret` - explaining why every
// GObjects/reflection-based technique tried before this failed to find
// it; it was never a UFUNCTION at all. The CT hooks this exact function
// and captures its "this" pointer (rcx) the first time anything calls
// it, into a symbol it calls p_currency. Confirmed offsets from that CT
// table cross-checked against real in-game HUD values (see
// dungeons_reader.py's CURRENCY_OFFSETS block for the full story):
//   Emeralds      = p_currency + 0x08
//   Eyes of Ender = p_currency + 0x14
//   Gold          = p_currency + 0x20  (still UNCONFIRMED - no nonzero
//                                        Gold reading tested against yet)
//
// We do the same via MinHook instead of a hand patch - safer, since
// MinHook handles instruction relocation properly. The AOB pattern
// (F8 8B 41 08 C3 CC) is scanned for in the main module; we hook at
// pattern+1 (the actual `mov eax,[rcx+8]; ret` body). Because x64's
// calling convention always passes the first pointer arg in RCX and
// returns int in EAX, a normal C function with this signature is ABI-
// compatible as a drop-in replacement - no hand-assembled bytes needed.

static void* g_currencyPtr = nullptr;

typedef int(*CurrencyGetterFn)(void* thisPtr);
static CurrencyGetterFn oCurrencyGetter = nullptr;

int hkCurrencyGetter(void* thisPtr)
{
    // Always track the LATEST thisPtr the game itself calls this getter
    // with - NOT just the first one ever seen. This getter is called
    // constantly by the game's own UI/logic, always with whatever the
    // CURRENT live currency object is. A "capture once, keep forever"
    // guard (the previous `if (!g_currencyPtr)` here) means that if the
    // underlying currency component is ever destroyed and recreated -
    // a hero swap, a save reload, the same class of zone-transition
    // churn already documented around apply_emerald_reward's own
    // staleness handling on the Python side - g_currencyPtr stays
    // permanently pinned to the OLD, now-stale/freed pointer, and every
    // later call (which DOES have the correct new pointer) gets
    // silently ignored. Confirmed happening live: a long-running
    // Dungeons.exe process (same PID across multiple client sessions)
    // ended up handing back a wildly garbage read (-1558079228) through
    // the stale pointer, and every subsequent write via that same
    // pointer "verified" successfully against ITSELF (read-back matched
    // what was just written) while never touching the real, live
    // currency object at all - so the in-game HUD never moved despite
    // every grant reporting success. Unconditionally re-assigning here
    // keeps g_currencyPtr self-healing: it converges back onto the real
    // live object within one native getter call after the game itself
    // next needs to display/use the currency (essentially immediately -
    // this getter is called far more often than dungeons_reader.py
    // polls), rather than requiring the whole DLL (and therefore the
    // whole game process) to restart to recover.
    g_currencyPtr = thisPtr;
    return oCurrencyGetter(thisPtr);
}

// Simple AOB scan across the main module's mapped image (reads size from
// its own PE header - no extra library dependency needed). Returns EVERY
// match, not just the first - see the currency hook install site below
// for why this matters: a hook built on FindPattern's old first-match-
// only behavior turned out to be silently hooking the wrong instance of
// a too-generic 6-byte pattern, and there was no way to tell without
// this.
// Isolated POD-only helper - no C++ objects with destructors in scope,
// same MSVC restriction as TryProcessEventCall above (C2712: __try can't
// coexist with a function that also has an object requiring unwinding -
// FindAllPatterns/FindPattern's own std::vector<uintptr_t>/local state
// triggered this the first time these two were written directly with
// __try inline). Pure pointer/size arguments only, so nothing here ever
// needs unwinding - safe to __try around.
static bool TryMatchPatternAt(const uint8_t* data, size_t offset, const uint8_t* pattern, size_t patternLen)
{
    __try
    {
        for (size_t j = 0; j < patternLen; ++j)
        {
            if (data[offset + j] != pattern[j])
                return false;
        }
        return true;
    }
    __except (EXCEPTION_EXECUTE_HANDLER)
    {
        return false; // unmapped/guard page mid-scan - treat as no match
    }
}

static std::vector<uintptr_t> FindAllPatterns(const uint8_t* pattern, size_t patternLen, size_t maxMatches = 64)
{
    std::vector<uintptr_t> matches;
    uintptr_t base = GetImageBase();
    auto dosHeader = reinterpret_cast<PIMAGE_DOS_HEADER>(base);
    if (dosHeader->e_magic != IMAGE_DOS_SIGNATURE)
        return matches;

    auto ntHeaders = reinterpret_cast<PIMAGE_NT_HEADERS>(base + dosHeader->e_lfanew);
    if (ntHeaders->Signature != IMAGE_NT_SIGNATURE)
        return matches;

    size_t imageSize = ntHeaders->OptionalHeader.SizeOfImage;
    const uint8_t* data = reinterpret_cast<const uint8_t*>(base);

    for (size_t i = 0; i + patternLen <= imageSize && matches.size() < maxMatches; ++i)
    {
        if (TryMatchPatternAt(data, i, pattern, patternLen))
            matches.push_back(base + i);
    }
    return matches;
}

// Simple AOB scan across the main module's mapped image (reads size from
// its own PE header - no extra library dependency needed).
static uintptr_t FindPattern(const uint8_t* pattern, size_t patternLen)
{
    uintptr_t base = GetImageBase();
    auto dosHeader = reinterpret_cast<PIMAGE_DOS_HEADER>(base);
    if (dosHeader->e_magic != IMAGE_DOS_SIGNATURE)
        return 0;

    auto ntHeaders = reinterpret_cast<PIMAGE_NT_HEADERS>(base + dosHeader->e_lfanew);
    if (ntHeaders->Signature != IMAGE_NT_SIGNATURE)
        return 0;

    size_t imageSize = ntHeaders->OptionalHeader.SizeOfImage;
    const uint8_t* data = reinterpret_cast<const uint8_t*>(base);

    for (size_t i = 0; i + patternLen <= imageSize; ++i)
    {
        if (TryMatchPatternAt(data, i, pattern, patternLen))
            return base + i;
    }
    return 0;
}


std::string HandleRequest(const std::string& request)
{
    if (request == "get_currency_ptr")
    {
        std::ostringstream out;
        out << "PTR:" << std::hex << reinterpret_cast<uintptr_t>(g_currencyPtr);
        return out.str();
    }

    if (request == "get_currency_value_events")
    {
        std::vector<CurrencyValueEvent> drained;
        {
            std::lock_guard<std::mutex> lock(g_currencyValueEventsMutex);
            std::swap(drained, g_currencyValueEvents);
        }
        std::ostringstream out;
        out << "EVENTS:" << std::dec << drained.size();
        for (const auto& e : drained)
        {
            out << "|" << std::hex << e.widgetAddr << std::dec
                << "," << e.newValue << "," << e.previousValue;
        }
        return out.str();
    }

    if (request == "get_currency_type_events")
    {
        std::vector<CurrencyTypeEvent> drained;
        {
            std::lock_guard<std::mutex> lock(g_currencyTypeEventsMutex);
            std::swap(drained, g_currencyTypeEvents);
        }
        std::ostringstream out;
        out << "EVENTS:" << std::dec << drained.size();
        for (const auto& e : drained)
        {
            out << "|" << std::hex << e.widgetAddr << std::dec
                << "," << e.serializedIdIndex;
        }
        return out.str();
    }

    if (request == "get_chest_events")
    {
        std::vector<InteractEvent> drained;
        {
            std::lock_guard<std::mutex> lock(g_interactEventsMutex);
            std::swap(drained, g_interactEvents);
        }
        std::ostringstream out;
        out << "EVENTS:" << std::dec << drained.size();
        for (const auto& e : drained)
        {
            // className can't contain '|' or ',' (UE identifiers are
            // alphanumeric/underscore only), so simple delimiting is safe.
            out << "|" << std::hex << e.actorAddr << std::dec << "," << e.className
                << "," << std::hex << e.worldPtr << std::dec;
        }
        return out.str();
    }

    if (request == "get_death_events")
    {
        std::vector<CharacterDeathEvent> drained;
        {
            std::lock_guard<std::mutex> lock(g_deathEventsMutex);
            std::swap(drained, g_deathEvents);
        }
        std::ostringstream out;
        out << "EVENTS:" << std::dec << drained.size();
        for (const auto& e : drained)
        {
            out << "|" << std::hex << e.actorAddr << std::dec;
        }
        return out.str();
    }

    if (request == "get_secret_events")
    {
        std::vector<SecretFoundEvent> drained;
        {
            std::lock_guard<std::mutex> lock(g_secretEventsMutex);
            std::swap(drained, g_secretEvents);
        }
        std::ostringstream out;
        out << "EVENTS:" << std::dec << drained.size();
        for (const auto& e : drained)
        {
            out << "|" << std::hex << e.actorAddr << std::dec << "," << e.className;
        }
        return out.str();
    }

    if (request == "get_mission_outcome_events")
    {
        std::vector<MissionOutcomeEvent> drained;
        {
            std::lock_guard<std::mutex> lock(g_missionOutcomeEventsMutex);
            std::swap(drained, g_missionOutcomeEvents);
        }
        std::ostringstream out;
        out << "EVENTS:" << std::dec << drained.size();
        for (const auto& e : drained)
        {
            out << "|" << std::hex << e.actorAddr << std::dec << "," << e.triggerName;
        }
        return out.str();
    }

    if (request.rfind("set_pickup_tier ", 0) == 0)
    {
        std::string body = request.substr(std::string("set_pickup_tier ").size());
        try
        {
            int tier = std::stoi(body);
            g_pickupUnlockTier.store(tier, std::memory_order_relaxed);
            LogLine("set_pickup_tier: now at tier " + std::to_string(tier));
            return "OK";
        }
        catch (...)
        {
            return "ERROR: invalid tier value";
        }
    }

    if (request == "get_pickup_tier")
    {
        std::ostringstream out;
        out << "TIER:" << g_pickupUnlockTier.load(std::memory_order_relaxed);
        return out.str();
    }

    if (request.rfind("CALL ", 0) == 0)
        return HandleCall(request.substr(5));

    if (request.rfind("CALLDATA ", 0) == 0)
        return HandleCallData(request.substr(9));

    // Cheap loading-screen/churn detector: just the object count, no full
    // scan. Python polls this a couple times a second and treats a big
    // swing in a short window as "something is loading right now" (a zone
    // transition tears down and recreates a large chunk of the object
    // graph in one burst - see this project's crash-investigation notes,
    // several confirmed and suspected crashes trace back to scanning/
    // resolving names during exactly this window) - gates risky scans/
    // name-resolution calls on the Python side without needing to know
    // the specific loading-screen widget class for this build/DLC.
    if (request == "gobjects_count")
    {
        TUObjectArray* gObjects = GetGObjects();
        if (!gObjects)
            return "ERROR:could not resolve GObjects";
        int32_t count = 0;
        if (!TryGetGObjectsCount(gObjects, count))
            return "ERROR:GObjects count read faulted";
        return "COUNT:" + std::to_string(count);
    }

    const std::string resolvePrefix = "resolve_name:";
    if (request.rfind(resolvePrefix, 0) == 0)
        return HandleResolveName(request.substr(resolvePrefix.size()));

    const std::string findByNamePrefix = "find_by_name:";
    if (request.rfind(findByNamePrefix, 0) == 0)
        return HandleFindByName(request.substr(findByNamePrefix.size()));

    const std::string findByClassPrefix = "find_by_class:";
    if (request.rfind(findByClassPrefix, 0) == 0)
        return HandleFindByClass(request.substr(findByClassPrefix.size()));

    const std::string findOuterPrefix = "find_outer:";
    if (request.rfind(findOuterPrefix, 0) == 0)
    {
        std::string hexAddr = request.substr(findOuterPrefix.size());
        uintptr_t target = 0;
        try
        {
            target = static_cast<uintptr_t>(std::stoull(hexAddr, nullptr, 16));
        }
        catch (...)
        {
            return "ERROR:could not parse address";
        }
        return FindObjectsWithOuter(target);
    }

    return "DLL received: " + request;
}

void PipeServerThread()
{
    while (true)
    {
        HANDLE pipe = CreateNamedPipeW(
            GetPipeName(),
            PIPE_ACCESS_DUPLEX,
            PIPE_TYPE_MESSAGE | PIPE_READMODE_MESSAGE | PIPE_WAIT,
            1,
            16384,
            16384,
            0,
            nullptr
        );

        if (pipe == INVALID_HANDLE_VALUE)
        {
            Sleep(1000);
            continue;
        }

        BOOL connected = ConnectNamedPipe(pipe, nullptr) ? TRUE : (GetLastError() == ERROR_PIPE_CONNECTED);

        if (connected)
        {
            char buffer[16384];
            DWORD bytesRead = 0;

            while (ReadFile(pipe, buffer, sizeof(buffer) - 1, &bytesRead, nullptr) && bytesRead > 0)
            {
                buffer[bytesRead] = '\0';
                std::string request(buffer);

                std::string response = HandleRequest(request);

                DWORD bytesWritten = 0;
                WriteFile(pipe, response.c_str(), (DWORD)response.size(), &bytesWritten, nullptr);
            }
        }

        DisconnectNamedPipe(pipe);
        CloseHandle(pipe);
    }
}

// (Present hook removed entirely - see the comment above SetupHookThread.)

// ---- Present hook: REMOVED ----
// This used to create a throwaway D3D11 device+swapchain via
// D3D11CreateDeviceAndSwapChain purely to read Present's address off its
// vtable, concurrently with the game's own real device/swapchain creation
// at startup (a Sleep(3000) in SetupHookThread tried to reduce the overlap,
// but couldn't guarantee it never happens). This is the strongest suspect
// for a crash a beta tester hit consistently at game startup ("during
// connection, on construction") - 3 crash dumps with byte-identical
// offsets, all purely inside Dungeons-Win64-Shipping/driver code with zero
// dungeons_bridge frames, and the tester confirmed it never happens with
// the mod NOT injected. A second D3D11 device fighting the game's own for
// the same GPU/driver resources during its init window is exactly the kind
// of thing that can fault at the driver level with no attributable stack.
//
// The only thing Present was actually used for was draining g_pendingCalls
// (the CALL/CALLDATA queue) once per frame - see DrainPendingCalls' comment,
// now called from hkProcessEvent_Impl instead, which needs no throwaway
// device and was already confirmed firing reliably (including in sessions
// where GetPresentAddress used to fail anyway, e.g. "Present address not
// found" in this tester's own log - Present was never reliably available
// to begin with, on top of being a suspected crash cause).

// Guards against SetupHookThread ever running its hook-installation logic
// more than once per process lifetime. Root-caused from a real crash dump:
// the debug log showed 2 fully-successful SetupHookThread sessions in a row
// with the IDENTICAL ProcessEvent target address (same live process, not a
// real relaunch - see is_dll_loaded's own false-negative comment on the
// Python side, which reduces but doesn't guarantee this never happens), then
// a 3rd attempt that crashed inside MinHook's own trampoline buffer
// allocator (VirtualAlloc/VirtualQuery, resolved from the crash dump's
// import thunks). MinHook's global hook table isn't designed to have
// MH_CreateHook called again for a target it's already hooked without an
// MH_RemoveHook/MH_Uninitialize in between - this makes that a no-op instead
// of undefined behavior, independent of whether the Python-side retry above
// ever eliminates the false-negative that triggers a redundant injection.
static std::atomic<bool> g_hooksAlreadySetUp{false};

void SetupHookThread()
{
    if (g_hooksAlreadySetUp.exchange(true))
    {
        LogLine("=== SetupHookThread called again in an already-hooked process - skipping "
                 "(MinHook's hook table isn't safe to re-initialize without an uninstall first). ===");
        return;
    }

    LogLine("=== SetupHookThread starting (new session) ===");
    ReadGameStoreConfig();  // must run before ANY Offsets::Active.* usage below
    // Small delay so classification/hooking doesn't start before the game's
    // own early init has had a chance to settle.
    Sleep(8000);  // widened from 3000 - see LogLine's PID+timestamp comment:
    // this crash (SecondsSinceStart=0, specifically when the client is
    // already attached before the game launches) persisted even with
    // wait_for_process_ready() gating injection on user32.dll being
    // loaded, so the original 3s guess wasn't the whole story. Not a
    // confirmed fix, just a wider safety margin while PID+timestamped
    // logs (new) make the next crash dump actually correlatable.

    MH_STATUS initStatus = MH_Initialize();
    LogLine("MH_Initialize status: " + std::to_string(static_cast<int>(initStatus)));
    if (initStatus != MH_OK)
        return;

    // Currency hook REMOVED: the pattern-scanned "generic getter" this
    // used to install on was real (a genuine function head), but NOT
    // actually UWalletComponent's currency getter - it was some other,
    // extremely hot per-frame native getter that happens to compile to
    // the exact same trivial `mov eax,[rcx+8]; ret` shape. Hooking it
    // was stable at install time but crashed the game once that
    // unrelated hot path actually ran. Not needed anyway: currency is
    // already read via UWalletComponent::Balance() through ProcessEvent
    // (the CALL/CALLDATA path below), which doesn't need this hook at
    // all.

    // ProcessEvent hook for chest-open detection. Same RVA GetProcessEventFn()
    // already uses for the CALL/CALLDATA path - after this hook is installed,
    // that path naturally starts going through hkProcessEvent too (which
    // just forwards to oProcessEvent when it's not an OnOpenLootChest call),
    // so nothing about the existing CALL functionality changes.
    uintptr_t peAddr = GetImageBase() + Offsets::Active.ProcessEvent;
    LogLine("ProcessEvent target address: 0x" + [&]{ std::ostringstream o; o << std::hex << peAddr; return o.str(); }());
    MH_STATUS peStatus = MH_CreateHook(reinterpret_cast<void*>(peAddr),
                  &hkProcessEvent, reinterpret_cast<void**>(&oProcessEvent));
    LogLine("ProcessEvent hook MH_CreateHook status: " + std::to_string(static_cast<int>(peStatus)));

    MH_STATUS enableStatus = MH_EnableHook(MH_ALL_HOOKS);
    LogLine("MH_EnableHook(MH_ALL_HOOKS) status: " + std::to_string(static_cast<int>(enableStatus)));
}

BOOL APIENTRY DllMain(HMODULE hModule, DWORD reason, LPVOID)
{
    if (reason == DLL_PROCESS_ATTACH)
    {
        g_ownModule = hModule;
        DisableThreadLibraryCalls(hModule);
        std::thread(PipeServerThread).detach();
        std::thread(SetupHookThread).detach();
    }
    return TRUE;
}
