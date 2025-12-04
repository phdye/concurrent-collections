# arch_detect — Platform Specifics

## Overview

Architecture detection inherently requires platform-specific code. Each platform has different mechanisms for querying CPU features.

## Platform Matrix

| Platform | Detection Method | Status |
|----------|------------------|--------|
| Linux x86-64 | CPUID instruction | ⬜ |
| Linux ARM64 | `/proc/cpuinfo` or `getauxval(AT_HWCAP)` | ⬜ |
| macOS x86-64 | CPUID instruction | ⬜ |
| macOS ARM64 | `sysctlbyname()` | ⬜ |
| Windows x86-64 | `__cpuid` intrinsic | ⬜ |
| Windows ARM64 | `IsProcessorFeaturePresent()` | ⬜ |
| Portable fallback | Compile-time only, no runtime features | ⬜ |

## Platform-Specific Implementations

### x86-64 (All OS)

**CPUID Instruction:**

```c
#if defined(__x86_64__) || defined(_M_X64)

#ifdef _MSC_VER
#include <intrin.h>
#define cpuid(info, leaf) __cpuid(info, leaf)
#else
#include <cpuid.h>
#define cpuid(info, leaf) __cpuid(leaf, info[0], info[1], info[2], info[3])
#endif

static bool detect_cmpxchg16b(void) {
    int info[4];
    cpuid(info, 1);
    return (info[2] & (1 << 13)) != 0;  // ECX bit 13
}

#endif
```

**Cache Line Detection:**

```c
static uint32_t detect_cache_line_size_x86(void) {
    int info[4];
    cpuid(info, 0x80000006);  // Extended L2 cache info
    return info[2] & 0xFF;     // ECX[7:0] = line size
}
```

### ARM64 Linux

**Using getauxval (preferred):**

```c
#if defined(__linux__) && defined(__aarch64__)
#include <sys/auxv.h>
#include <asm/hwcap.h>

static bool detect_lse(void) {
    unsigned long hwcap = getauxval(AT_HWCAP);
    return (hwcap & HWCAP_ATOMICS) != 0;
}
#endif
```

**Fallback via /proc/cpuinfo:**

```c
static bool detect_lse_from_proc(void) {
    FILE *f = fopen("/proc/cpuinfo", "r");
    if (!f) return false;
    
    char line[256];
    while (fgets(line, sizeof(line), f)) {
        if (strstr(line, "Features") && strstr(line, "atomics")) {
            fclose(f);
            return true;
        }
    }
    fclose(f);
    return false;
}
```

### macOS ARM64

**Using sysctl:**

```c
#if defined(__APPLE__) && defined(__aarch64__)
#include <sys/sysctl.h>

static bool detect_lse_macos(void) {
    // Apple Silicon always has LSE
    // Verify via sysctl if needed
    int64_t value = 0;
    size_t size = sizeof(value);
    if (sysctlbyname("hw.optional.arm.FEAT_LSE", &value, &size, NULL, 0) == 0) {
        return value != 0;
    }
    return true;  // Assume true for Apple Silicon
}

static uint32_t detect_cache_line_size_macos(void) {
    int64_t value = 0;
    size_t size = sizeof(value);
    if (sysctlbyname("hw.cachelinesize", &value, &size, NULL, 0) == 0) {
        return (uint32_t)value;
    }
    return 128;  // Apple Silicon default
}
#endif
```

### Windows ARM64

```c
#if defined(_WIN32) && defined(_M_ARM64)
#include <windows.h>

static bool detect_lse_windows(void) {
    return IsProcessorFeaturePresent(PF_ARM_V81_ATOMIC_INSTRUCTIONS_AVAILABLE);
}
#endif
```

## Abstraction Layer

```c
// arch_detect.h - Unified interface

// Compile-time architecture
#if defined(__x86_64__) || defined(_M_X64)
    #define CC_ARCH_X86_64 1
#elif defined(__aarch64__) || defined(_M_ARM64)
    #define CC_ARCH_ARM64 1
#else
    #define CC_ARCH_UNKNOWN 1
#endif

// Runtime feature detection - implementation varies by platform
void cc_arch_detect_init(void);

// Unified query interface
bool cc_has_cmpxchg16b(void);  // Always false on non-x86
bool cc_has_lse(void);          // Always false on non-ARM
uint32_t cc_get_cache_line_size(void);
```

## Build Configuration

```cmake
# CMakeLists.txt
if(CMAKE_SYSTEM_PROCESSOR MATCHES "x86_64|AMD64")
    target_compile_definitions(arch_detect PRIVATE CC_TARGET_X86_64)
elseif(CMAKE_SYSTEM_PROCESSOR MATCHES "aarch64|ARM64")
    target_compile_definitions(arch_detect PRIVATE CC_TARGET_ARM64)
endif()

if(APPLE)
    target_compile_definitions(arch_detect PRIVATE CC_TARGET_MACOS)
elseif(WIN32)
    target_compile_definitions(arch_detect PRIVATE CC_TARGET_WINDOWS)
else()
    target_compile_definitions(arch_detect PRIVATE CC_TARGET_LINUX)
endif()
```

## Testing Requirements

| Platform | Required Tests | CI Runner |
|----------|---------------|-----------|
| Linux x86-64 | CPUID detection | ubuntu-latest |
| Linux ARM64 | getauxval/proc detection | ubuntu-24.04-arm |
| macOS x86-64 | CPUID detection | macos-13 |
| macOS ARM64 | sysctl detection | macos-14 |
| Windows x86-64 | __cpuid intrinsic | windows-latest |

## Known Issues

| Platform | Issue | Workaround | Status |
|----------|-------|------------|--------|
| Linux containers | `/proc/cpuinfo` may reflect host | Use `getauxval` preferentially | Addressed |
| Old macOS | `sysctlbyname` may not have ARM keys | Check for key existence | Addressed |
| Hyper-V ARM64 | Feature detection may differ from host | Conservative defaults | Documented |
