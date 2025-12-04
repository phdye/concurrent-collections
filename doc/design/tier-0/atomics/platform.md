# atomics — Platform Specifics

## Overview

Atomic operations require platform-specific implementations due to compiler and instruction set differences.

## Platform Matrix

| Platform | Implementation | 128-bit CAS | Status |
|----------|----------------|-------------|--------|
| GCC/Clang x86-64 | C11 atomics | CMPXCHG16B | ⬜ |
| GCC/Clang ARM64 | C11 atomics | LDXP/STXP or CASP | ⬜ |
| MSVC x86-64 | Interlocked intrinsics | _InterlockedCompareExchange128 | ⬜ |
| MSVC ARM64 | Interlocked intrinsics | Not available | ⬜ |

## x86-64 Specifics

**128-bit CAS:**
```c
#ifdef __GNUC__
static inline bool cas128(__int128 *ptr, __int128 *expected, __int128 desired) {
    return __sync_bool_compare_and_swap(ptr, *expected, desired);
}
#elif defined(_MSC_VER)
static inline bool cas128(__int128 *ptr, __int128 *expected, __int128 desired) {
    return _InterlockedCompareExchange128(
        (volatile LONG64*)ptr,
        (LONG64)(desired >> 64),
        (LONG64)desired,
        (LONG64*)expected
    );
}
#endif
```

## ARM64 Specifics

**LSE Atomics (when available):**
- Use LDADD, STADD, CAS instructions
- Detected via arch_detect module

**LL/SC Fallback:**
- LDXR/STXR pairs
- Used when LSE not available

## MSVC Intrinsics Mapping

| C11 Atomic | MSVC Intrinsic |
|------------|----------------|
| `atomic_load` | Direct read (volatile) |
| `atomic_store` | Direct write (volatile) + barrier |
| `atomic_exchange` | `InterlockedExchangePointer` |
| `atomic_compare_exchange` | `InterlockedCompareExchangePointer` |
| `atomic_fetch_add` | `InterlockedAdd64` |
| `atomic_thread_fence` | `MemoryBarrier()` |

## Build Configuration

```cmake
if(MSVC)
    # MSVC doesn't support C11 atomics
    target_compile_definitions(atomics PRIVATE CC_USE_MSVC_INTRINSICS)
endif()

# Enable 128-bit CAS on x86-64
if(CMAKE_SYSTEM_PROCESSOR MATCHES "x86_64|AMD64")
    if(NOT MSVC)
        target_compile_options(atomics PRIVATE -mcx16)
    endif()
endif()
```

## Known Issues

| Platform | Issue | Workaround |
|----------|-------|------------|
| MSVC ARM64 | No 128-bit atomic | Use lock-based fallback |
| Old GCC | `__int128` alignment issues | Use aligned wrapper struct |
