# [Module Name] — Platform Specifics

## Overview

[Why this module has platform-specific implementations]

## Platform Matrix

| Platform | Implementation | Status |
|----------|----------------|--------|
| Linux x86-64 | [Approach] | ⬜ |
| Linux ARM64 | [Approach] | ⬜ |
| macOS x86-64 | [Approach] | ⬜ |
| macOS ARM64 | [Approach] | ⬜ |
| Windows x86-64 | [Approach] | ⬜ |
| Portable fallback | [Approach] | ⬜ |

Legend: ⬜ Not implemented, 🔶 Partial, ✅ Complete

## Platform Detection

### Compile-Time Detection

```c
#if defined(__x86_64__) || defined(_M_X64)
    // x86-64 specific
#elif defined(__aarch64__) || defined(_M_ARM64)
    // ARM64 specific
#else
    // Portable fallback
#endif
```

### Runtime Detection

[CPUID, feature flags, etc.]

```c
// Example runtime detection
bool has_feature_x(void) {
    // Detection logic
}
```

## Platform-Specific Implementations

### x86-64

[Implementation details]

**Features used:**
- [Feature 1]: [Purpose]
- [Feature 2]: [Purpose]

**Intrinsics:**
```c
// Key intrinsics used
```

### ARM64

[Implementation details]

**Features used:**
- [Feature 1]: [Purpose]
- [Feature 2]: [Purpose]

**Intrinsics:**
```c
// Key intrinsics used
```

### Windows-Specific

[Any Windows-specific considerations]

### Portable Fallback

[C11 standard implementation]

## Abstraction Layer

[How platform differences are hidden]

```c
// Abstraction header
#ifdef PLATFORM_X86_64
    #define do_thing() do_thing_x86()
#else
    #define do_thing() do_thing_portable()
#endif
```

## Build Configuration

[CMake/Meson/setup.py configuration]

```cmake
# Example CMake
if(CMAKE_SYSTEM_PROCESSOR MATCHES "x86_64")
    target_sources(module PRIVATE x86_impl.c)
endif()
```

## Testing Requirements

| Platform | Required Tests | CI Runner |
|----------|---------------|-----------|
| [Platform] | [Tests] | [Runner type] |

## Known Issues

| Platform | Issue | Workaround | Status |
|----------|-------|------------|--------|
| [Platform] | [Problem] | [Solution] | [Open/Fixed] |
