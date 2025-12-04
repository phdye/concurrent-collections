# arch_detect — Design

## Overview

The `arch_detect` module provides compile-time and runtime detection of CPU architecture and feature flags. This enables the library to select optimal code paths (e.g., LCRQ on x86-64 with CMPXCHG16B) while maintaining portability.

## Dependencies

| Dependency | Purpose |
|------------|---------|
| C compiler | Predefined macros for architecture |
| CPUID (x86) | Runtime feature detection |
| System registers (ARM) | Runtime feature detection |

## Architecture

### Compile-Time Detection

Use preprocessor macros to identify base architecture:

```c
typedef enum {
    ARCH_X86_64,
    ARCH_ARM64,
    ARCH_RISCV64,
    ARCH_UNKNOWN
} cc_arch_t;

#if defined(__x86_64__) || defined(_M_X64)
    #define CC_ARCH CC_ARCH_X86_64
#elif defined(__aarch64__) || defined(_M_ARM64)
    #define CC_ARCH CC_ARCH_ARM64
#elif defined(__riscv) && __riscv_xlen == 64
    #define CC_ARCH CC_ARCH_RISCV64
#else
    #define CC_ARCH CC_ARCH_UNKNOWN
#endif
```

### Runtime Feature Detection

```c
typedef struct {
    bool cmpxchg16b;    // x86-64: double-width CAS
    bool lse;           // ARM64: Large System Extensions
    bool lse2;          // ARM64: LSE2 (atomic 128-bit load/store)
    uint32_t cache_line_size;
} cc_cpu_features_t;

// Populated at module init
extern cc_cpu_features_t cc_cpu_features;
```

### Data Structures

```c
// Feature flags structure
typedef struct {
    // x86-64 features
    bool cmpxchg16b;      // CMPXCHG16B instruction
    bool avx;             // AVX support
    bool avx2;            // AVX2 support
    
    // ARM64 features
    bool lse;             // Atomics extension (LDADD, etc.)
    bool lse2;            // Atomic 128-bit load/store
    
    // Cache info
    uint32_t l1_cache_line_size;
    uint32_t l2_cache_line_size;
} cc_cpu_features_t;
```

### Algorithms

| Detection | Method | Platform |
|-----------|--------|----------|
| x86-64 CMPXCHG16B | CPUID leaf 1, ECX bit 13 | x86-64 |
| ARM64 LSE | Read ID_AA64ISAR0_EL1 or `/proc/cpuinfo` | ARM64 |
| Cache line size | CPUID or sysconf | All |

### Concurrency Model

This module is **initialization-time only**. Feature detection runs once at module load and populates read-only globals. No thread safety concerns after initialization.

## API Surface

### Public Functions

```c
// Get detected architecture
cc_arch_t cc_get_arch(void);

// Get architecture name as string
const char* cc_get_arch_name(void);

// Get feature flags (read-only pointer)
const cc_cpu_features_t* cc_get_cpu_features(void);

// Check specific features
bool cc_has_cmpxchg16b(void);  // x86-64
bool cc_has_lse(void);          // ARM64

// Get cache line size (for padding)
uint32_t cc_get_cache_line_size(void);

// Module initialization (called once)
void cc_arch_detect_init(void);
```

### Python Bindings

```python
from concurrent_collections import config

config.detected_arch           # 'x86_64', 'aarch64', 'riscv64', 'unknown'
config.detected_features       # {'cmpxchg16b': True, 'lse': False, ...}
config.cache_line_size         # 64 or 128
```

## Design Decisions

| Decision | Choice | Rationale | Alternatives Considered |
|----------|--------|-----------|------------------------|
| Detection timing | Module init | One-time cost, no runtime overhead | On-demand (adds latency to first use) |
| Feature storage | Global struct | Simple, cache-friendly | Thread-local (unnecessary) |
| x86 detection | CPUID | Standard, reliable | `/proc/cpuinfo` parsing (Linux only) |
| ARM detection | ID registers or `/proc` | Kernel provides access | Inline probe (risky) |
| Unknown arch handling | Provide conservative defaults | Graceful degradation | Fail fast (too restrictive) |

## Integration Points

- **config**: Exposes features via Python API
- **atomics**: Uses features to select CAS implementations
- **lcrq**: Checks `cmpxchg16b` before enabling LCRQ path
- **smr_***: May use cache line size for padding

## Open Questions

1. **Virtualization detection**: Should we detect if running in a VM where features might be unavailable or behave differently?
2. **NUMA detection**: Should cache topology / NUMA node info be included?
