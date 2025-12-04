# arch_detect — Specification

## Overview

This module detects CPU architecture and features at initialization time, providing read-only access to the results for the lifetime of the process.

## Invariants

1. **Immutability after init**: Once `cc_arch_detect_init()` completes, all feature flags and architecture values are immutable.

2. **Consistency**: The detected architecture matches the actual CPU executing the code.

3. **Conservative defaults**: Unknown architectures or undetectable features default to the most portable (least capable) option.

## Preconditions

- Module must be initialized via `cc_arch_detect_init()` before any queries
- On ARM64 Linux, `/proc/cpuinfo` must be readable (fallback used if not)

## Contracts by Operation

### cc_arch_detect_init

**Signature:**
```c
void cc_arch_detect_init(void);
```

**Description:** Initialize architecture detection. Must be called once before any other functions. Safe to call multiple times (no-op after first).

**Preconditions:**
- None (can be called at any point during process startup)

**Postconditions:**
- `cc_cpu_features` global is populated
- All feature query functions return valid results
- Thread-safe to call query functions from any thread

**Errors:**
- None (cannot fail; uses conservative defaults on detection failure)

**Complexity:** O(1)

**Thread Safety:** Safe to call from multiple threads (internally synchronized or idempotent)

---

### cc_get_arch

**Signature:**
```c
cc_arch_t cc_get_arch(void);
```

**Description:** Returns the detected CPU architecture enum.

**Preconditions:**
- `cc_arch_detect_init()` has been called

**Postconditions:**
- Returns one of: `ARCH_X86_64`, `ARCH_ARM64`, `ARCH_RISCV64`, `ARCH_UNKNOWN`

**Errors:**
- None

**Complexity:** O(1)

**Thread Safety:** Safe (reads immutable data)

---

### cc_get_arch_name

**Signature:**
```c
const char* cc_get_arch_name(void);
```

**Description:** Returns human-readable architecture name.

**Preconditions:**
- `cc_arch_detect_init()` has been called

**Postconditions:**
- Returns static string: "x86_64", "aarch64", "riscv64", or "unknown"
- Pointer valid for lifetime of process

**Errors:**
- None

**Complexity:** O(1)

**Thread Safety:** Safe (returns pointer to static data)

---

### cc_get_cpu_features

**Signature:**
```c
const cc_cpu_features_t* cc_get_cpu_features(void);
```

**Description:** Returns pointer to feature flags structure.

**Preconditions:**
- `cc_arch_detect_init()` has been called

**Postconditions:**
- Returns non-NULL pointer to immutable structure
- Pointer valid for lifetime of process

**Errors:**
- None

**Complexity:** O(1)

**Thread Safety:** Safe (returns pointer to immutable data)

---

### cc_has_cmpxchg16b

**Signature:**
```c
bool cc_has_cmpxchg16b(void);
```

**Description:** Check if CPU supports 128-bit compare-and-swap (x86-64 only).

**Preconditions:**
- `cc_arch_detect_init()` has been called

**Postconditions:**
- Returns `true` if CMPXCHG16B instruction is available
- Returns `false` on non-x86-64 or if feature not detected

**Errors:**
- None

**Complexity:** O(1)

**Thread Safety:** Safe

---

### cc_has_lse

**Signature:**
```c
bool cc_has_lse(void);
```

**Description:** Check if CPU supports ARM Large System Extensions.

**Preconditions:**
- `cc_arch_detect_init()` has been called

**Postconditions:**
- Returns `true` if LSE atomics (LDADD, STADD, etc.) are available
- Returns `false` on non-ARM64 or if feature not detected

**Errors:**
- None

**Complexity:** O(1)

**Thread Safety:** Safe

---

### cc_get_cache_line_size

**Signature:**
```c
uint32_t cc_get_cache_line_size(void);
```

**Description:** Returns L1 data cache line size in bytes.

**Preconditions:**
- `cc_arch_detect_init()` has been called

**Postconditions:**
- Returns detected cache line size (typically 64 or 128)
- Returns 64 if detection fails (safe default)

**Errors:**
- None

**Complexity:** O(1)

**Thread Safety:** Safe

## Error Handling

| Error Condition | Detection | Response |
|-----------------|-----------|----------|
| CPUID not available | Try/catch or feature check | Use conservative defaults |
| `/proc/cpuinfo` unreadable | File open fails | Use conservative defaults |
| Unknown CPU vendor | CPUID vendor check | Use conservative defaults |
| Running in VM without feature | Feature test fails | Report feature as unavailable |

## Thread Safety

| Guarantee | Scope | Notes |
|-----------|-------|-------|
| Initialization safety | `cc_arch_detect_init` | Idempotent, internally synchronized |
| Read-only access | All query functions | No synchronization needed |
| No mutation | Post-init | All data immutable after init |

## Memory Model

No memory ordering concerns. All data is written once during initialization and read-only thereafter. Standard sequencing from module initialization to use ensures visibility.

## Performance Bounds

| Operation | Time | Notes |
|-----------|------|-------|
| `cc_arch_detect_init` | O(1), ~microseconds | CPUID calls, file I/O |
| All query functions | O(1), ~nanoseconds | Simple memory reads |
