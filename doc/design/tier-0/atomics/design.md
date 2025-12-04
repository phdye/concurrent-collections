# atomics — Design

## Overview

The `atomics` module provides a portable abstraction over atomic operations and memory barriers. It wraps C11 atomics with platform-specific fallbacks for MSVC and provides higher-level primitives used throughout the library.

## Dependencies

| Dependency | Purpose |
|------------|---------|
| C11 `<stdatomic.h>` | Primary atomic implementation |
| MSVC `<intrin.h>` | Windows intrinsics fallback |
| arch_detect | Feature detection for optimal paths |

## Architecture

### Core Types

```c
// Atomic pointer type (most common)
typedef struct {
    _Atomic(void*) value;
} cc_atomic_ptr_t;

// Atomic size_t for counters
typedef struct {
    _Atomic(size_t) value;
} cc_atomic_size_t;

// Atomic uint64 for timestamps/versions
typedef struct {
    _Atomic(uint64_t) value;
} cc_atomic_u64_t;

// 128-bit for DCAS (x86-64 only)
typedef struct {
    __int128 value;  // Or platform equivalent
} cc_atomic_u128_t;
```

### Memory Orders

```c
typedef enum {
    CC_RELAXED = memory_order_relaxed,
    CC_CONSUME = memory_order_consume,
    CC_ACQUIRE = memory_order_acquire,
    CC_RELEASE = memory_order_release,
    CC_ACQ_REL = memory_order_acq_rel,
    CC_SEQ_CST = memory_order_seq_cst
} cc_memory_order_t;
```

### Operations

| Operation | Description | Use Case |
|-----------|-------------|----------|
| load | Atomic read | Reading shared state |
| store | Atomic write | Publishing updates |
| exchange | Atomic swap | Lock acquisition |
| compare_exchange_weak | CAS (may spuriously fail) | Retry loops |
| compare_exchange_strong | CAS (no spurious failure) | Single attempts |
| fetch_add | Atomic increment | Counters |
| fetch_sub | Atomic decrement | Counters |
| fetch_or | Atomic OR | Flag setting |
| fetch_and | Atomic AND | Flag clearing |

### Platform Abstraction

```c
// Example: CAS abstraction
static inline bool cc_atomic_ptr_cas_weak(
    cc_atomic_ptr_t *atom,
    void **expected,
    void *desired,
    cc_memory_order_t success,
    cc_memory_order_t failure
) {
#if defined(__STDC_VERSION__) && __STDC_VERSION__ >= 201112L
    return atomic_compare_exchange_weak_explicit(
        &atom->value, expected, desired, success, failure
    );
#elif defined(_MSC_VER)
    void *old = *expected;
    void *prev = InterlockedCompareExchangePointer(
        (volatile PVOID*)&atom->value, desired, old
    );
    if (prev == old) return true;
    *expected = prev;
    return false;
#endif
}
```

## API Surface

### Pointer Atomics

```c
void* cc_atomic_ptr_load(cc_atomic_ptr_t *a, cc_memory_order_t order);
void cc_atomic_ptr_store(cc_atomic_ptr_t *a, void *val, cc_memory_order_t order);
void* cc_atomic_ptr_exchange(cc_atomic_ptr_t *a, void *val, cc_memory_order_t order);
bool cc_atomic_ptr_cas_weak(cc_atomic_ptr_t *a, void **exp, void *des, cc_memory_order_t s, cc_memory_order_t f);
bool cc_atomic_ptr_cas_strong(cc_atomic_ptr_t *a, void **exp, void *des, cc_memory_order_t s, cc_memory_order_t f);
```

### Integer Atomics

```c
size_t cc_atomic_size_load(cc_atomic_size_t *a, cc_memory_order_t order);
void cc_atomic_size_store(cc_atomic_size_t *a, size_t val, cc_memory_order_t order);
size_t cc_atomic_size_fetch_add(cc_atomic_size_t *a, size_t val, cc_memory_order_t order);
size_t cc_atomic_size_fetch_sub(cc_atomic_size_t *a, size_t val, cc_memory_order_t order);
```

### Memory Barriers

```c
void cc_atomic_thread_fence(cc_memory_order_t order);
void cc_atomic_signal_fence(cc_memory_order_t order);
```

### Double-Width CAS (x86-64 only)

```c
bool cc_atomic_u128_cas(cc_atomic_u128_t *a, __int128 *exp, __int128 des);
```

## Design Decisions

| Decision | Choice | Rationale | Alternatives |
|----------|--------|-----------|--------------|
| Primary implementation | C11 atomics | Standard, portable | Inline asm (less portable) |
| MSVC fallback | Interlocked intrinsics | Required for Windows | _InterlockedCompareExchange128 |
| Memory order type | Enum wrapping stdatomic | Type safety | Raw integers |
| Weak vs strong CAS | Provide both | Different use cases | Only strong (miss optimization) |

## Open Questions

1. Should we provide `cc_atomic_ptr_load_acquire` convenience macros for common patterns?
2. Should 128-bit atomics be optional at runtime based on CMPXCHG16B detection?
