# atomics — Specification

## Overview

Provides atomic operations with explicit memory ordering. All operations are lock-free on supported platforms.

## Invariants

1. **Atomicity**: All operations complete without interference from other threads.
2. **Memory ordering**: Operations respect specified memory order constraints.
3. **Progress**: All operations are lock-free (no internal locks).

## Contracts by Operation

### cc_atomic_ptr_load

**Signature:**
```c
void* cc_atomic_ptr_load(cc_atomic_ptr_t *a, cc_memory_order_t order);
```

**Preconditions:**
- `a` is non-NULL and properly aligned
- `order` is CC_RELAXED, CC_CONSUME, CC_ACQUIRE, or CC_SEQ_CST

**Postconditions:**
- Returns the current value atomically
- Memory operations after load see effects visible before the matching store (if acquire/seq_cst)

**Thread Safety:** Lock-free

---

### cc_atomic_ptr_store

**Signature:**
```c
void cc_atomic_ptr_store(cc_atomic_ptr_t *a, void *val, cc_memory_order_t order);
```

**Preconditions:**
- `a` is non-NULL and properly aligned
- `order` is CC_RELAXED, CC_RELEASE, or CC_SEQ_CST

**Postconditions:**
- Value is atomically written
- Memory operations before store are visible to loads with acquire/seq_cst

**Thread Safety:** Lock-free

---

### cc_atomic_ptr_cas_weak

**Signature:**
```c
bool cc_atomic_ptr_cas_weak(
    cc_atomic_ptr_t *a,
    void **expected,
    void *desired,
    cc_memory_order_t success,
    cc_memory_order_t failure
);
```

**Preconditions:**
- `a`, `expected` non-NULL and aligned
- `failure` order ≤ `success` order
- `failure` is not CC_RELEASE or CC_ACQ_REL

**Postconditions:**
- If `*a == *expected`: `*a` set to `desired`, returns true
- Else: `*expected` set to current value, returns false
- May spuriously fail (return false even when equal)

**Thread Safety:** Lock-free

---

### cc_atomic_ptr_cas_strong

**Signature:**
```c
bool cc_atomic_ptr_cas_strong(
    cc_atomic_ptr_t *a,
    void **expected,
    void *desired,
    cc_memory_order_t success,
    cc_memory_order_t failure
);
```

**Preconditions:** Same as cas_weak

**Postconditions:**
- Same as cas_weak but no spurious failures
- Only fails if `*a != *expected`

**Thread Safety:** Lock-free

---

### cc_atomic_size_fetch_add

**Signature:**
```c
size_t cc_atomic_size_fetch_add(cc_atomic_size_t *a, size_t val, cc_memory_order_t order);
```

**Preconditions:**
- `a` is non-NULL and aligned

**Postconditions:**
- Returns previous value
- Atomically adds `val` to stored value

**Thread Safety:** Lock-free

---

### cc_atomic_thread_fence

**Signature:**
```c
void cc_atomic_thread_fence(cc_memory_order_t order);
```

**Preconditions:**
- `order` is valid

**Postconditions:**
- Memory barrier of specified strength is executed
- Synchronizes with matching fences/atomic ops in other threads

**Thread Safety:** N/A (synchronization primitive)

## Memory Model

This module implements the C11 memory model:

| Order | Guarantees |
|-------|------------|
| CC_RELAXED | Atomicity only, no ordering |
| CC_CONSUME | Data-dependent loads see prior writes |
| CC_ACQUIRE | Loads see all writes before matching release |
| CC_RELEASE | Writes visible to subsequent acquire loads |
| CC_ACQ_REL | Both acquire and release |
| CC_SEQ_CST | Total order across all seq_cst operations |

## Performance Bounds

| Operation | Complexity | Hardware |
|-----------|------------|----------|
| load | O(1) | Single instruction |
| store | O(1) | Single instruction |
| CAS | O(1) | Single instruction (may retry internally) |
| fetch_add | O(1) | Single instruction (lock prefix on x86) |
| fence | O(1) | mfence/dmb instruction |
