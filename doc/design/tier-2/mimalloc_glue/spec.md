# mimalloc_glue — Specification

## Overview

The `mimalloc_glue` module provides guaranteed thread-safe memory allocation with cross-thread free support. All operations are non-blocking on the fast path.

## Invariants

1. **Thread Safety**: All allocation and free operations are thread-safe
2. **Cross-Thread Free**: Memory allocated by thread A can be freed by thread B
3. **Alignment Guarantee**: `cc_alloc_aligned` returns memory aligned to requested boundary
4. **No Leaks**: Every successful allocation must eventually be freed
5. **Statistics Consistency**: Statistics reflect actual allocations (if enabled)

## Preconditions

- mimalloc library linked and initialized
- `size > 0` for all allocation functions
- `alignment` must be power of 2 and >= `sizeof(void*)`
- `ptr` passed to `cc_free` must be from `cc_alloc*` or NULL

## Contracts by Operation

### cc_alloc

**Signature:**
```c
void* cc_alloc(size_t size);
```

**Description:** Allocate `size` bytes of uninitialized memory.

**Preconditions:**
- `size > 0`

**Postconditions:**
- Returns non-NULL pointer to at least `size` bytes, OR
- Returns NULL on allocation failure

**Errors:**
- Returns NULL if allocation fails (out of memory)

**Complexity:** O(1) amortized

**Thread Safety:** Thread-safe, non-blocking fast path

---

### cc_calloc

**Signature:**
```c
void* cc_calloc(size_t count, size_t size);
```

**Description:** Allocate `count * size` bytes, zero-initialized.

**Preconditions:**
- `count * size > 0`
- `count * size` does not overflow

**Postconditions:**
- Returns non-NULL pointer to zeroed memory, OR
- Returns NULL on allocation failure

**Errors:**
- Returns NULL if allocation fails

**Complexity:** O(count * size) for zeroing

**Thread Safety:** Thread-safe

---

### cc_alloc_aligned

**Signature:**
```c
void* cc_alloc_aligned(size_t size, size_t alignment);
```

**Description:** Allocate `size` bytes aligned to `alignment` boundary.

**Preconditions:**
- `size > 0`
- `alignment` is power of 2
- `alignment >= sizeof(void*)`

**Postconditions:**
- Returns pointer where `(uintptr_t)ptr % alignment == 0`, OR
- Returns NULL on failure

**Errors:**
- Returns NULL if allocation fails
- Behavior undefined if alignment is not power of 2

**Complexity:** O(1) amortized

**Thread Safety:** Thread-safe

---

### cc_alloc_node

**Signature:**
```c
void* cc_alloc_node(size_t size);
```

**Description:** Allocate cache-line aligned memory for a node structure.

**Preconditions:**
- `size > 0`

**Postconditions:**
- Returns pointer aligned to `CC_CACHE_LINE_SIZE` (64 bytes), OR
- Returns NULL on failure

**Errors:**
- Returns NULL if allocation fails

**Complexity:** O(1) amortized

**Thread Safety:** Thread-safe

---

### cc_free

**Signature:**
```c
void cc_free(void* ptr, size_t size);
```

**Description:** Free memory previously allocated by `cc_alloc*`.

**Preconditions:**
- `ptr` was returned by `cc_alloc*`, OR `ptr` is NULL
- `ptr` has not been previously freed

**Postconditions:**
- Memory is returned to the allocator
- `ptr` is no longer valid

**Errors:**
- None (NULL is safe no-op)
- Double-free is undefined behavior

**Complexity:** O(1) amortized

**Thread Safety:** Thread-safe, can be called from any thread

---

### cc_free_unsized

**Signature:**
```c
void cc_free_unsized(void* ptr);
```

**Description:** Free memory without size tracking (for compatibility).

**Preconditions:**
- Same as `cc_free`

**Postconditions:**
- Same as `cc_free`
- Statistics only track count, not bytes

**Thread Safety:** Thread-safe

---

### cc_alloc_stats_enable

**Signature:**
```c
void cc_alloc_stats_enable(bool enable);
```

**Description:** Enable or disable allocation statistics collection.

**Preconditions:** None

**Postconditions:**
- Future allocations/frees update statistics if enabled

**Thread Safety:** Thread-safe (atomic flag)

---

### cc_alloc_stats_snapshot

**Signature:**
```c
cc_alloc_snapshot_t cc_alloc_stats_snapshot(void);
```

**Description:** Get current allocation statistics.

**Preconditions:** None

**Postconditions:**
- Returns consistent snapshot of statistics
- Does not reset counters

**Thread Safety:** Thread-safe (atomic reads)

---

### cc_alloc_stats_reset

**Signature:**
```c
void cc_alloc_stats_reset(void);
```

**Description:** Reset allocation statistics to zero.

**Preconditions:** None

**Postconditions:**
- All counters set to zero

**Thread Safety:** Thread-safe (atomic stores)

## Error Handling

| Error Condition | Detection | Response |
|-----------------|-----------|----------|
| Out of memory | `mi_malloc` returns NULL | Return NULL |
| Zero size | Size check | Return NULL |
| Invalid alignment | Not validated | Undefined behavior |
| Double free | Not detected at runtime | Undefined (use ASAN) |

## Thread Safety Summary

| Guarantee | Scope | Notes |
|-----------|-------|-------|
| Allocation thread-safe | All `cc_alloc*` | via mimalloc thread-local |
| Free from any thread | `cc_free*` | mimalloc cross-thread support |
| Statistics thread-safe | All stats functions | Atomic operations |

## Memory Model

### Ordering Guarantees

- Statistics use `memory_order_relaxed` (sufficient for counters)
- No ordering guarantees between allocation and free across threads
- SMR layer provides necessary ordering for node access

### Visibility

- Allocated memory is immediately visible to allocating thread
- Cross-thread visibility requires explicit synchronization (SMR provides this)

## Performance Bounds

| Operation | Average | Worst Case | Notes |
|-----------|---------|------------|-------|
| `cc_alloc` | O(1) | O(n) | n = heap cleanup work |
| `cc_free` same thread | O(1) | O(1) | Thread-local free |
| `cc_free` cross thread | O(1) | O(n) | Transfer to owning heap |
| Statistics update | O(1) | O(1) | Single atomic op |

## Statistics Contract

```c
typedef struct {
    uint64_t alloc_count;      // Total allocations
    uint64_t free_count;       // Total frees
    uint64_t alloc_bytes;      // Total bytes allocated
    uint64_t free_bytes;       // Total bytes freed
    uint64_t current_allocated; // alloc_bytes - free_bytes
} cc_alloc_snapshot_t;
```

**Invariants:**
- `current_allocated >= 0` (may temporarily violate due to relaxed ordering)
- `free_count <= alloc_count` (eventually consistent)
- Statistics are approximate due to relaxed atomics

## Platform-Specific Behavior

| Platform | Cache Line Size | Notes |
|----------|-----------------|-------|
| x86-64 | 64 bytes | Standard |
| ARM64 | 64 bytes | Standard |
| Apple M1/M2 | 128 bytes | Consider 128 for optimal |

## Interaction with SMR

The SMR layer uses `mimalloc_glue` with these guarantees:

1. **Allocation**: Node allocated during container operation
2. **Retirement**: Node added to retire list (not yet freed)
3. **Reclamation**: SMR determines safe, calls `cc_free`

```
Time →
Thread A: cc_alloc() ──────────────────────────────────────────────→
Thread B:           smr_retire() ──────────────────────────────────→
Thread C:                        [epoch passes] cc_free() ─────────→
```

The gap between retire and free is managed by SMR; `mimalloc_glue` simply provides the allocation/free primitives.
