# smr_ibr — Design

## Overview

The `smr_ibr` module implements Interval-Based Reclamation (IBR), a safe memory reclamation scheme for lock-free data structures. IBR solves the fundamental problem of determining when it's safe to free memory that may still be accessed by concurrent readers.

## Dependencies

| Dependency | Purpose |
|------------|---------|
| atomics | Atomic operations for epoch tracking |
| config | Runtime configuration, thread detection |
| mimalloc_glue | Actual memory allocation/deallocation |

## The Problem: Safe Memory Reclamation

In lock-free data structures:
```
Thread A                    Thread B
────────                    ────────
node = find(key)
                           delete(key)
                           // When can we free node?
read(node->value)          // Thread A still holds reference!
                           free(node)  // CRASH: use-after-free
```

**Challenge**: Thread B cannot know when Thread A is done accessing the node.

**Solution**: Defer freeing until we can prove no thread holds a reference.

## Architecture

### Core Concept: Epochs

IBR divides time into epochs. Each thread records which epoch it entered:

```
Global Epoch:  [1]─────────[2]─────────[3]─────────[4]
                    │           │           │
Thread 1:      ▓▓▓▓▓▓▓▓[2]──────────────────────▓▓▓▓▓
Thread 2:      ▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓[2]──────[3]──────────
Thread 3:      ▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓[3]───────

Legend: ▓▓▓ = outside critical section, [N] = in epoch N
```

**Key Insight**: A node retired in epoch E can only be freed when NO thread is in epoch ≤ E.

### Data Structures

```c
// Global state
typedef struct {
    atomic_uint64_t global_epoch;           // Current global epoch
    atomic_uint64_t thread_epochs[MAX_THREADS]; // Per-thread epoch
    atomic_bool thread_active[MAX_THREADS];  // Thread in critical section?
} smr_global_t;

// Per-thread state
typedef struct {
    uint64_t local_epoch;                   // Cached local epoch
    retire_list_t* retire_lists[3];         // Limbo lists per epoch (ring buffer)
    uint32_t retire_count;                  // Items in current limbo list
    uint32_t thread_id;                     // Thread's slot in global arrays
} smr_thread_t;

// Retired node entry
typedef struct {
    void* ptr;                              // Pointer to retired node
    size_t size;                            // Node size (for stats)
    void (*free_fn)(void*, size_t);         // Free callback
} retire_entry_t;

// Limbo list (nodes pending reclamation)
typedef struct retire_list {
    retire_entry_t* entries;
    uint32_t count;
    uint32_t capacity;
    uint64_t epoch;                         // Epoch when nodes were retired
} retire_list_t;
```

### IBR Algorithm

#### Enter Critical Section

```c
void smr_enter(smr_thread_t* thr) {
    // Load current global epoch
    uint64_t epoch = atomic_load_explicit(&g_smr.global_epoch, memory_order_acquire);

    // Record that this thread is in this epoch
    thr->local_epoch = epoch;
    atomic_store_explicit(&g_smr.thread_epochs[thr->thread_id], epoch, memory_order_release);
    atomic_store_explicit(&g_smr.thread_active[thr->thread_id], true, memory_order_release);

    // Memory barrier ensures epoch is visible before any data access
    atomic_thread_fence(memory_order_seq_cst);
}
```

#### Exit Critical Section

```c
void smr_exit(smr_thread_t* thr) {
    // Clear active flag - we're no longer holding references
    atomic_store_explicit(&g_smr.thread_active[thr->thread_id], false, memory_order_release);

    // Opportunistically try to reclaim
    if (thr->retire_count >= RETIRE_THRESHOLD) {
        smr_poll(thr);
    }
}
```

#### Retire a Node

```c
void smr_retire(smr_thread_t* thr, void* ptr, size_t size, void (*free_fn)(void*, size_t)) {
    // Get current limbo list (indexed by epoch mod 3)
    uint64_t epoch = thr->local_epoch;
    retire_list_t* list = thr->retire_lists[epoch % 3];

    // Add to limbo list
    list->entries[list->count++] = (retire_entry_t){ptr, size, free_fn};
    thr->retire_count++;

    // Try to advance epoch if we've retired enough
    if (thr->retire_count >= RETIRE_THRESHOLD) {
        smr_try_advance_epoch(thr);
        smr_poll(thr);
    }
}
```

#### Poll for Reclamation

```c
void smr_poll(smr_thread_t* thr) {
    uint64_t safe_epoch = smr_compute_safe_epoch();

    // Free nodes from epochs older than safe_epoch
    for (int i = 0; i < 3; i++) {
        retire_list_t* list = thr->retire_lists[i];
        if (list->epoch < safe_epoch && list->count > 0) {
            // Safe to free all nodes in this list
            for (uint32_t j = 0; j < list->count; j++) {
                retire_entry_t* e = &list->entries[j];
                e->free_fn(e->ptr, e->size);
            }
            list->count = 0;
            thr->retire_count -= list->count;
        }
    }
}

uint64_t smr_compute_safe_epoch(void) {
    uint64_t min_epoch = UINT64_MAX;

    for (int t = 0; t < MAX_THREADS; t++) {
        if (atomic_load_explicit(&g_smr.thread_active[t], memory_order_acquire)) {
            uint64_t epoch = atomic_load_explicit(&g_smr.thread_epochs[t], memory_order_acquire);
            if (epoch < min_epoch) {
                min_epoch = epoch;
            }
        }
    }

    return min_epoch;
}
```

#### Advance Global Epoch

```c
void smr_try_advance_epoch(smr_thread_t* thr) {
    uint64_t current = atomic_load_explicit(&g_smr.global_epoch, memory_order_acquire);
    uint64_t safe = smr_compute_safe_epoch();

    // Can only advance if all active threads have caught up
    if (safe >= current) {
        // CAS to avoid duplicate advances
        atomic_compare_exchange_strong(&g_smr.global_epoch, &current, current + 1);
    }
}
```

### Memory Bound Analysis

With T threads and retire threshold R:
- Each thread can have up to 3R nodes in limbo (3 epoch lists)
- Worst case: 3 × T × R nodes pending
- Memory bound: O(T²R) in pathological cases where all threads retire simultaneously

**Typical case**: Much better, as epochs advance and nodes are reclaimed promptly.

### Handling Stalled Threads

A stalled thread (blocking I/O, long computation) holds an old epoch, blocking reclamation.

**Detection:**
```c
bool smr_is_stalled(int thread_id, uint64_t threshold_epochs) {
    if (!atomic_load(&g_smr.thread_active[thread_id])) {
        return false;  // Not active, not stalled
    }

    uint64_t global = atomic_load(&g_smr.global_epoch);
    uint64_t thread_epoch = atomic_load(&g_smr.thread_epochs[thread_id]);

    return (global - thread_epoch) > threshold_epochs;
}
```

**Mitigation Strategies:**
1. **Cooperative Exit**: Document that threads should exit SMR during long operations
2. **Epoch Timeout**: Force-advance epoch after timeout (with caution)
3. **Thread Cleanup**: Unregister threads that exit/crash

## API Surface

### C API

```c
// Global initialization
int smr_init(void);
void smr_shutdown(void);

// Thread registration (must call before using SMR)
smr_thread_t* smr_thread_register(void);
void smr_thread_unregister(smr_thread_t* thr);

// Critical section
void smr_enter(smr_thread_t* thr);
void smr_exit(smr_thread_t* thr);

// Node retirement
void smr_retire(smr_thread_t* thr, void* ptr, size_t size, void (*free_fn)(void*, size_t));

// Manual reclamation poll
void smr_poll(smr_thread_t* thr);

// Diagnostics
uint64_t smr_get_epoch(void);
uint64_t smr_pending_count(smr_thread_t* thr);
```

### Python Integration

```python
# Automatic per-thread registration via TLS
# User doesn't interact with SMR directly

# Diagnostic access via config
from concurrent_collections import config

config.smr_scheme = 'ibr'  # Default
config.retire_threshold = 64
config.max_reclaim_per_poll = 32

# Statistics (if enabled)
stats = config.smr_stats()
print(f"Global epoch: {stats.global_epoch}")
print(f"Pending nodes: {stats.pending_count}")
```

## Integration with Containers

### SkipListMap Example

```c
// In SkipListMap delete operation
static PyObject* skiplist_delete(SkipListMapObject* self, PyObject* key) {
    smr_thread_t* smr = get_thread_smr();
    smr_enter(smr);

    SkipListNode* node = find_and_unlink(self, key);
    if (node) {
        // Node is unlinked but may still be accessed by concurrent readers
        smr_retire(smr, node, sizeof(SkipListNode), skiplist_node_free);
    }

    smr_exit(smr);
    Py_RETURN_NONE;
}

// Free callback
static void skiplist_node_free(void* ptr, size_t size) {
    SkipListNode* node = (SkipListNode*)ptr;
    Py_DECREF(node->key);
    Py_DECREF(node->value);
    cc_free(ptr, size);
}
```

## Design Decisions

| Decision | Choice | Rationale |
|----------|--------|-----------|
| Epoch representation | uint64_t | Effectively infinite (no overflow in practice) |
| Limbo list count | 3 (ring buffer) | Sufficient for 2-epoch lag + current |
| Thread tracking | Array | Simple, O(1) lookup, fixed max threads |
| Retirement trigger | Count-based | Amortizes reclamation cost |
| Free callback | Function pointer | Flexible for different node types |

## Configuration

| Parameter | Default | Description |
|-----------|---------|-------------|
| `retire_threshold` | 64 | Nodes before triggering reclamation |
| `max_reclaim_per_poll` | 32 | Max nodes freed per poll |
| `max_threads` | 256 | Maximum concurrent threads |
| `stall_threshold_epochs` | 100 | Epochs before thread considered stalled |

## Performance Characteristics

### Overhead

| Operation | Cost | Notes |
|-----------|------|-------|
| `smr_enter` | ~5-10ns | One atomic load, one store, fence |
| `smr_exit` | ~5ns | One atomic store |
| `smr_retire` | ~20ns | List append, occasional poll |
| `smr_poll` | ~50ns-5μs | Depends on nodes to free |

### Scalability

- Thread-local retire lists minimize contention
- Global epoch read is shared (cache line)
- Epoch advance is CAS-based (single writer wins)
- Scales well to 32+ threads

## Open Questions

| Question | Options | Impact |
|----------|---------|--------|
| Thread registration | Explicit vs automatic | API complexity vs safety |
| Stalled thread handling | Timeout vs signal | Complexity vs reliability |
| Per-container vs global SMR | Separate vs shared | Memory vs simplicity |
