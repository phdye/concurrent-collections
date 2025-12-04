# smr_debra — Design

## Overview

The `smr_debra` module implements DEBRA+ (Distributed Epoch-Based Reclamation Algorithm with Neutralization), an advanced safe memory reclamation scheme. DEBRA+ extends basic epoch-based reclamation with signal-based thread neutralization to handle stalled threads.

## Dependencies

| Dependency | Purpose |
|------------|---------|
| atomics | Atomic operations for epoch tracking |
| config | Runtime configuration, thread detection |
| mimalloc_glue | Actual memory allocation/deallocation |
| smr_ibr | Shared epoch concepts (may share code) |

## Why DEBRA+ Over Basic IBR?

| Feature | IBR | DEBRA+ |
|---------|-----|--------|
| Stalled thread handling | Blocks reclamation | Signal-based neutralization |
| Memory bound guarantee | Weak (depends on cooperation) | Strong (O(T × R)) |
| Complexity | Simple | Moderate |
| Portability | High | Requires signals (POSIX) |

**Use Case**: DEBRA+ is preferred when:
- Applications may have threads that stall (blocking I/O, page faults)
- Stricter memory bounds are required
- Running on POSIX systems (Linux, macOS)

## Architecture

### Core Concept: Neutralization

When a thread stalls, other threads can "neutralize" it via a signal:

```
Thread A (stalled)         Thread B (wants to reclaim)
────────────────          ─────────────────────────────
enter(epoch=2)
  read(node)
  <page fault>             detect_stall(A)
                           send_signal(A, SIGURG)
  <signal handler>
  save_context()
  exit()                   # A no longer blocks reclamation
  <resume later>
  re-enter()
  re-read(node)            # May get different value!
```

### Key Insight: Helping vs Blocking

Traditional IBR: stalled thread blocks everyone.
DEBRA+: other threads "help" by neutralizing the stalled thread.

The neutralized thread must be prepared to:
1. Exit critical section (in signal handler)
2. Re-enter and re-read data (may have changed)
3. Handle operation restart

### Data Structures

```c
// Global state (extends smr_ibr)
typedef struct {
    // Epoch tracking (same as IBR)
    atomic_uint64_t global_epoch;
    atomic_uint64_t thread_epochs[MAX_THREADS];
    atomic_bool thread_active[MAX_THREADS];

    // DEBRA+ additions
    atomic_bool thread_neutralized[MAX_THREADS];  // Was thread neutralized?
    pthread_t thread_handles[MAX_THREADS];        // For sending signals
    atomic_uint32_t neutralize_count;             // Statistics
} debra_global_t;

// Per-thread state
typedef struct {
    // Same as IBR
    uint64_t local_epoch;
    retire_list_t* retire_lists[3];
    uint32_t retire_count;
    uint32_t thread_id;

    // DEBRA+ additions
    sigjmp_buf checkpoint;           // For longjmp after signal
    bool checkpoint_valid;           // Is checkpoint set?
    bool was_neutralized;            // Check after operations
    uint32_t operation_count;        // For poll scheduling
} debra_thread_t;
```

### Signal Handler

```c
// Installed for SIGURG (out-of-band signal)
static void debra_signal_handler(int sig, siginfo_t* info, void* ctx) {
    debra_thread_t* thr = get_thread_debra();
    if (!thr || !thr->checkpoint_valid) {
        return;  // Not in critical section, ignore
    }

    // Mark as neutralized
    atomic_store(&g_debra.thread_neutralized[thr->thread_id], true);
    thr->was_neutralized = true;

    // Exit critical section
    atomic_store(&g_debra.thread_active[thr->thread_id], false);

    // Jump back to checkpoint (abort current operation)
    siglongjmp(thr->checkpoint, 1);
}
```

### Enter Critical Section (DEBRA+)

```c
bool debra_enter(debra_thread_t* thr) {
    // Set checkpoint for neutralization
    if (sigsetjmp(thr->checkpoint, 1) != 0) {
        // Returned here from signal handler
        // Operation was aborted, must restart
        return false;  // Tell caller to retry
    }
    thr->checkpoint_valid = true;

    // Standard epoch entry
    uint64_t epoch = atomic_load(&g_debra.global_epoch);
    thr->local_epoch = epoch;
    atomic_store(&g_debra.thread_epochs[thr->thread_id], epoch);
    atomic_store(&g_debra.thread_active[thr->thread_id], true);

    atomic_thread_fence(memory_order_seq_cst);

    return true;  // Proceed with operation
}
```

### Exit Critical Section (DEBRA+)

```c
void debra_exit(debra_thread_t* thr) {
    thr->checkpoint_valid = false;  // Disable neutralization

    atomic_store(&g_debra.thread_active[thr->thread_id], false);

    // Opportunistic reclamation
    if (++thr->operation_count >= POLL_INTERVAL) {
        thr->operation_count = 0;
        debra_poll(thr);
    }
}
```

### Neutralization

```c
bool debra_try_neutralize(uint32_t thread_id) {
    // Check if thread is stalled
    if (!atomic_load(&g_debra.thread_active[thread_id])) {
        return false;  // Not active, nothing to do
    }

    uint64_t thread_epoch = atomic_load(&g_debra.thread_epochs[thread_id]);
    uint64_t global = atomic_load(&g_debra.global_epoch);

    if (global - thread_epoch < STALL_THRESHOLD) {
        return false;  // Not stalled yet
    }

    // Send neutralization signal
    pthread_t handle = g_debra.thread_handles[thread_id];
    int rc = pthread_kill(handle, SIGURG);

    if (rc == 0) {
        atomic_fetch_add(&g_debra.neutralize_count, 1);
        return true;
    }
    return false;
}
```

### Poll with Neutralization

```c
void debra_poll(debra_thread_t* thr) {
    uint64_t safe_epoch = debra_compute_safe_epoch();

    // Check for stalled threads blocking reclamation
    if (thr->retire_count > LIMBO_THRESHOLD) {
        for (int t = 0; t < MAX_THREADS; t++) {
            if (debra_is_stalled(t)) {
                debra_try_neutralize(t);
            }
        }
        // Recompute after neutralization
        safe_epoch = debra_compute_safe_epoch();
    }

    // Standard reclamation (same as IBR)
    for (int i = 0; i < 3; i++) {
        retire_list_t* list = thr->retire_lists[i];
        if (list->epoch < safe_epoch && list->count > 0) {
            for (uint32_t j = 0; j < list->count; j++) {
                retire_entry_t* e = &list->entries[j];
                e->free_fn(e->ptr, e->size);
            }
            list->count = 0;
        }
    }
}
```

## Operation Patterns

### Basic Operation with Restart

```c
PyObject* skiplist_get(SkipListMapObject* self, PyObject* key) {
    debra_thread_t* thr = get_thread_debra();

restart:
    if (!debra_enter(thr)) {
        goto restart;  // Was neutralized, retry
    }

    PyObject* result = find_internal(self, key);

    // Check for neutralization before using result
    if (thr->was_neutralized) {
        thr->was_neutralized = false;
        debra_exit(thr);
        goto restart;
    }

    // Safe to use result
    Py_XINCREF(result);
    debra_exit(thr);

    return result;
}
```

### Write Operation with Restart

```c
int skiplist_put(SkipListMapObject* self, PyObject* key, PyObject* value) {
    debra_thread_t* thr = get_thread_debra();

restart:
    if (!debra_enter(thr)) {
        goto restart;
    }

    int result = insert_internal(self, key, value);

    if (thr->was_neutralized) {
        thr->was_neutralized = false;
        // Note: insert may have partially succeeded
        // Need operation-specific rollback or idempotent retry
        debra_exit(thr);
        goto restart;
    }

    debra_exit(thr);
    return result;
}
```

## Memory Bound Guarantee

DEBRA+ provides a stronger memory bound than IBR:

**Theorem**: With T threads, retire threshold R, and neutralization:
- Maximum pending nodes: O(T × R)
- Not O(T² × R) like IBR worst case

**Proof Sketch**:
1. Each thread contributes at most R nodes before triggering reclamation
2. Stalled threads are neutralized, so they exit critical section
3. No thread blocks reclamation indefinitely
4. Therefore, at most T × R nodes can accumulate before safe_epoch advances

## Platform Considerations

### Signal Selection

| Signal | Pros | Cons |
|--------|------|------|
| SIGURG | Out-of-band, rarely used | May conflict with select() |
| SIGUSR1/2 | Standard user signals | Often used by apps |
| SIGRTMIN+n | Real-time, reserved | Less portable |

**Choice**: SIGURG as default, configurable.

### Windows Compatibility

DEBRA+ uses POSIX signals unavailable on Windows. Options:

1. **Fallback to IBR**: No neutralization on Windows
2. **Thread Suspension**: Use SuspendThread/ResumeThread (risky)
3. **Cooperative Polling**: Require threads to check flag periodically

**Implementation**: Fallback to IBR on Windows.

```c
#if defined(_WIN32)
    // Windows: no signal support, fall back to basic epoch
    #define DEBRA_NEUTRALIZATION_SUPPORTED 0
#else
    #define DEBRA_NEUTRALIZATION_SUPPORTED 1
#endif
```

## API Surface

### C API

```c
// Initialization
int debra_init(void);
void debra_shutdown(void);

// Thread registration
debra_thread_t* debra_thread_register(void);
void debra_thread_unregister(debra_thread_t* thr);

// Critical section (returns false if neutralized)
bool debra_enter(debra_thread_t* thr);
void debra_exit(debra_thread_t* thr);

// Check neutralization
bool debra_was_neutralized(debra_thread_t* thr);
void debra_clear_neutralized(debra_thread_t* thr);

// Retirement (same as IBR)
void debra_retire(debra_thread_t* thr, void* ptr, size_t size,
                  void (*free_fn)(void*, size_t));

// Reclamation
void debra_poll(debra_thread_t* thr);

// Diagnostics
uint64_t debra_get_epoch(void);
uint64_t debra_pending_count(debra_thread_t* thr);
uint32_t debra_neutralize_count(void);
```

### Python Integration

```python
from concurrent_collections import config

# Select SMR scheme (default: 'ibr')
config.smr_scheme = 'debra'  # Use DEBRA+ with neutralization

# DEBRA+ specific config
config.debra_stall_threshold = 100     # Epochs before stall detection
config.debra_neutralize_signal = 23    # SIGURG by default
```

## Design Decisions

| Decision | Choice | Rationale |
|----------|--------|-----------|
| Signal for neutralization | SIGURG | Least likely to conflict |
| Checkpoint mechanism | sigsetjmp/siglongjmp | Portable, async-signal-safe |
| Fallback on Windows | Basic IBR | No portable signal mechanism |
| Stall threshold | Configurable (default 100) | Balance responsiveness vs overhead |
| Neutralization trigger | On poll when limbo full | Demand-driven, not proactive |

## Configuration

| Parameter | Default | Description |
|-----------|---------|-------------|
| `retire_threshold` | 64 | Nodes before triggering reclamation |
| `stall_threshold` | 100 | Epochs before thread considered stalled |
| `poll_interval` | 32 | Operations between poll attempts |
| `limbo_threshold` | 256 | Pending nodes before neutralization attempt |
| `signal_number` | SIGURG | Signal for neutralization |

## Performance Characteristics

### Overhead

| Operation | Cost | Notes |
|-----------|------|-------|
| `debra_enter` | ~15-25ns | sigsetjmp overhead |
| `debra_exit` | ~5ns | Same as IBR |
| `debra_retire` | ~20ns | Same as IBR |
| `debra_poll` | ~50ns-5μs | Depends on nodes to free |
| Signal send | ~1-5μs | Infrequent |
| Signal receive | ~10-50μs | Includes longjmp |

### When Neutralization Occurs

Neutralization is rare in well-behaved applications:
- Only when threads actually stall (blocking I/O, page faults)
- Threshold prevents false positives
- One-time cost per stall event

## Comparison with Other Schemes

| Scheme | Stall Handling | Memory Bound | Complexity |
|--------|----------------|--------------|------------|
| IBR | None (blocks) | O(T²R) | Simple |
| DEBRA+ | Signal neutralization | O(TR) | Moderate |
| Hazard Pointers | N/A (per-object) | O(T×HP) | Simple |
| EBR | None (blocks) | O(T²R) | Simple |

## Open Questions

| Question | Options | Impact |
|----------|---------|--------|
| Signal choice | SIGURG vs SIGUSR1 | App compatibility |
| Nested critical sections | Disallow vs track depth | API complexity |
| Windows implementation | IBR fallback vs suspension | Platform parity |

## References

- Brown, T. "Reclaiming Memory for Lock-Free Data Structures: There has to be a Better Way" (2015)
- DEBRA original paper: epoch-based with quiescent state detection
- DEBRA+: adds signal-based neutralization for non-quiescent threads
