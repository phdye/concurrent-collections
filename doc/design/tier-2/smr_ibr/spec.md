# smr_ibr — Specification

## Overview

Formal specification of contracts, invariants, and safety properties for the Interval-Based Reclamation (IBR) safe memory reclamation scheme.

## Module Contracts

### Global Initialization

```c
/**
 * @function smr_init
 * @brief Initialize the global SMR state
 *
 * @pre  SMR not already initialized (single init per process)
 * @post Global epoch set to 1
 * @post All thread slots marked inactive
 * @post All thread epochs set to 0
 *
 * @returns 0 on success, -1 on failure
 * @errors  ENOMEM if allocation fails
 */
int smr_init(void);
```

```c
/**
 * @function smr_shutdown
 * @brief Shutdown the global SMR state
 *
 * @pre  All threads have unregistered
 * @pre  All retired nodes have been reclaimed
 * @post Global state freed
 *
 * @warning Calling with active threads causes undefined behavior
 */
void smr_shutdown(void);
```

### Thread Registration

```c
/**
 * @function smr_thread_register
 * @brief Register calling thread with SMR
 *
 * @pre  Thread not already registered
 * @pre  Available slot exists (thread_count < MAX_THREADS)
 * @post Thread assigned unique slot
 * @post Thread marked inactive
 * @post Thread's retire lists initialized (empty)
 *
 * @returns Pointer to thread-local SMR state
 * @returns NULL if no slots available
 */
smr_thread_t* smr_thread_register(void);
```

```c
/**
 * @function smr_thread_unregister
 * @brief Unregister calling thread from SMR
 *
 * @pre  thr != NULL
 * @pre  thr was returned by smr_thread_register on this thread
 * @pre  Thread is outside critical section (not active)
 * @post Thread's slot marked available
 * @post All pending retired nodes transferred or freed
 * @post thr is invalid (must not be used after this call)
 */
void smr_thread_unregister(smr_thread_t* thr);
```

### Critical Section

```c
/**
 * @function smr_enter
 * @brief Enter SMR critical section
 *
 * @pre  thr != NULL
 * @pre  thr is valid (registered, not unregistered)
 * @pre  Thread is not already in critical section
 * @post Thread marked active
 * @post Thread's epoch set to current global epoch
 * @post Memory fence ensures visibility before data access
 *
 * @note Reentrant calls are NOT supported (undefined behavior)
 */
void smr_enter(smr_thread_t* thr);
```

```c
/**
 * @function smr_exit
 * @brief Exit SMR critical section
 *
 * @pre  thr != NULL
 * @pre  Thread is in critical section (active)
 * @post Thread marked inactive
 * @post Thread no longer blocks reclamation
 * @post May trigger opportunistic reclamation
 *
 * @note Thread must not access protected pointers after this call
 */
void smr_exit(smr_thread_t* thr);
```

### Node Retirement

```c
/**
 * @function smr_retire
 * @brief Retire a node for deferred reclamation
 *
 * @param thr      Thread-local SMR state
 * @param ptr      Pointer to retired node
 * @param size     Size of allocation (for stats)
 * @param free_fn  Function to call when safe to free
 *
 * @pre  thr != NULL
 * @pre  ptr != NULL
 * @pre  free_fn != NULL
 * @pre  Thread is in critical section
 * @pre  Node has been logically removed (unlinked from data structure)
 * @pre  No new references to node will be created
 * @post Node added to limbo list for current epoch
 * @post Node will be freed when safe (no thread in epoch ≤ retire_epoch)
 *
 * @note free_fn must be safe to call from any thread
 * @note free_fn must handle Python reference counting if applicable
 */
void smr_retire(smr_thread_t* thr, void* ptr, size_t size,
                void (*free_fn)(void*, size_t));
```

### Reclamation

```c
/**
 * @function smr_poll
 * @brief Attempt to reclaim safe nodes
 *
 * @pre  thr != NULL
 * @post Nodes from epochs < safe_epoch are freed
 * @post Freed nodes removed from limbo lists
 *
 * @note May free zero nodes if no safe epoch exists
 * @note Called automatically during smr_exit when threshold reached
 */
void smr_poll(smr_thread_t* thr);
```

### Diagnostics

```c
/**
 * @function smr_get_epoch
 * @brief Get current global epoch
 *
 * @returns Current global epoch value
 * @note For diagnostics only; may be stale immediately after return
 */
uint64_t smr_get_epoch(void);
```

```c
/**
 * @function smr_pending_count
 * @brief Get number of nodes pending reclamation
 *
 * @pre  thr != NULL
 * @returns Number of nodes in thread's limbo lists
 */
uint64_t smr_pending_count(smr_thread_t* thr);
```

## Invariants

### Global Invariants

| ID | Invariant | Rationale |
|----|-----------|-----------|
| G1 | `global_epoch` is monotonically increasing | Epochs never go backward |
| G2 | `global_epoch` advances only when all active threads have caught up | Ensures safe reclamation |
| G3 | At most MAX_THREADS are registered at any time | Fixed array size |
| G4 | Thread slot is either available OR (assigned to exactly one thread) | No slot sharing |

### Thread Invariants

| ID | Invariant | Rationale |
|----|-----------|-----------|
| T1 | If `thread_active[t]`, then `thread_epochs[t] ≤ global_epoch` | Active threads lag at most by current epoch |
| T2 | Retire lists contain nodes from epochs `[E-2, E]` where E = current epoch | Ring buffer of 3 epochs |
| T3 | `retire_count = sum(retire_lists[*].count)` | Counter consistency |
| T4 | Thread in critical section has `local_epoch = thread_epochs[thread_id]` | Cached copy matches published |

### Reclamation Invariants

| ID | Invariant | Rationale |
|----|-----------|-----------|
| R1 | Node retired in epoch E is freed only when `safe_epoch > E` | Safety guarantee |
| R2 | `safe_epoch = min(thread_epochs[t] for all active t)` | Definition of safe epoch |
| R3 | If no threads active, `safe_epoch = global_epoch` | All epochs are safe |
| R4 | Once freed, pointer is never accessed by SMR | No use-after-free |

## Safety Properties

### S1: No Use-After-Free

**Property**: A node is never freed while any thread may hold a reference.

**Proof Sketch**:
1. Thread T acquires reference to node N by entering critical section (epoch E_T)
2. Node N retired in epoch E_R where E_R ≥ E_T (node visible when T entered)
3. Node N freed only when safe_epoch > E_R
4. safe_epoch > E_R ⟹ all active threads have epoch > E_R ⟹ T's epoch > E_R
5. T's epoch > E_R ⟹ T has exited the critical section where it held the reference
6. Therefore, N is freed only after T releases reference ∎

### S2: No Double-Free

**Property**: Each node is freed exactly once.

**Proof Sketch**:
1. Node added to exactly one limbo list (indexed by epoch % 3)
2. Limbo list cleared atomically during poll
3. Once freed, node removed from limbo list
4. Node cannot be re-added (already logically removed from data structure)
5. Therefore, each node freed at most once ∎

### S3: Progress (No Permanent Stall)

**Property**: If threads continue to enter/exit critical sections, retired nodes are eventually freed.

**Proof Sketch**:
1. Thread exiting advances its epoch to current global epoch
2. When all threads have advanced, global epoch can advance
3. Global epoch advancing increases safe_epoch
4. Eventually safe_epoch > any retire_epoch
5. Therefore, nodes are eventually freed (given continued activity) ∎

**Note**: A permanently stalled thread violates progress. See design.md for mitigation.

### S4: Memory Bound

**Property**: Pending memory is bounded by O(T × R) in typical operation.

- T = number of threads
- R = retire threshold

**Worst case**: O(T² × R) if all threads retire maximum simultaneously.

## Liveness Properties

### L1: Epoch Advancement

**Property**: Global epoch advances when all active threads are at the current epoch.

**Formula**: `∀t. (active[t] ⟹ epoch[t] = global_epoch) ⟹ ◇(global_epoch' > global_epoch)`

### L2: Reclamation

**Property**: A retired node is eventually freed (under fairness assumptions).

**Formula**: `retire(n) ⟹ ◇free(n)`

**Assumption**: No thread remains in critical section indefinitely.

## Memory Order Specification

### smr_enter

```
Load global_epoch         : acquire
Store thread_epochs[id]   : release
Store thread_active[id]   : release
Thread fence              : seq_cst
```

**Rationale**: Ensure epoch is visible before any data access in critical section.

### smr_exit

```
Store thread_active[id]   : release
```

**Rationale**: Ensure all data accesses in critical section are visible before marking inactive.

### smr_compute_safe_epoch

```
Load thread_active[t]     : acquire
Load thread_epochs[t]     : acquire (if active)
```

**Rationale**: See most recent epoch of each active thread.

### smr_try_advance_epoch

```
Load global_epoch         : acquire
CAS global_epoch          : seq_cst
```

**Rationale**: Single-writer advances epoch atomically.

## Error Handling

| Condition | Behavior |
|-----------|----------|
| `smr_init` called twice | Undefined (implementation may assert) |
| `smr_thread_register` with no slots | Returns NULL |
| `smr_enter` while already active | Undefined (not reentrant) |
| `smr_exit` while not active | Undefined |
| `smr_retire` with NULL ptr | Undefined (assert in debug) |
| `smr_retire` with NULL free_fn | Undefined (assert in debug) |
| `smr_unregister` while active | Undefined |

## Thread Safety

| Function | Thread Safety |
|----------|---------------|
| `smr_init` | Not thread-safe (call once from main thread) |
| `smr_shutdown` | Not thread-safe (call once from main thread) |
| `smr_thread_register` | Thread-safe (each thread calls once) |
| `smr_thread_unregister` | Thread-safe (each thread calls for own state) |
| `smr_enter` | Thread-safe (operates on own state) |
| `smr_exit` | Thread-safe (operates on own state) |
| `smr_retire` | Thread-safe (thread-local limbo lists) |
| `smr_poll` | Thread-safe (thread-local reclamation) |
| `smr_get_epoch` | Thread-safe (atomic read) |
| `smr_pending_count` | Thread-safe (read own state) |

## State Machine

### Thread State

```
            smr_thread_register()
UNREGISTERED ─────────────────────► REGISTERED/INACTIVE
                                           │
                                           │ smr_enter()
                                           ▼
                                    REGISTERED/ACTIVE
                                           │
                                           │ smr_exit()
                                           ▼
                                    REGISTERED/INACTIVE
                                           │
                                           │ smr_thread_unregister()
                                           ▼
                                    UNREGISTERED
```

### Node State

```
                   smr_retire()          safe_epoch > retire_epoch
LIVE ──► LOGICALLY_REMOVED ──► IN_LIMBO ──────────────────────────► FREED
```

## Formal Verification Notes

The TLA+ specification in `spec.tla` formally verifies:
- Safety property S1 (no use-after-free)
- Safety property S2 (no double-free)
- Invariants G1, G2, R1, R2

Model checking parameters:
- Threads: 3 (sufficient to expose races)
- Epochs: 5 (demonstrates advancement)
- Nodes: 4 (sufficient to test reclamation)
