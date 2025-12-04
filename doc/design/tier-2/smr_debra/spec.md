# smr_debra — Specification

## Overview

Formal specification of contracts, invariants, and safety properties for DEBRA+ (Distributed Epoch-Based Reclamation with Neutralization).

## Module Contracts

### Global Initialization

```c
/**
 * @function debra_init
 * @brief Initialize the global DEBRA+ state
 *
 * @pre  DEBRA+ not already initialized
 * @post Global epoch set to 1
 * @post All thread slots marked inactive
 * @post Signal handler installed for neutralization
 *
 * @returns 0 on success, -1 on failure
 * @errors  ENOMEM if allocation fails
 * @errors  Signal handler installation failure
 */
int debra_init(void);
```

```c
/**
 * @function debra_shutdown
 * @brief Shutdown the global DEBRA+ state
 *
 * @pre  All threads have unregistered
 * @pre  All retired nodes have been reclaimed
 * @post Global state freed
 * @post Signal handler restored to previous
 *
 * @warning Calling with active threads causes undefined behavior
 */
void debra_shutdown(void);
```

### Thread Registration

```c
/**
 * @function debra_thread_register
 * @brief Register calling thread with DEBRA+
 *
 * @pre  Thread not already registered
 * @pre  Available slot exists
 * @post Thread assigned unique slot
 * @post Thread handle stored for signal delivery
 * @post Thread's retire lists initialized
 *
 * @returns Pointer to thread-local DEBRA+ state
 * @returns NULL if no slots available
 */
debra_thread_t* debra_thread_register(void);
```

```c
/**
 * @function debra_thread_unregister
 * @brief Unregister calling thread from DEBRA+
 *
 * @pre  thr != NULL
 * @pre  thr is valid (registered, not unregistered)
 * @pre  Thread is outside critical section
 * @pre  checkpoint_valid == false
 * @post Thread's slot marked available
 * @post All pending retired nodes transferred or freed
 * @post Thread handle cleared
 */
void debra_thread_unregister(debra_thread_t* thr);
```

### Critical Section

```c
/**
 * @function debra_enter
 * @brief Enter DEBRA+ critical section
 *
 * @pre  thr != NULL
 * @pre  thr is valid
 * @pre  Thread not already in critical section
 *
 * @post If returns true:
 *       - Thread marked active
 *       - Thread's epoch set to current global epoch
 *       - Checkpoint established for neutralization
 *       - checkpoint_valid == true
 *
 * @post If returns false:
 *       - Thread was neutralized via signal
 *       - Thread is NOT in critical section
 *       - Caller must retry operation
 *
 * @returns true if entered successfully
 * @returns false if neutralized (must restart operation)
 *
 * @note Caller MUST handle false return and restart
 */
bool debra_enter(debra_thread_t* thr);
```

```c
/**
 * @function debra_exit
 * @brief Exit DEBRA+ critical section
 *
 * @pre  thr != NULL
 * @pre  Thread is in critical section
 *
 * @post Thread marked inactive
 * @post checkpoint_valid == false
 * @post Thread no longer blocks reclamation
 * @post was_neutralized flag preserved (for caller to check)
 *
 * @note Thread must not access protected pointers after this call
 */
void debra_exit(debra_thread_t* thr);
```

### Neutralization Check

```c
/**
 * @function debra_was_neutralized
 * @brief Check if thread was neutralized during operation
 *
 * @pre  thr != NULL
 *
 * @returns true if thread was neutralized since last clear
 *
 * @note Call after completing operation, before using results
 * @note If true, results may be invalid - retry operation
 */
bool debra_was_neutralized(debra_thread_t* thr);
```

```c
/**
 * @function debra_clear_neutralized
 * @brief Clear the neutralization flag
 *
 * @pre  thr != NULL
 * @post was_neutralized == false
 *
 * @note Call before retrying operation
 */
void debra_clear_neutralized(debra_thread_t* thr);
```

### Node Retirement

```c
/**
 * @function debra_retire
 * @brief Retire a node for deferred reclamation
 *
 * @param thr      Thread-local DEBRA+ state
 * @param ptr      Pointer to retired node
 * @param size     Size of allocation
 * @param free_fn  Function to call when safe to free
 *
 * @pre  thr != NULL, ptr != NULL, free_fn != NULL
 * @pre  Thread is in critical section
 * @pre  Node has been logically removed
 *
 * @post Node added to limbo list
 * @post Node will be freed when safe
 *
 * @note Same contract as smr_retire (IBR)
 */
void debra_retire(debra_thread_t* thr, void* ptr, size_t size,
                  void (*free_fn)(void*, size_t));
```

### Signal Handler

```c
/**
 * @function debra_signal_handler
 * @brief Handle neutralization signal (internal)
 *
 * @pre  Signal is SIGURG (or configured signal)
 * @pre  Called asynchronously by kernel
 *
 * @post If checkpoint_valid:
 *       - thread_neutralized[id] = true
 *       - was_neutralized = true
 *       - thread_active[id] = false
 *       - longjmp to checkpoint (function does not return normally)
 *
 * @post If !checkpoint_valid:
 *       - No effect (signal ignored)
 *
 * @note This is async-signal-safe
 * @note Uses only async-signal-safe operations (atomic stores, siglongjmp)
 */
static void debra_signal_handler(int sig, siginfo_t* info, void* ctx);
```

## Invariants

### Global Invariants

| ID | Invariant | Rationale |
|----|-----------|-----------|
| G1 | `global_epoch` is monotonically increasing | Same as IBR |
| G2 | Signal handler installed during active lifetime | Required for neutralization |
| G3 | Thread handles are valid while slot is assigned | For signal delivery |
| G4 | At most one signal handler per signal number | No handler conflicts |

### Thread Invariants

| ID | Invariant | Rationale |
|----|-----------|-----------|
| T1 | `checkpoint_valid ⟹ thread_active[id]` | Checkpoint only valid in critical section |
| T2 | `thread_active[id] ⟹ checkpoint_valid` | Active threads have checkpoint |
| T3 | `was_neutralized ⟹ !checkpoint_valid` | Neutralized threads exited |
| T4 | Signal handler may fire at any point during critical section | Async nature |

### Neutralization Invariants

| ID | Invariant | Rationale |
|----|-----------|-----------|
| N1 | Neutralization only targets stalled threads (epoch lag > threshold) | Avoid false positives |
| N2 | After neutralization, thread's `thread_active` is false | Clears blocking |
| N3 | Neutralized thread's operation must be restarted | Results may be stale |
| N4 | Signal delivery is best-effort (may fail for terminated threads) | Robustness |

### Reclamation Invariants

All IBR reclamation invariants (R1-R4) apply, plus:

| ID | Invariant | Rationale |
|----|-----------|-----------|
| R5 | Neutralization may advance safe_epoch | Clears stalled blockers |
| R6 | Memory bound O(T × R) with neutralization | Stronger than IBR |

## Safety Properties

### S1: No Use-After-Free

**Property**: Same as IBR - a node is never freed while any thread may hold a reference.

**Extension for DEBRA+**: Neutralization does not violate this because:
1. Neutralized thread's `thread_active` becomes false
2. Thread no longer "holds" a reference for safe_epoch calculation
3. Thread must re-acquire reference after restart (may get different data)

### S2: No Double-Free

**Property**: Same as IBR - each node is freed exactly once.

### S3: Signal Safety

**Property**: Signal handler only uses async-signal-safe operations.

**Proof**:
1. `atomic_store` is async-signal-safe
2. `siglongjmp` is async-signal-safe
3. No memory allocation in handler
4. No mutex locks in handler
5. No I/O in handler

### S4: Checkpoint Validity

**Property**: `siglongjmp` only called when checkpoint is valid.

**Proof**:
1. `checkpoint_valid` set true only after `sigsetjmp`
2. `checkpoint_valid` set false in `debra_exit` before checkpoint invalidated
3. Signal handler checks `checkpoint_valid` before calling `siglongjmp`

### S5: Operation Restart Safety

**Property**: Restarted operations observe consistent state.

**Proof**:
1. Neutralized thread exits critical section
2. Re-enters with fresh epoch
3. All data accesses are after new enter
4. Therefore, sees consistent (possibly updated) state

## Liveness Properties

### L1: No Permanent Stall

**Property**: Stalled threads are neutralized, enabling epoch advancement.

**Formula**: `stalled(t) ∧ limbo_full ⟹ ◇neutralized(t)`

### L2: Bounded Memory

**Property**: Pending memory bounded by O(T × R).

**Proof**: Neutralization ensures no thread blocks reclamation indefinitely.

### L3: Progress

**Property**: Retired nodes are eventually freed.

**Assumption**: Neutralization signals are eventually delivered and processed.

## Memory Order Specification

### debra_enter

```
sigsetjmp                 : (setjmp semantics, memory barrier implied)
Store thread_epochs[id]   : release
Store thread_active[id]   : release
Thread fence              : seq_cst
```

### debra_exit

```
checkpoint_valid = false  : plain (single-threaded access)
Store thread_active[id]   : release
```

### debra_signal_handler

```
Store thread_neutralized[id] : release
Store thread_active[id]      : release
siglongjmp                   : (memory barrier implied)
```

### debra_try_neutralize

```
Load thread_active[id]    : acquire
Load thread_epochs[id]    : acquire
Load global_epoch         : acquire
pthread_kill              : (synchronization point)
```

## Error Handling

| Condition | Behavior |
|-----------|----------|
| `debra_init` signal handler fails | Returns -1 |
| `debra_enter` sigsetjmp fails | Undefined (should not happen) |
| `pthread_kill` fails | Returns ESRCH if thread exited, ignored |
| Nested `debra_enter` | Undefined (not supported) |
| Signal arrives outside critical section | Ignored |

## Thread Safety

| Function | Thread Safety |
|----------|---------------|
| `debra_init` | Not thread-safe (call once) |
| `debra_shutdown` | Not thread-safe (call once) |
| `debra_thread_register` | Thread-safe |
| `debra_thread_unregister` | Thread-safe (own state) |
| `debra_enter` | Thread-safe (own state) |
| `debra_exit` | Thread-safe (own state) |
| `debra_retire` | Thread-safe (thread-local lists) |
| `debra_poll` | Thread-safe |
| `debra_try_neutralize` | Thread-safe (targets other thread) |
| `debra_signal_handler` | Async-signal-safe |

## State Machine

### Thread State (Extended)

```
                  debra_thread_register()
UNREGISTERED ─────────────────────────────► REGISTERED/INACTIVE
                                                   │
                          ┌─────────────────debra_enter()──────────────────┐
                          │ (returns true)                                  │
                          ▼                                                 │
                   REGISTERED/ACTIVE ◄──────────────────────────────────────┤
                          │                                                 │
          ┌───────────────┼───────────────┐                                 │
          │               │               │                                 │
   debra_exit()    neutralized     debra_exit()                             │
          │          (signal)      (normal)                                 │
          ▼               │               │                                 │
   REGISTERED/INACTIVE    │               │                                 │
          │               ▼               │                                 │
          │        NEUTRALIZED            │                                 │
          │          (jumps to            │                                 │
          │           checkpoint)         │                                 │
          │               │               │                                 │
          │               ▼               ▼                                 │
          │        debra_enter() returns false ─────────────────────────────┘
          │                                                    (retry)
          │
          ▼
   debra_thread_unregister()
          │
          ▼
    UNREGISTERED
```

## Async-Signal-Safe Operations

The signal handler must only use these operations:

| Operation | Safe? | Used |
|-----------|-------|------|
| `atomic_store` | Yes | Yes |
| `siglongjmp` | Yes | Yes |
| `write` (for debugging) | Yes | No |
| `malloc` | No | No |
| `printf` | No | No |
| `mutex_lock` | No | No |

## Platform-Specific Behavior

### POSIX (Linux, macOS)

- Full neutralization support via signals
- SIGURG used by default
- Signal handler installed with SA_SIGINFO

### Windows

- Neutralization not supported
- Falls back to IBR behavior
- Memory bound is O(T²R) instead of O(TR)

```c
#ifdef _WIN32
bool debra_enter(debra_thread_t* thr) {
    // No checkpoint, no neutralization
    // Standard epoch entry only
    return smr_enter((smr_thread_t*)thr), true;
}
#endif
```

## Formal Verification Notes

The TLA+ specification in `spec.tla` extends IBR specification with:
- Neutralization action
- Signal delivery modeling
- Operation restart semantics

Additional properties verified:
- Signal handler does not violate memory safety
- Neutralization enables epoch advancement
- Bounded memory property

Model checking parameters:
- Threads: 3
- Nodes: 4
- Include neutralization actions
