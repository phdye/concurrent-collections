# smr_debra — Test Coverage

## Overview

Testing strategy validates DEBRA+ correctness, focusing on neutralization safety, signal handling, and operation restart semantics.

## Test Categories

### Unit Tests — Initialization

| Test | Covers | Status |
|------|--------|--------|
| `test_init_succeeds` | `debra_init` returns 0 | ⬜ |
| `test_init_installs_signal_handler` | Signal handler installed | ⬜ |
| `test_init_preserves_previous_handler` | Previous handler saved | ⬜ |
| `test_shutdown_restores_handler` | Previous handler restored | ⬜ |
| `test_shutdown_succeeds` | `debra_shutdown` completes | ⬜ |

Legend: ⬜ Not implemented, 🔶 Partial, ✅ Complete

### Unit Tests — Thread Registration

| Test | Covers | Status |
|------|--------|--------|
| `test_register_stores_thread_handle` | pthread_t stored | ⬜ |
| `test_register_returns_valid_state` | Non-NULL return | ⬜ |
| `test_unregister_clears_handle` | Handle invalidated | ⬜ |
| `test_register_max_threads` | MAX_THREADS registrations | ⬜ |

### Unit Tests — Critical Section

| Test | Covers | Status |
|------|--------|--------|
| `test_enter_returns_true_normally` | Normal entry succeeds | ⬜ |
| `test_enter_sets_checkpoint_valid` | Checkpoint flag set | ⬜ |
| `test_enter_establishes_checkpoint` | sigsetjmp called | ⬜ |
| `test_exit_clears_checkpoint_valid` | Checkpoint flag cleared | ⬜ |
| `test_enter_exit_pair` | Normal enter/exit works | ⬜ |

### Unit Tests — Neutralization Flag

| Test | Covers | Status |
|------|--------|--------|
| `test_was_neutralized_initially_false` | Flag starts false | ⬜ |
| `test_was_neutralized_after_neutralize` | Flag true after signal | ⬜ |
| `test_clear_neutralized` | Flag cleared properly | ⬜ |
| `test_neutralized_flag_survives_exit` | Flag preserved after exit | ⬜ |

### Unit Tests — Retirement

| Test | Covers | Status |
|------|--------|--------|
| `test_retire_same_as_ibr` | Retirement works like IBR | ⬜ |
| `test_retire_triggers_poll` | Poll at threshold | ⬜ |
| `test_poll_triggers_neutralization` | Neutralization on stall | ⬜ |

### Signal Tests — Handler

| Test | Covers | Status |
|------|--------|--------|
| `test_signal_handler_installed` | SIGURG handler active | ⬜ |
| `test_signal_ignored_outside_cs` | Signal outside CS is no-op | ⬜ |
| `test_signal_inside_cs_jumps` | Signal causes longjmp | ⬜ |
| `test_signal_sets_neutralized` | Flag set by handler | ⬜ |
| `test_signal_clears_active` | Active flag cleared | ⬜ |
| `test_multiple_signals_safe` | Repeated signals handled | ⬜ |

### Signal Tests — Async Safety

| Test | Covers | Status |
|------|--------|--------|
| `test_handler_async_signal_safe` | Only safe operations | ⬜ |
| `test_handler_no_malloc` | No heap allocation | ⬜ |
| `test_handler_no_locks` | No mutex operations | ⬜ |
| `test_signal_during_atomic_op` | Signal mid-CAS is safe | ⬜ |

### Neutralization Tests — Detection

| Test | Covers | Status |
|------|--------|--------|
| `test_stall_detection_threshold` | Stall after N epochs | ⬜ |
| `test_stall_detection_active_only` | Only active threads | ⬜ |
| `test_stall_not_detected_early` | No false positives | ⬜ |
| `test_neutralize_returns_true` | Success return | ⬜ |
| `test_neutralize_increments_count` | Stats updated | ⬜ |

### Neutralization Tests — Effect

| Test | Covers | Status |
|------|--------|--------|
| `test_neutralized_thread_exits` | Thread exits CS | ⬜ |
| `test_neutralized_epoch_unblocked` | Safe epoch advances | ⬜ |
| `test_neutralized_can_reenter` | Thread can restart | ⬜ |
| `test_neutralized_operation_restarts` | Full restart works | ⬜ |

### Concurrency Tests — Basic

| Test | Covers | Threads | Status |
|------|--------|---------|--------|
| `test_concurrent_enter_exit` | Many threads | 8 | ⬜ |
| `test_concurrent_retire` | Parallel retirement | 8 | ⬜ |
| `test_concurrent_poll` | Parallel poll | 8 | ⬜ |
| `test_concurrent_neutralization` | Parallel neutralize | 4 | ⬜ |

### Concurrency Tests — Stall Simulation

| Test | Covers | Threads | Status |
|------|--------|---------|--------|
| `test_stalled_thread_neutralized` | Blocked thread freed | 4 | ⬜ |
| `test_stalled_thread_restarts` | Restart after stall | 4 | ⬜ |
| `test_multiple_stalled_threads` | Several stalls | 8 | ⬜ |
| `test_cascading_neutralization` | Chain of stalls | 8 | ⬜ |

### Concurrency Tests — Stress

| Test | Covers | Threads | Duration | Status |
|------|--------|---------|----------|--------|
| `test_stress_neutralization` | Heavy signal load | 16 | 10s | ⬜ |
| `test_stress_memory_bound` | O(TR) bound held | 16 | 30s | ⬜ |
| `test_stress_mixed_stalls` | Some threads stall | 32 | 30s | ⬜ |
| `test_stress_rapid_restart` | Fast neutralize/restart | 8 | 10s | ⬜ |

### Operation Restart Tests

| Test | Covers | Status |
|------|--------|--------|
| `test_read_restart_gets_current` | Re-read after neutralize | ⬜ |
| `test_write_restart_succeeds` | Retry after neutralize | ⬜ |
| `test_delete_restart_succeeds` | Retry delete | ⬜ |
| `test_restart_loop_terminates` | No infinite restart | ⬜ |
| `test_restart_pattern_idempotent` | Safe to retry | ⬜ |

### Integration Tests — Data Structures

| Test | Covers | Status |
|------|--------|--------|
| `test_skiplist_with_debra` | SkipListMap uses DEBRA+ | ⬜ |
| `test_skiplist_neutralize_during_get` | Get restart works | ⬜ |
| `test_skiplist_neutralize_during_put` | Put restart works | ⬜ |
| `test_bst_with_debra` | TreeMap uses DEBRA+ | ⬜ |
| `test_queue_with_debra` | Queue uses DEBRA+ | ⬜ |

### Memory Tests

| Test | Covers | Status |
|------|--------|--------|
| `test_no_leak_with_neutralization` | Neutralize doesn't leak | ⬜ |
| `test_memory_bound_otr` | O(TR) bound verified | ⬜ |
| `test_memory_bound_better_than_ibr` | Tighter than IBR | ⬜ |
| `test_asan_no_uaf` | ASAN: no use-after-free | ⬜ |
| `test_asan_no_double_free` | ASAN: no double-free | ⬜ |

### Performance Tests

| Test | Metric | Target | Status |
|------|--------|--------|--------|
| `perf_enter_latency` | ns/enter | < 30ns | ⬜ |
| `perf_exit_latency` | ns/exit | < 15ns | ⬜ |
| `perf_neutralization_latency` | us/neutralize | < 100us | ⬜ |
| `perf_signal_delivery` | us/signal | < 10us | ⬜ |
| `perf_restart_overhead` | ns/restart | < 1us | ⬜ |
| `perf_vs_ibr_no_stalls` | ratio | < 1.5x | ⬜ |

### Platform Tests

| Platform | Neutralization | Tests | Status |
|----------|----------------|-------|--------|
| Linux x86-64 | Supported | All | ⬜ |
| Linux ARM64 | Supported | All | ⬜ |
| macOS x86-64 | Supported | All | ⬜ |
| macOS ARM64 | Supported | All | ⬜ |
| Windows x86-64 | Fallback (IBR) | Subset | ⬜ |

### Windows Fallback Tests

| Test | Covers | Status |
|------|--------|--------|
| `test_windows_no_neutralization` | Feature disabled | ⬜ |
| `test_windows_ibr_fallback` | IBR behavior used | ⬜ |
| `test_windows_enter_always_true` | Enter never fails | ⬜ |
| `test_windows_memory_bound_t2r` | O(T²R) bound | ⬜ |

### Edge Cases

| Case | Expected Behavior | Test |
|------|-------------------|------|
| Signal during sigsetjmp | Handled correctly | `test_signal_during_setjmp` |
| Signal during siglongjmp | Safe (async-signal-safe) | `test_signal_during_longjmp` |
| Thread exits during neutralize | pthread_kill returns ESRCH | `test_neutralize_exited_thread` |
| Nested enter attempt | Undefined (document) | N/A |
| Signal with invalid checkpoint | Ignored | `test_signal_invalid_checkpoint` |
| Rapid enter/exit/signal | All handled | `test_rapid_signal_storm` |

### Error Path Tests

| Error Condition | Expected Result | Test |
|-----------------|-----------------|------|
| Signal handler install fails | Init returns -1 | `test_init_handler_fail` |
| pthread_kill fails | Returns error, continues | `test_neutralize_kill_fail` |
| Thread unregisters during signal | Race handled | `test_unregister_during_signal` |

## Test Infrastructure

### Stall Simulation

```python
def simulate_stall(duration_seconds):
    """Simulate a stalled thread."""
    import time
    import ctypes

    # Prevent Python from handling signals
    ctypes.CDLL(None).pthread_sigmask(...)  # Block SIGURG briefly

    # Simulate blocking operation
    time.sleep(duration_seconds)

    # Re-enable signals
    ctypes.CDLL(None).pthread_sigmask(...)  # Unblock
```

### Signal Verification

```python
import signal

def test_signal_handler_installed():
    """Verify our handler is installed."""
    debra_init()

    handler = signal.getsignal(signal.SIGURG)
    # Note: C handler appears as SIG_DFL in Python
    # Need to verify via C level check

    debra_shutdown()
```

### Neutralization Test Pattern

```python
def test_neutralized_operation_restarts():
    """Test operation restart after neutralization."""
    debra_init()
    thr = debra_thread_register()

    restart_count = 0
    max_restarts = 10

    while restart_count < max_restarts:
        if not debra_enter(thr):
            restart_count += 1
            continue  # Neutralized, retry

        # Perform operation
        result = do_operation()

        if debra_was_neutralized(thr):
            debra_clear_neutralized(thr)
            debra_exit(thr)
            restart_count += 1
            continue  # Neutralized, retry

        debra_exit(thr)
        break  # Success

    assert restart_count < max_restarts, "Too many restarts"
    debra_thread_unregister(thr)
    debra_shutdown()
```

### Memory Bound Verification

```python
def test_memory_bound_otr():
    """Verify O(T × R) memory bound."""
    T = 8   # threads
    R = 64  # retire threshold
    max_pending = T * R * 3  # Theoretical max with margin

    # Create stalling threads
    stall_barrier = threading.Barrier(T // 2)

    def stalling_worker():
        thr = debra_thread_register()
        debra_enter(thr)
        stall_barrier.wait()  # All stallers sync
        time.sleep(10)  # Simulate stall
        # Will be neutralized
        debra_exit(thr)
        debra_thread_unregister(thr)

    def active_worker(pending_counts):
        thr = debra_thread_register()
        for _ in range(1000):
            if debra_enter(thr):
                for _ in range(10):
                    ptr = allocate_node()
                    debra_retire(thr, ptr, size, free_fn)
                pending_counts.append(debra_pending_count(thr))
                debra_exit(thr)
        debra_thread_unregister(thr)

    # Start workers
    pending = []
    stallers = [Thread(target=stalling_worker) for _ in range(T // 2)]
    actives = [Thread(target=active_worker, args=(pending,)) for _ in range(T // 2)]

    for t in stallers + actives:
        t.start()
    for t in actives:
        t.join()
    for t in stallers:
        t.join()

    # Verify bound
    assert max(pending) <= max_pending, f"Exceeded O(TR) bound: {max(pending)} > {max_pending}"
```

## Test Data Generators

```python
# Stall durations to test
STALL_DURATIONS = [0.001, 0.01, 0.1, 1.0]  # seconds

# Stall patterns
STALL_PATTERNS = [
    'single',       # One thread stalls
    'half',         # Half threads stall
    'alternating',  # Threads alternate stalling
    'burst',        # All stall briefly
]

# Thread counts
THREAD_COUNTS = [2, 4, 8, 16, 32]

# Signal stress levels
SIGNAL_RATES = [1, 10, 100, 1000]  # signals/second
```

## Coverage Goals

| Category | Target | Rationale |
|----------|--------|-----------|
| Line coverage | > 95% | Core correctness |
| Branch coverage | > 90% | Edge cases |
| Signal path coverage | 100% | Critical for safety |
| Platform coverage | All POSIX + Windows fallback | Portability |

## Test Priorities

| Priority | Tests | Reason |
|----------|-------|--------|
| P0 (Critical) | Signal safety tests | Async-signal correctness |
| P0 (Critical) | Memory safety tests | No UAF with neutralization |
| P1 (High) | Operation restart tests | Correctness after neutralize |
| P1 (High) | Memory bound tests | O(TR) guarantee |
| P2 (Medium) | Performance tests | Overhead acceptable |
| P2 (Medium) | Platform tests | Portability |
| P3 (Low) | Stress tests | Edge case robustness |

## Known Limitations

| Limitation | Test Coverage | Notes |
|------------|---------------|-------|
| Windows no neutralization | Fallback tests | IBR behavior on Windows |
| Signal conflicts | Document only | SIGURG may conflict with select() |
| Nested critical sections | Not supported | Undefined behavior |
| Real-time signals | Not tested | Not used |
