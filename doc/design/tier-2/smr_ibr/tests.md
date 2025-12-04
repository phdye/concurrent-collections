# smr_ibr — Test Coverage

## Overview

Testing strategy validates the correctness of IBR safe memory reclamation, focusing on safety properties (no use-after-free, no double-free) and liveness (eventual reclamation).

## Test Categories

### Unit Tests — Initialization

| Test | Covers | Status |
|------|--------|--------|
| `test_init_succeeds` | `smr_init` returns 0 | ⬜ |
| `test_init_sets_epoch_to_1` | Global epoch starts at 1 | ⬜ |
| `test_init_all_slots_inactive` | All thread slots inactive after init | ⬜ |
| `test_shutdown_succeeds` | `smr_shutdown` completes | ⬜ |

Legend: ⬜ Not implemented, 🔶 Partial, ✅ Complete

### Unit Tests — Thread Registration

| Test | Covers | Status |
|------|--------|--------|
| `test_register_returns_valid_state` | Registration returns non-NULL | ⬜ |
| `test_register_assigns_unique_id` | Each thread gets unique slot | ⬜ |
| `test_register_max_threads` | MAX_THREADS registrations succeed | ⬜ |
| `test_register_over_max_returns_null` | MAX_THREADS+1 returns NULL | ⬜ |
| `test_unregister_frees_slot` | Slot available after unregister | ⬜ |
| `test_register_reuses_freed_slot` | Freed slot can be reused | ⬜ |

### Unit Tests — Critical Section

| Test | Covers | Status |
|------|--------|--------|
| `test_enter_marks_active` | `smr_enter` sets active flag | ⬜ |
| `test_enter_captures_epoch` | `smr_enter` captures current global epoch | ⬜ |
| `test_exit_clears_active` | `smr_exit` clears active flag | ⬜ |
| `test_enter_exit_pair` | Enter/exit sequence works | ⬜ |
| `test_multiple_enter_exit_cycles` | Repeated enter/exit works | ⬜ |

### Unit Tests — Retirement

| Test | Covers | Status |
|------|--------|--------|
| `test_retire_adds_to_limbo` | Node added to limbo list | ⬜ |
| `test_retire_increments_count` | `retire_count` increments | ⬜ |
| `test_retire_epoch_indexed` | Node goes to epoch % 3 list | ⬜ |
| `test_retire_triggers_poll_at_threshold` | Poll called at threshold | ⬜ |
| `test_retire_multiple_nodes` | Many nodes can be retired | ⬜ |

### Unit Tests — Reclamation

| Test | Covers | Status |
|------|--------|--------|
| `test_poll_frees_old_nodes` | Nodes from old epochs freed | ⬜ |
| `test_poll_keeps_recent_nodes` | Current epoch nodes kept | ⬜ |
| `test_poll_decrements_count` | `retire_count` decremented on free | ⬜ |
| `test_poll_empty_is_noop` | Poll with no nodes is safe | ⬜ |
| `test_compute_safe_epoch_no_active` | Safe epoch = global when no active threads | ⬜ |
| `test_compute_safe_epoch_with_active` | Safe epoch = min of active epochs | ⬜ |

### Unit Tests — Epoch Advancement

| Test | Covers | Status |
|------|--------|--------|
| `test_epoch_advances` | Global epoch increases | ⬜ |
| `test_epoch_advances_only_when_safe` | Epoch blocked by old thread | ⬜ |
| `test_epoch_cas_prevents_duplicate` | Only one advance per epoch | ⬜ |

### Concurrency Tests — Basic

| Test | Covers | Threads | Status |
|------|--------|---------|--------|
| `test_concurrent_register` | Many threads register | 8 | ⬜ |
| `test_concurrent_enter_exit` | Many threads enter/exit | 8 | ⬜ |
| `test_concurrent_retire` | Many threads retire nodes | 8 | ⬜ |
| `test_concurrent_poll` | Many threads poll | 8 | ⬜ |

### Concurrency Tests — Safety Properties

| Test | Covers | Threads | Status |
|------|--------|---------|--------|
| `test_no_use_after_free` | ASAN: freed node not accessed | 8 | ⬜ |
| `test_no_double_free` | ASAN: node freed exactly once | 8 | ⬜ |
| `test_stalled_thread_blocks_reclaim` | Old epoch blocks freeing | 4 | ⬜ |
| `test_stalled_thread_detection` | Stall detection works | 2 | ⬜ |

### Concurrency Tests — Stress

| Test | Covers | Threads | Duration | Status |
|------|--------|---------|----------|--------|
| `test_stress_high_churn` | Rapid enter/exit/retire | 16 | 10s | ⬜ |
| `test_stress_memory_bound` | Memory stays bounded | 16 | 30s | ⬜ |
| `test_stress_epoch_overflow` | Epoch approaches UINT64_MAX | 8 | 60s | ⬜ |
| `test_stress_mixed_workload` | Readers and writers mixed | 32 | 30s | ⬜ |

### Integration Tests — Data Structures

| Test | Covers | Status |
|------|--------|--------|
| `test_skiplist_with_smr` | SkipListMap uses SMR correctly | ⬜ |
| `test_skiplist_delete_retire` | Deleted nodes retired | ⬜ |
| `test_skiplist_concurrent_access` | Concurrent reads during delete | ⬜ |
| `test_bst_with_smr` | TreeMap uses SMR correctly | ⬜ |
| `test_queue_with_smr` | Queue nodes retired properly | ⬜ |

### Integration Tests — Python GIL Interaction

| Test | Covers | Status |
|------|--------|--------|
| `test_smr_with_gil` | Works with GIL enabled | ⬜ |
| `test_smr_without_gil` | Works with free-threaded Python | ⬜ |
| `test_smr_python_refcount` | Py_DECREF called in free callback | ⬜ |
| `test_smr_python_objects` | Python objects properly released | ⬜ |

### Memory Tests

| Test | Covers | Status |
|------|--------|--------|
| `test_no_leak_simple` | Basic retire/free doesn't leak | ⬜ |
| `test_no_leak_stress` | Long-running test doesn't leak | ⬜ |
| `test_asan_use_after_free` | ASAN catches UAF (negative test) | ⬜ |
| `test_asan_double_free` | ASAN catches double-free (negative test) | ⬜ |
| `test_memory_bound_held` | Pending nodes ≤ 3 × T × R | ⬜ |
| `test_thread_cleanup_frees` | Unregister frees pending nodes | ⬜ |

### Performance Tests

| Test | Metric | Target | Status |
|------|--------|--------|--------|
| `perf_enter_latency` | ns/enter | < 20ns | ⬜ |
| `perf_exit_latency` | ns/exit | < 15ns | ⬜ |
| `perf_retire_latency` | ns/retire | < 50ns | ⬜ |
| `perf_poll_latency_empty` | ns/poll | < 20ns | ⬜ |
| `perf_poll_latency_with_nodes` | ns/node freed | < 100ns | ⬜ |
| `perf_epoch_advance_latency` | ns/advance | < 100ns | ⬜ |
| `perf_safe_epoch_scan` | ns/thread scanned | < 10ns | ⬜ |
| `perf_throughput` | retires/sec | > 10M | ⬜ |

### Edge Cases

| Case | Expected Behavior | Test |
|------|-------------------|------|
| Retire at threshold - 1 | No poll triggered | `test_retire_below_threshold` |
| Retire at exactly threshold | Poll triggered | `test_retire_at_threshold` |
| All threads exit simultaneously | Epoch advances | `test_all_threads_exit` |
| Single thread only | Epoch still advances | `test_single_thread_mode` |
| Zero active threads | Safe epoch = global epoch | `test_no_active_threads` |
| Thread unregister with pending | Nodes transferred or freed | `test_unregister_pending` |
| Rapid register/unregister | Slots properly managed | `test_slot_churn` |

### Error Path Tests

| Error Condition | Expected Result | Test |
|-----------------|-----------------|------|
| Register with no slots | Returns NULL | `test_register_full` |
| Init already initialized | Undefined (document) | N/A |
| Enter while active | Undefined (assert) | N/A |
| Exit while inactive | Undefined (assert) | N/A |
| Retire NULL | Undefined (assert) | N/A |

### Platform Tests

| Platform | Required Tests | Status |
|----------|----------------|--------|
| Linux x86-64 | All | ⬜ |
| Linux ARM64 | All | ⬜ |
| macOS x86-64 | All | ⬜ |
| macOS ARM64 | All | ⬜ |
| Windows x86-64 | All | ⬜ |

## Test Infrastructure

### Test Harness

```python
@pytest.fixture
def smr_context():
    """Initialize SMR for test, cleanup after."""
    smr_init()
    yield
    smr_shutdown()

@pytest.fixture
def thread_context(smr_context):
    """Register thread, unregister after."""
    thr = smr_thread_register()
    yield thr
    smr_thread_unregister(thr)
```

### Concurrency Test Pattern

```python
def test_concurrent_retire():
    barrier = threading.Barrier(8)
    errors = []

    def worker():
        thr = smr_thread_register()
        barrier.wait()  # Synchronize start

        for _ in range(1000):
            smr_enter(thr)
            ptr = allocate_node()
            smr_retire(thr, ptr, sizeof_node, free_node)
            smr_exit(thr)

        smr_thread_unregister(thr)

    threads = [Thread(target=worker) for _ in range(8)]
    for t in threads:
        t.start()
    for t in threads:
        t.join()

    assert not errors
```

### ASAN Integration

```bash
# Build with ASAN
CFLAGS="-fsanitize=address -fno-omit-frame-pointer" python setup.py build

# Run tests
ASAN_OPTIONS="detect_leaks=1:halt_on_error=1" pytest tests/test_smr_ibr.py
```

### Memory Bound Verification

```python
def test_memory_bound_held():
    """Verify pending memory stays within O(T × R)."""
    T = 8  # threads
    R = 64  # retire threshold
    max_pending = 3 * T * R  # Theoretical maximum

    pending_counts = []

    def worker():
        thr = smr_thread_register()
        for _ in range(10000):
            smr_enter(thr)
            # Retire some nodes
            for _ in range(random.randint(1, 10)):
                ptr = allocate_node()
                smr_retire(thr, ptr, sizeof_node, free_node)
            pending_counts.append(smr_pending_count(thr))
            smr_exit(thr)
        smr_thread_unregister(thr)

    # Run workers
    threads = [Thread(target=worker) for _ in range(T)]
    for t in threads:
        t.start()
    for t in threads:
        t.join()

    # Verify bound
    assert max(pending_counts) <= max_pending
```

## Test Data Generators

```python
# Retirement patterns
RETIRE_PATTERNS = [
    'single',       # One node at a time
    'batch',        # Threshold nodes at once
    'burst',        # Many nodes rapidly
    'periodic',     # Regular intervals
    'random',       # Random timing
]

# Thread counts for scaling tests
THREAD_COUNTS = [1, 2, 4, 8, 16, 32]

# Workload durations
DURATIONS = [1, 5, 10, 30, 60]  # seconds
```

## Coverage Goals

| Category | Target | Rationale |
|----------|--------|-----------|
| Line coverage | > 95% | Core correctness |
| Branch coverage | > 90% | Edge cases |
| Concurrency coverage | All paths | Race conditions |
| Platform coverage | All 5 platforms | Portability |

## Test Priorities

| Priority | Tests | Reason |
|----------|-------|--------|
| P0 (Critical) | Safety property tests | Core correctness |
| P0 (Critical) | Memory tests (ASAN) | Use-after-free prevention |
| P1 (High) | Concurrency stress | Real-world scenarios |
| P1 (High) | Integration tests | End-to-end validation |
| P2 (Medium) | Performance tests | Overhead monitoring |
| P2 (Medium) | Edge case tests | Completeness |
| P3 (Low) | Platform tests | Portability verification |
