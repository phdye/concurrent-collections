# treiber — Test Specification

## Unit Tests

| Test ID | Description |
|---------|-------------|
| `test_create_destroy` | Create/destroy stack |
| `test_push_pop_single` | Push then pop one item |
| `test_lifo_order` | LIFO ordering maintained |
| `test_pop_empty` | Pop from empty returns NULL |
| `test_peek` | Peek without removing |
| `test_many_items` | Push/pop 10000 items |

## Concurrency Tests

| Test ID | Threads | Description |
|---------|---------|-------------|
| `test_concurrent_push` | 8 | Parallel pushes |
| `test_concurrent_pop` | 8 | Parallel pops |
| `test_concurrent_mixed` | 8 | Push and pop |
| `test_high_contention` | 16 | Stress test |

### LIFO Verification

```python
def test_lifo_serial():
    """Verify strict LIFO ordering."""
    stack = LockFreeStack()

    items = list(range(100))
    for item in items:
        stack.push(item)

    popped = []
    while True:
        item = stack.pop()
        if item is None:
            break
        popped.append(item)

    assert popped == list(reversed(items))
```

## Elimination Tests

| Test ID | Description |
|---------|-------------|
| `test_elimination_enabled` | Elimination occurs under contention |
| `test_elimination_disabled` | Works without elimination |
| `test_elimination_timeout` | Handles timeout correctly |
| `test_elimination_correctness` | Eliminated pairs match |

```python
def test_elimination_effectiveness():
    """Test that elimination reduces CAS failures."""
    stack_no_elim = LockFreeStack(enable_elimination=False)
    stack_with_elim = LockFreeStack(enable_elimination=True)

    profiler_no = StackProfiler()
    profiler_with = StackProfiler()

    # Run high-contention workload
    def contention_worker(stack, profiler):
        for _ in range(1000):
            with profiler.profile_push():
                stack.push(object())
            with profiler.profile_pop():
                stack.pop()

    # Compare CAS failures
    run_concurrent(contention_worker, 8, stack_no_elim, profiler_no)
    run_concurrent(contention_worker, 8, stack_with_elim, profiler_with)

    stats_no = profiler_no.get_stats()
    stats_with = profiler_with.get_stats()

    # Elimination should reduce CAS failures
    assert stats_with.push_cas_failures < stats_no.push_cas_failures * 0.8
```

## Memory Tests

| Test ID | Description |
|---------|-------------|
| `test_asan` | No memory errors |
| `test_tsan` | No data races |
| `test_no_leaks` | All nodes freed |
| `test_smr_correctness` | Safe memory reclamation |

## Performance Tests

| Test ID | Target |
|---------|--------|
| `bench_push_seq` | >2M ops/s |
| `bench_pop_seq` | >2M ops/s |
| `bench_concurrent` | >1M ops/s (8 threads) |
| `bench_elimination` | Measure improvement |

## Coverage

- Line: ≥90%
- Elimination paths: 100%
