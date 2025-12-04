# wcq — Test Specification

## Unit Tests

| Test ID | Description |
|---------|-------------|
| `test_create_destroy` | Create/destroy queue |
| `test_basic_ops` | Enqueue/dequeue |
| `test_fifo` | FIFO ordering |
| `test_full_queue` | Handle full queue |
| `test_empty_queue` | Handle empty queue |

## Wait-Freedom Verification

| Test ID | Description |
|---------|-------------|
| `test_bounded_steps` | Verify O(n) step bound |
| `test_no_starvation` | All threads complete |
| `test_worst_case` | Intentionally slow threads |

```python
def test_bounded_steps():
    """Verify wait-free step bound."""
    q = WaitFreeQueue(capacity=100, max_threads=8)
    profiler = WCQProfiler(expected_step_bound=20)

    def worker():
        for _ in range(100):
            with profiler.profile_enqueue() as ctx:
                q.put(object())
            with profiler.profile_dequeue() as ctx:
                q.get_nowait()

    threads = [Thread(target=worker) for _ in range(8)]
    [t.start() for t in threads]
    [t.join() for t in threads]

    verification = profiler.verify_wait_freedom(thread_count=8)
    assert verification['is_wait_free'], verification['issues']
```

## Concurrency Tests

| Test ID | Threads | Description |
|---------|---------|-------------|
| `test_concurrent_ops` | 8 | Mixed operations |
| `test_helping` | 8 | Verify helping mechanism |
| `test_high_thread_count` | 32 | Scale to many threads |

## Performance Tests

| Test ID | Target |
|---------|--------|
| `bench_throughput` | >500K ops/s |
| `bench_latency_max` | <100μs worst case |

## Coverage

- Line: ≥90%
- Helping paths: 100%
