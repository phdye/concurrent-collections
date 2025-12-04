# scq — Test Specification

## Unit Tests

| Test ID | Description |
|---------|-------------|
| `test_create_destroy` | Create/destroy queue |
| `test_enqueue_single` | Enqueue one item |
| `test_dequeue_single` | Dequeue one item |
| `test_fifo_order` | FIFO ordering preserved |
| `test_full_queue` | Enqueue to full returns false |
| `test_empty_queue` | Dequeue from empty returns NULL |
| `test_wraparound` | Queue works after wraparound |

## Concurrency Tests

| Test ID | Threads | Description |
|---------|---------|-------------|
| `test_spsc` | 1+1 | Single producer single consumer |
| `test_mpsc` | 4+1 | Multi producer single consumer |
| `test_spmc` | 1+4 | Single producer multi consumer |
| `test_mpmc` | 4+4 | Multi producer multi consumer |
| `test_high_contention` | 16+16 | Stress test |

### FIFO Verification

```python
def test_fifo_concurrent():
    """Verify FIFO under concurrency."""
    q = LockFreeQueue(capacity=1024)
    enqueue_order = []
    dequeue_order = []
    lock = threading.Lock()

    def producer(tid):
        for i in range(100):
            item = (tid, i)
            q.put(item)
            with lock:
                enqueue_order.append(item)

    def consumer():
        while True:
            item = q.get_nowait()
            if item is None:
                break
            with lock:
                dequeue_order.append(item)

    # Run producers
    producers = [Thread(target=producer, args=(i,)) for i in range(4)]
    [p.start() for p in producers]
    [p.join() for p in producers]

    # Drain queue
    while q.get_nowait() is not None:
        pass

    # Verify per-producer FIFO
    for tid in range(4):
        tid_items = [(t, i) for t, i in dequeue_order if t == tid]
        assert tid_items == sorted(tid_items, key=lambda x: x[1])
```

## Memory Tests

| Test ID | Description |
|---------|-------------|
| `test_asan_operations` | No memory errors |
| `test_tsan_concurrent` | No data races |
| `test_no_leaks` | No memory leaks |

## Performance Tests

| Test ID | Target |
|---------|--------|
| `bench_spsc` | >5M ops/s |
| `bench_mpmc_4x4` | >2M ops/s |
| `bench_latency` | P99 < 10μs |

## Coverage

- Line: ≥90%
- FIFO paths: 100%
