# skiplist_locked — Test Specification

## Test Categories

### Unit Tests

#### Basic Operations

| Test ID | Description | Validation |
|---------|-------------|------------|
| `test_create_destroy` | Create/destroy empty list | No leaks |
| `test_insert_single` | Insert single element | Searchable |
| `test_insert_multiple` | Insert 1000 elements | All present |
| `test_delete_existing` | Delete existing key | Returns true |
| `test_delete_missing` | Delete non-existent | Returns false |
| `test_search_existing` | Search existing | Returns value |
| `test_search_missing` | Search non-existent | Returns false |

#### Ordering Tests

| Test ID | Description | Validation |
|---------|-------------|------------|
| `test_ordering_maintained` | Insert random, iterate | Sorted order |
| `test_first_last` | First/last key | Correct extremes |
| `test_floor_ceiling` | Floor/ceiling operations | Mathematical correctness |

### Concurrency Tests

#### Thread Safety

| Test ID | Threads | Description | Validation |
|---------|---------|-------------|------------|
| `test_concurrent_insert` | 8 | Parallel inserts | All keys present |
| `test_concurrent_delete` | 8 | Parallel deletes | All keys removed |
| `test_concurrent_mixed` | 8 | Mixed operations | Consistent state |
| `test_search_during_modify` | 8 | Search during insert/delete | No crashes |

#### Deadlock Tests

| Test ID | Description | Validation |
|---------|-------------|------------|
| `test_no_deadlock_insert` | Concurrent inserts same keys | Completes within timeout |
| `test_no_deadlock_delete` | Concurrent deletes | Completes within timeout |
| `test_no_deadlock_mixed` | Insert + delete same keys | Completes within timeout |

```python
def test_no_deadlock_insert():
    """Verify no deadlock with concurrent inserts."""
    sl = SkipListMapLocked()
    keys = list(range(100))

    def worker():
        for _ in range(100):
            for k in random.sample(keys, len(keys)):
                sl[k] = k

    threads = [Thread(target=worker) for _ in range(8)]
    [t.start() for t in threads]

    # Should complete within 10 seconds
    for t in threads:
        t.join(timeout=10)
        assert not t.is_alive(), "Deadlock detected!"
```

### Lock Contention Tests

| Test ID | Description | Validation |
|---------|-------------|------------|
| `test_contention_rate` | Measure contention under load | Rate within bounds |
| `test_validation_failures` | Count retries | Reasonable retry count |
| `test_hot_spot` | All threads same key | No deadlock, correct result |

### Memory Tests

| Test ID | Description | Validation |
|---------|-------------|------------|
| `test_no_leaks` | Create/populate/destroy | Zero leaks |
| `test_refcount` | Insert/delete cycles | Correct refcounts |

### Performance Tests

| Test ID | Config | Target |
|---------|--------|--------|
| `bench_insert_single` | 1M inserts, 1 thread | >300K ops/s |
| `bench_insert_multi` | 1M inserts, 8 threads | >1M ops/s |
| `bench_search_single` | 1M searches | >1M ops/s |
| `bench_search_multi` | 1M searches, 8 threads | >4M ops/s |

### Comparison Tests

| Test ID | Description | Validation |
|---------|-------------|------------|
| `test_vs_lockfree_correctness` | Same operations, both variants | Same final state |
| `test_vs_lockfree_throughput` | Benchmark comparison | Document difference |

## Coverage Requirements

| Category | Line Coverage |
|----------|---------------|
| Core operations | ≥95% |
| Locking paths | ≥90% |
| **Overall** | **≥90%** |
