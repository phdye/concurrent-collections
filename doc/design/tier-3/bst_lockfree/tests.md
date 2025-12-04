# bst_lockfree — Test Specification

## Test Categories

### Unit Tests

| Test ID | Description | Validation |
|---------|-------------|------------|
| `test_create_destroy` | Create/destroy empty tree | No leaks |
| `test_insert_single` | Insert one key | Searchable |
| `test_insert_many` | Insert 1000 keys | All searchable |
| `test_insert_duplicate` | Insert same key | Returns EXISTS |
| `test_delete_leaf` | Delete leaf node | Properly removed |
| `test_delete_cascade` | Delete causes restructure | Tree valid |
| `test_search_existing` | Search present key | Returns value |
| `test_search_missing` | Search absent key | Returns false |

### Tree Structure Tests

| Test ID | Description | Validation |
|---------|-------------|------------|
| `test_external_property` | All internals have 2 children | Invariant holds |
| `test_routing_keys` | Keys route correctly | BST property |
| `test_sentinel_untouched` | Sentinels never deleted | Always present |

### Concurrency Tests

| Test ID | Threads | Description |
|---------|---------|-------------|
| `test_concurrent_insert` | 8 | Parallel inserts |
| `test_concurrent_delete` | 8 | Parallel deletes |
| `test_concurrent_mixed` | 8 | All operations |
| `test_helping_correctness` | 8 | Verify helping completes ops |

### Linearizability Tests

```python
def test_linearizable():
    """Verify history is linearizable."""
    tree = TreeMap()
    history = ConcurrentHistory()

    def worker(tid):
        for _ in range(100):
            op = random.choice(['insert', 'delete', 'search'])
            key = random.randint(0, 20)

            start = history.start_op(tid, op, key)
            if op == 'insert':
                result = tree.put(key, key)
            elif op == 'delete':
                result = tree.pop(key, None) is not None
            else:
                result = key in tree
            history.end_op(start, result)

    run_concurrent(worker, 4)
    assert linearizability_check(history, SequentialBSTSpec())
```

### Memory Tests

| Test ID | Description |
|---------|-------------|
| `test_asan_operations` | ASAN clean under load |
| `test_tsan_concurrent` | TSAN clean |
| `test_refcount_correct` | Python refs balanced |

### Performance Tests

| Test ID | Target |
|---------|--------|
| `bench_insert_seq` | >300K ops/s |
| `bench_search_seq` | >800K ops/s |
| `bench_mixed_concurrent` | >1M ops/s (8 threads) |

## Coverage

- Line coverage: ≥90%
- Branch coverage: ≥85%
- Helping paths: ≥95% (critical for correctness)
