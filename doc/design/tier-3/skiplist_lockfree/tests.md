# skiplist_lockfree — Test Specification

## Test Categories

### Unit Tests

#### Basic Operations

| Test ID | Description | Validation |
|---------|-------------|------------|
| `test_create_destroy` | Create/destroy empty skiplist | No memory leaks |
| `test_insert_single` | Insert single element | Search returns it |
| `test_insert_multiple` | Insert 1000 elements | All searchable |
| `test_insert_duplicate` | Insert same key twice | Returns EXISTS |
| `test_insert_replace` | Insert with replace=true | Value updated |
| `test_delete_existing` | Delete existing key | Returns true |
| `test_delete_missing` | Delete non-existent key | Returns false |
| `test_search_existing` | Search existing key | Returns true, value |
| `test_search_missing` | Search non-existent key | Returns false |
| `test_count_accuracy` | Verify count after ops | Matches expected |

#### Ordering Operations

| Test ID | Description | Validation |
|---------|-------------|------------|
| `test_ordering_int` | Integer key ordering | Ascending order maintained |
| `test_ordering_string` | String key ordering | Lexicographic order |
| `test_ordering_custom` | Custom comparator | Comparator order respected |
| `test_first_key` | Get smallest key | Correct key returned |
| `test_last_key` | Get largest key | Correct key returned |
| `test_first_empty` | First on empty list | Returns false |
| `test_last_empty` | Last on empty list | Returns false |

#### Floor/Ceiling Operations

| Test ID | Description | Validation |
|---------|-------------|------------|
| `test_floor_exact` | Floor of existing key | Returns that key |
| `test_floor_between` | Floor between keys | Returns smaller |
| `test_floor_below_min` | Floor below minimum | Returns false |
| `test_ceiling_exact` | Ceiling of existing key | Returns that key |
| `test_ceiling_between` | Ceiling between keys | Returns larger |
| `test_ceiling_above_max` | Ceiling above maximum | Returns false |

#### Range Iteration

| Test ID | Description | Validation |
|---------|-------------|------------|
| `test_iter_full` | Iterate all elements | All elements in order |
| `test_iter_range_bounded` | Iterate [10, 20] | Only elements in range |
| `test_iter_range_open_start` | Iterate [*, 50] | Up to bound |
| `test_iter_range_open_end` | Iterate [50, *] | From bound to end |
| `test_iter_empty_range` | Iterate [100, 50] | No elements |
| `test_iter_exclusive_end` | Iterate [10, 20) | 20 excluded |

### Concurrency Tests

#### Thread Safety

| Test ID | Threads | Operations | Validation |
|---------|---------|------------|------------|
| `test_concurrent_insert` | 8 | Insert disjoint | All keys present |
| `test_concurrent_delete` | 8 | Delete disjoint | All keys removed |
| `test_concurrent_search` | 8 | Search only | No crashes, correct results |
| `test_concurrent_mixed` | 8 | Insert/delete/search | No crashes, consistent state |
| `test_concurrent_same_key` | 8 | Insert/delete same key | One wins per round |

#### Linearizability

| Test ID | Description | Validation |
|---------|-------------|------------|
| `test_linearizable_insert_delete` | Concurrent insert/delete | History verifiable |
| `test_linearizable_search` | Search sees consistent state | No phantom reads |
| `test_linearizable_range` | Range iter weakly consistent | Valid snapshot |

```python
def test_linearizable_insert_delete():
    """
    Use a linearizability checker (e.g., Lowe's) to verify
    that concurrent insert/delete operations produce a history
    consistent with some sequential execution.
    """
    sl = SkipListMap()
    history = ConcurrentHistory()

    def worker(tid):
        for i in range(100):
            key = random.randint(0, 50)
            op = random.choice(['insert', 'delete', 'search'])

            start = history.start_op(tid, op, key)
            if op == 'insert':
                result = sl.put(key, key)
            elif op == 'delete':
                result = sl.pop(key, None) is not None
            else:
                result = key in sl
            history.end_op(start, result)

    threads = [Thread(target=worker, args=(i,)) for i in range(4)]
    [t.start() for t in threads]
    [t.join() for t in threads]

    assert linearizability_check(history, SequentialSkipListSpec())
```

#### Stress Tests

| Test ID | Config | Duration | Validation |
|---------|--------|----------|------------|
| `test_stress_high_contention` | 16 threads, 100 keys | 10s | No deadlock, no crash |
| `test_stress_memory_pressure` | Insert/delete 1M keys | Until stable | Memory bounded |
| `test_stress_iterator_concurrent` | Iterate during mutations | 10s | No crash, valid results |

### Memory Safety Tests

#### ASAN Tests

| Test ID | Description | Expected |
|---------|-------------|----------|
| `test_asan_insert_delete` | Insert then delete all | No use-after-free |
| `test_asan_concurrent` | Concurrent ops | No races detected |
| `test_asan_iterator` | Iterator during delete | No use-after-free |

#### TSAN Tests

| Test ID | Description | Expected |
|---------|-------------|----------|
| `test_tsan_concurrent_insert` | Parallel inserts | No data races |
| `test_tsan_concurrent_delete` | Parallel deletes | No data races |
| `test_tsan_concurrent_mixed` | Mixed operations | No data races |

#### Memory Leak Tests

| Test ID | Description | Expected |
|---------|-------------|----------|
| `test_leak_basic` | Create/populate/destroy | Zero leaks |
| `test_leak_exception` | Python exception during op | Zero leaks |
| `test_leak_concurrent` | Concurrent stress | Zero leaks |

### Reference Counting Tests

| Test ID | Description | Validation |
|---------|-------------|------------|
| `test_refcount_insert` | Insert increases refcount | INCREF verified |
| `test_refcount_delete` | Delete decreases refcount | DECREF after SMR |
| `test_refcount_replace` | Replace updates refcount | Old DECREF, new INCREF |
| `test_refcount_search` | Search increments result | Caller owns reference |
| `test_refcount_iter` | Iterator increments items | Each item properly owned |

```python
def test_refcount_insert():
    sl = SkipListMap()
    key = object()
    value = object()

    initial_key_refcount = sys.getrefcount(key)
    initial_value_refcount = sys.getrefcount(value)

    sl[key] = value

    assert sys.getrefcount(key) == initial_key_refcount + 1
    assert sys.getrefcount(value) == initial_value_refcount + 1

def test_refcount_delete():
    sl = SkipListMap()
    key = object()
    value = object()
    sl[key] = value

    initial_key_refcount = sys.getrefcount(key)
    initial_value_refcount = sys.getrefcount(value)

    del sl[key]

    # Force SMR epoch advancement
    smr_force_reclaim()

    assert sys.getrefcount(key) == initial_key_refcount - 1
    assert sys.getrefcount(value) == initial_value_refcount - 1
```

### Property-Based Tests

```python
from hypothesis import given, strategies as st

@given(st.lists(st.integers()))
def test_property_insert_search(keys):
    """All inserted keys are searchable."""
    sl = SkipListMap()
    for k in keys:
        sl[k] = k
    for k in set(keys):
        assert k in sl
        assert sl[k] == k

@given(st.lists(st.integers()), st.lists(st.integers()))
def test_property_delete_removes(insert_keys, delete_keys):
    """Deleted keys are not searchable."""
    sl = SkipListMap()
    for k in insert_keys:
        sl[k] = k
    for k in delete_keys:
        sl.pop(k, None)
    for k in delete_keys:
        if k not in insert_keys or insert_keys.count(k) <= delete_keys.count(k):
            assert k not in sl

@given(st.lists(st.integers()))
def test_property_ordering_maintained(keys):
    """Iteration yields keys in sorted order."""
    sl = SkipListMap()
    for k in keys:
        sl[k] = k
    result = list(sl.keys())
    assert result == sorted(set(keys))

@given(st.integers(), st.lists(st.integers()))
def test_property_floor_ceiling(search, keys):
    """Floor/ceiling obey mathematical definition."""
    sl = SkipListMap()
    for k in keys:
        sl[k] = k

    unique = sorted(set(keys))

    floor = sl.floor_key(search)
    if floor is not None:
        assert floor <= search
        assert floor in unique
        assert all(k > search for k in unique if k > floor)

    ceiling = sl.ceiling_key(search)
    if ceiling is not None:
        assert ceiling >= search
        assert ceiling in unique
        assert all(k < search for k in unique if k < ceiling)
```

### Performance Tests

#### Throughput Benchmarks

| Test ID | Config | Target |
|---------|--------|--------|
| `bench_insert_sequential` | 1M inserts, 1 thread | >500K ops/s |
| `bench_insert_concurrent` | 1M inserts, 8 threads | >2M ops/s |
| `bench_search_sequential` | 1M searches, 1 thread | >1M ops/s |
| `bench_search_concurrent` | 1M searches, 8 threads | >5M ops/s |
| `bench_mixed_workload` | 50% search, 25% insert, 25% delete | >1M ops/s |

#### Latency Benchmarks

| Test ID | Config | P50 Target | P99 Target |
|---------|--------|------------|------------|
| `bench_latency_insert` | 100K ops | <1μs | <10μs |
| `bench_latency_search` | 100K ops | <500ns | <5μs |
| `bench_latency_delete` | 100K ops | <1μs | <10μs |

#### Scaling Tests

| Test ID | Description | Validation |
|---------|-------------|------------|
| `bench_scaling_threads` | 1-32 threads | Near-linear for reads |
| `bench_scaling_size` | 1K-10M elements | O(log n) maintained |

### Edge Cases

| Test ID | Description | Expected |
|---------|-------------|----------|
| `test_empty_operations` | Search/delete on empty | Returns false |
| `test_single_element` | All ops on size-1 list | Correct behavior |
| `test_max_level` | Force max level nodes | Works correctly |
| `test_large_keys` | 1MB string keys | Works, may be slow |
| `test_none_value` | Insert None as value | Distinguishes from missing |
| `test_unhashable_key` | List as key | Comparator handles it |

### Comparator Tests

| Test ID | Description | Validation |
|---------|-------------|------------|
| `test_comparator_natural` | Default Python ordering | Correct for int, str, tuple |
| `test_comparator_reverse` | Reverse ordering | Descending iteration |
| `test_comparator_key_func` | key=lambda x: x.field | Extracts key properly |
| `test_comparator_custom_c` | C function pointer | Used without Python call |
| `test_comparator_exception` | Comparator raises | Exception propagated |

## Test Infrastructure

### Fixtures

```python
@pytest.fixture
def empty_skiplist():
    return SkipListMap()

@pytest.fixture
def populated_skiplist():
    sl = SkipListMap()
    for i in range(1000):
        sl[i] = f"value_{i}"
    return sl

@pytest.fixture
def smr_domain():
    domain = SMRDomain()
    yield domain
    domain.shutdown()
```

### Utilities

```python
def concurrent_run(func, num_threads, *args):
    """Run func concurrently from multiple threads."""
    threads = [Thread(target=func, args=args) for _ in range(num_threads)]
    [t.start() for t in threads]
    [t.join() for t in threads]

def verify_ordering(skiplist):
    """Verify skiplist maintains sorted order."""
    keys = list(skiplist.keys())
    for i in range(len(keys) - 1):
        assert keys[i] < keys[i + 1]
```

## Coverage Requirements

| Category | Line Coverage | Branch Coverage |
|----------|---------------|-----------------|
| Core operations | ≥95% | ≥90% |
| Error paths | ≥90% | ≥85% |
| Edge cases | ≥85% | ≥80% |
| **Overall** | **≥90%** | **≥85%** |
