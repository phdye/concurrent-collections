# bst_locked — Test Specification

## Unit Tests

| Test ID | Description |
|---------|-------------|
| `test_create_destroy` | Create/destroy empty tree |
| `test_insert_single` | Insert one element |
| `test_insert_many` | Insert 1000 elements |
| `test_delete_leaf` | Delete leaf node |
| `test_delete_one_child` | Delete node with one child |
| `test_delete_two_children` | Delete node with two children |
| `test_search_hit` | Search existing key |
| `test_search_miss` | Search non-existent key |

## Concurrency Tests

| Test ID | Threads | Description |
|---------|---------|-------------|
| `test_concurrent_insert` | 8 | Parallel inserts |
| `test_concurrent_delete` | 8 | Parallel deletes |
| `test_concurrent_mixed` | 8 | Mixed operations |
| `test_no_deadlock` | 8 | Complete within timeout |

## Memory Tests

| Test ID | Description |
|---------|-------------|
| `test_no_leaks` | No memory leaks |
| `test_refcount` | Python refs correct |

## Performance Tests

| Test ID | Target |
|---------|--------|
| `bench_insert` | >200K ops/s |
| `bench_search` | >500K ops/s |

## Coverage

- Line: ≥90%
- Branch: ≥85%
