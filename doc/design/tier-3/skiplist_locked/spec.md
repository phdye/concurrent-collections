# skiplist_locked — Specification

## Module Identity

- **Name:** `skiplist_locked`
- **Version:** 1.0.0
- **Stability:** Stable
- **Tier:** 3 (Core Algorithms)
- **Dependencies:** `comparator`, `mimalloc_glue`

## Behavioral Specification

### Linearization Points

| Operation | Linearization Point |
|-----------|---------------------|
| `insert` (success) | Write to `pred->next[0]` while holding locks |
| `insert` (exists) | Read showing key present under lock |
| `delete` (success) | Setting `marked = true` |
| `delete` (not found) | Read showing key absent under lock |
| `search` (found) | Read of matching unmarked node |
| `search` (not found) | Read showing key absent |

### Thread Safety Model

- **Mutual Exclusion**: Modifications use hand-over-hand locking
- **Read Isolation**: Optimistic reads skip marked nodes
- **Deadlock Prevention**: Lock ordering follows traversal order

## Function Contracts

### skiplist_locked_create

```c
skiplist_locked_t *skiplist_locked_create(
    comparator_t *cmp,
    const skiplist_locked_config_t *config
);
```

**Preconditions:**
- `cmp != NULL`

**Postconditions:**
- Returns valid skiplist or `NULL` on failure
- Initially empty (`count == 0`)

**Thread Safety:** Single-threaded

### skiplist_locked_insert

```c
skiplist_locked_insert_result_t skiplist_locked_insert(
    skiplist_locked_t *sl,
    void *key,
    void *value,
    bool replace_if_exists
);
```

**Preconditions:**
- `sl != NULL`
- `key != NULL`

**Postconditions:**
- `INSERT_SUCCESS`: Key inserted, count incremented
- `INSERT_EXISTS`: Key present, no change
- `INSERT_REPLACED`: Value updated
- `INSERT_ERROR`: Allocation failed

**Thread Safety:** Blocking, may wait for locks

### skiplist_locked_delete

```c
bool skiplist_locked_delete(
    skiplist_locked_t *sl,
    void *key,
    void **old_value
);
```

**Preconditions:**
- `sl != NULL`
- `key != NULL`

**Postconditions:**
- Returns `true`: Key removed, count decremented
- Returns `false`: Key not found

**Thread Safety:** Blocking, may wait for locks

### skiplist_locked_search

```c
bool skiplist_locked_search(
    skiplist_locked_t *sl,
    void *key,
    void **value
);
```

**Preconditions:**
- `sl != NULL`
- `key != NULL`

**Postconditions:**
- Returns `true`: Key found, value returned
- Returns `false`: Key not found

**Thread Safety:** Lock-free (optimistic read)

## Invariants

```
INV-SLL-1: LockOrdering
    ∀ thread t holding locks L1, L2:
        L1.node precedes L2.node in traversal order

INV-SLL-2: MarkedNodesUnreachable
    ∀ node n: n.marked ⟹ eventually(n not reachable from head)

INV-SLL-3: OrderPreserved
    ∀ node n: n.next[0] ≠ tail ⟹ compare(n.key, n.next[0].key) < 0
```

## Error Handling

| Error | Return | Recovery |
|-------|--------|----------|
| Allocation failure | `INSERT_ERROR` | Caller retries |
| Deadlock | Impossible | Lock ordering prevents |

## Performance Contracts

### Complexity

| Operation | Expected | Worst Case |
|-----------|----------|------------|
| Insert | O(log n) | O(n) with contention |
| Delete | O(log n) | O(n) with contention |
| Search | O(log n) | O(n) |

### Blocking Behavior

| Operation | Maximum Wait |
|-----------|--------------|
| Insert | Bounded by concurrent insert/delete count |
| Delete | Same as insert |
| Search | None (lock-free) |
