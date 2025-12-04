# skiplist_lockfree — Specification

## Module Identity

- **Name:** `skiplist_lockfree`
- **Version:** 1.0.0
- **Stability:** Stable
- **Tier:** 3 (Core Algorithms)
- **Dependencies:** `atomics`, `comparator`, `smr_ibr` or `smr_debra`, `mimalloc_glue`

## Behavioral Specification

### Linearization Points

| Operation | Linearization Point |
|-----------|---------------------|
| `insert` (success) | Successful CAS on `pred->next[0]` |
| `insert` (exists) | Read showing key present |
| `delete` (success) | Successful CAS marking `node->next[0]` |
| `delete` (not found) | Read showing key absent |
| `search` (found) | Read of matching node at level 0 |
| `search` (not found) | Read showing key absent |

### Ordering Guarantees

```
INVARIANT SkipListOrdering:
    ∀ node ∈ Nodes:
        node.next[0] ≠ tail ⟹ compare(node.key, node.next[0].key) < 0
```

### Concurrent Semantics

1. **Isolation**: No operation observes partially-constructed nodes
2. **Atomicity**: Each operation appears atomic at its linearization point
3. **Progress**: At least one concurrent operation completes (lock-freedom)

## Function Contracts

### skiplist_create

```c
skiplist_t *skiplist_create(
    comparator_t *cmp,
    smr_domain_t *smr,
    const skiplist_config_t *config
);
```

**Preconditions:**
- `cmp != NULL`
- `smr != NULL`
- `config == NULL` or valid configuration

**Postconditions:**
- Returns valid skiplist or `NULL` on allocation failure
- Skiplist initially empty (`count == 0`)
- Head and tail sentinels initialized

**Thread Safety:** Single-threaded (call from main thread)

### skiplist_destroy

```c
void skiplist_destroy(skiplist_t *sl);
```

**Preconditions:**
- `sl != NULL`
- No concurrent operations in progress

**Postconditions:**
- All nodes freed
- All Python references decremented
- Skiplist memory freed

**Thread Safety:** Single-threaded

### skiplist_insert

```c
skiplist_insert_result_t skiplist_insert(
    skiplist_t *sl,
    void *key,
    void *value,
    bool replace_if_exists
);
```

**Preconditions:**
- `sl != NULL`
- `key != NULL`
- `value` may be `NULL` for set operations

**Postconditions:**
- `INSERT_SUCCESS`: Key-value inserted, `count` incremented
- `INSERT_EXISTS`: Key already present, state unchanged
- `INSERT_REPLACED`: Value replaced, `count` unchanged
- `INSERT_ERROR`: Allocation failed, state unchanged

**Thread Safety:** Lock-free, may be called concurrently

**Memory:** Increments refcount on `key` and `value` on success

### skiplist_delete

```c
bool skiplist_delete(
    skiplist_t *sl,
    void *key,
    void **old_value
);
```

**Preconditions:**
- `sl != NULL`
- `key != NULL`

**Postconditions:**
- Returns `true`: Node marked and retired, `count` decremented
- Returns `false`: Key not found, state unchanged
- If `old_value != NULL` and returns `true`: `*old_value` set with incremented refcount

**Thread Safety:** Lock-free, may be called concurrently

**Memory:** Old node retired to SMR domain

### skiplist_search

```c
bool skiplist_search(
    skiplist_t *sl,
    void *key,
    void **value
);
```

**Preconditions:**
- `sl != NULL`
- `key != NULL`

**Postconditions:**
- Returns `true`: Key found, `*value` set with incremented refcount
- Returns `false`: Key not found

**Thread Safety:** Wait-free, may be called concurrently

### skiplist_count

```c
size_t skiplist_count(const skiplist_t *sl);
```

**Preconditions:**
- `sl != NULL`

**Postconditions:**
- Returns approximate element count
- May be stale due to concurrent modifications

**Thread Safety:** Wait-free

### skiplist_first_key / skiplist_last_key

```c
bool skiplist_first_key(skiplist_t *sl, void **key);
bool skiplist_last_key(skiplist_t *sl, void **key);
```

**Preconditions:**
- `sl != NULL`
- `key != NULL`

**Postconditions:**
- Returns `true`: Key returned with incremented refcount
- Returns `false`: Skiplist empty

**Thread Safety:** Wait-free

### skiplist_floor_key / skiplist_ceiling_key

```c
bool skiplist_floor_key(skiplist_t *sl, void *search_key, void **result);
bool skiplist_ceiling_key(skiplist_t *sl, void *search_key, void **result);
```

**Preconditions:**
- `sl != NULL`
- `search_key != NULL`
- `result != NULL`

**Postconditions:**
- `floor_key`: Returns greatest key ≤ `search_key`
- `ceiling_key`: Returns smallest key ≥ `search_key`
- Returns `true` with incremented refcount, or `false` if no such key

**Thread Safety:** Wait-free

### skiplist_iter_range

```c
skiplist_iter_t *skiplist_iter_range(
    skiplist_t *sl,
    void *start,
    void *end,
    bool inclusive_end
);
```

**Preconditions:**
- `sl != NULL`
- `start == NULL` for unbounded start
- `end == NULL` for unbounded end

**Postconditions:**
- Returns iterator positioned at first element in range
- Iterator must be freed with `skiplist_iter_free()`

**Thread Safety:** Lock-free creation, weakly consistent iteration

### skiplist_iter_next

```c
bool skiplist_iter_next(
    skiplist_iter_t *iter,
    void **key,
    void **value
);
```

**Preconditions:**
- `iter != NULL`
- Iterator not exhausted

**Postconditions:**
- Returns `true`: `*key` and `*value` set with incremented refcounts
- Returns `false`: End of range or skiplist

**Thread Safety:** Single-threaded per iterator

**Consistency:** Weakly consistent (may observe concurrent modifications)

## Invariants

### Structural Invariants

```
INV-SL-1: SkipListOrder
    ∀ i ∈ [0, max_level):
        ∀ node: !IS_MARKED(node.next[i]) ⟹
            node.next[i] = tail ∨ compare(node.key, node.next[i].key) < 0

INV-SL-2: LevelConnectivity
    ∀ node, i: i < top_level(node) ⟹
        ∃ path from head to node using only level i

INV-SL-3: MarkedNodeReachability
    ∀ node: IS_MARKED(node.next[0]) ⟹
        node not reachable from head via unmarked path at level 0

INV-SL-4: SentinelIntegrity
    head ≠ tail ∧ !IS_MARKED(head) ∧ !IS_MARKED(tail)
```

### Safety Invariants

```
INV-SAFE-1: NoUseAfterFree
    ∀ node: Accessed(node) ⟹ !Freed(node)
    Ensured by: SMR integration

INV-SAFE-2: NoDoubleFree
    ∀ node: retire(node) called at most once
    Ensured by: Only successful marker wins deletion

INV-SAFE-3: RefCountCorrect
    ∀ node: node.key.refcount ≥ 1 while node reachable
    Ensured by: INCREF on insert, DECREF on free

INV-SAFE-4: LinearizableHistory
    ∃ total order on operations consistent with:
        - Real-time order (op1 completes before op2 starts ⟹ op1 < op2)
        - Sequential specification of skip list
```

## Error Handling

| Error | Return Value | Action |
|-------|-------------|--------|
| Allocation failure | `INSERT_ERROR` or `NULL` | Caller should retry or fail gracefully |
| Invalid comparator | Undefined behavior | Precondition violation |
| NULL skiplist | Undefined behavior | Precondition violation |

## Performance Contracts

### Complexity

| Operation | Expected | Worst Case | Notes |
|-----------|----------|------------|-------|
| Insert | O(log n) | O(n) | Worst case with adversarial input |
| Delete | O(log n) | O(n) | Same as insert |
| Search | O(log n) | O(n) | Same as insert |
| First/Last | O(1) | O(1) | Direct access |
| Floor/Ceiling | O(log n) | O(n) | Traversal-based |
| Range(k) | O(log n + k) | O(n + k) | k = result size |

### Space

- Per-node: `sizeof(void*) * (2 + avg_level)` + `sizeof(uint32_t)`
- Expected avg_level with p=0.25: 1.33
- Memory overhead: ~20 bytes per node on 64-bit

### Contention

| Scenario | Behavior |
|----------|----------|
| Read-heavy | Near-linear scaling |
| Write-heavy | CAS failures increase with threads |
| Hot spot | May cause livelock (exponential backoff mitigates) |

## Resource Management

### Python References

| Event | Action |
|-------|--------|
| Node creation | INCREF key, INCREF value |
| Node retirement | Deferred DECREF via SMR |
| Value replacement | INCREF new, DECREF old |
| Iterator next | INCREF returned key/value |

### Memory

| Event | Handler |
|-------|---------|
| Node allocation | `cc_alloc()` via mimalloc |
| Node deallocation | `cc_free()` via SMR callback |
| Iterator allocation | Standard `malloc()` |
| Iterator deallocation | Standard `free()` |

## Configuration Constraints

| Parameter | Valid Range | Default | Notes |
|-----------|-------------|---------|-------|
| max_level | 1-64 | 32 | Higher = more memory, better O(log n) |
| level_probability | 0.1-0.5 | 0.25 | 0.25 optimal for most workloads |

## Compatibility

### ABI Stability

- Opaque struct pointers: Stable
- Function signatures: Stable
- Internal structs: Unstable (may change)

### API Deprecation

- Minimum 2 minor versions warning before removal
- Deprecated functions marked with `CC_DEPRECATED`
