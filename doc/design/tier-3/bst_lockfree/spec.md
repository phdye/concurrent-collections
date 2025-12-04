# bst_lockfree — Specification

## Module Identity

- **Name:** `bst_lockfree`
- **Version:** 1.0.0
- **Stability:** Stable
- **Tier:** 3 (Core Algorithms)
- **Dependencies:** `atomics`, `comparator`, `smr_ibr` or `smr_debra`, `mimalloc_glue`

## Behavioral Specification

### Linearization Points

| Operation | Linearization Point |
|-----------|---------------------|
| `insert` (success) | Successful CAS linking new internal node |
| `insert` (exists) | Read finding existing key |
| `delete` (success) | CAS setting INTENT flag |
| `delete` (not found) | Read showing key absent |
| `search` (found) | Read of matching leaf |
| `search` (not found) | Read showing key absent |

### Tree Structure Invariants

```
INV-BST-1: ExternalTreeProperty
    ∀ internal node i:
        i.left ≠ NULL ∧ i.right ≠ NULL

INV-BST-2: RoutingKeyProperty
    ∀ internal node i, leaf l in left subtree:
        compare(l.key, i.key) < 0
    ∀ internal node i, leaf l in right subtree:
        compare(l.key, i.key) ≥ 0

INV-BST-3: LeafUniqueness
    ∀ leaves l1, l2: l1 ≠ l2 ⟹ l1.key ≠ l2.key
```

## Function Contracts

### bst_create

```c
bst_t *bst_create(comparator_t *cmp, smr_domain_t *smr);
```

**Preconditions:**
- `cmp != NULL`
- `smr != NULL`

**Postconditions:**
- Returns valid BST with sentinels initialized
- Tree contains only sentinel leaves

### bst_insert

```c
bst_insert_result_t bst_insert(bst_t *tree, void *key, void *value, bool replace);
```

**Preconditions:**
- `tree != NULL`
- `key != NULL`

**Postconditions:**
- `BST_INSERT_SUCCESS`: Key-value inserted
- `BST_INSERT_EXISTS`: Key present, unchanged
- `BST_INSERT_REPLACED`: Value updated
- `BST_INSERT_ERROR`: Allocation failed

**Thread Safety:** Lock-free

### bst_delete

```c
bool bst_delete(bst_t *tree, void *key, void **old_value);
```

**Preconditions:**
- `tree != NULL`
- `key != NULL`

**Postconditions:**
- Returns `true`: Key removed, nodes retired
- Returns `false`: Key not found

**Thread Safety:** Lock-free with helping

### bst_search

```c
bool bst_search(bst_t *tree, void *key, void **value);
```

**Preconditions:**
- `tree != NULL`
- `key != NULL`

**Postconditions:**
- Returns `true`: Key found, value returned
- Returns `false`: Key not found

**Thread Safety:** Wait-free

## Safety Invariants

```
INV-SAFE-1: NoUseAfterFree
    ∀ node n: Accessed(n) ⟹ !Freed(n)

INV-SAFE-2: FlagMonotonicity
    Edge flags only progress: CLEAN → INTENT → MARKED

INV-SAFE-3: LinearizableHistory
    Operations appear atomic at linearization points
```

## Performance Contracts

### Complexity

| Operation | Expected | Worst Case |
|-----------|----------|------------|
| Insert | O(log n) | O(n) |
| Delete | O(log n) | O(n) |
| Search | O(log n) | O(n) |

### Space

- Internal node: ~40 bytes
- Leaf node: ~24 bytes
- Total overhead: ~1.5x key-value storage

## Error Handling

| Error | Return | State |
|-------|--------|-------|
| OOM | `BST_INSERT_ERROR` | Unchanged |
| Invalid key | UB | Precondition violation |
