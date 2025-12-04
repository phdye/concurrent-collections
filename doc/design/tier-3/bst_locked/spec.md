# bst_locked — Specification

## Module Identity

- **Name:** `bst_locked`
- **Version:** 1.0.0
- **Tier:** 3 (Core Algorithms)
- **Dependencies:** `comparator`, `mimalloc_glue`

## Function Contracts

### bst_locked_create

```c
bst_locked_t *bst_locked_create(comparator_t *cmp);
```

**Preconditions:** `cmp != NULL`
**Postconditions:** Returns empty BST or NULL

### bst_locked_insert

```c
bool bst_locked_insert(bst_locked_t *tree, void *key, void *value);
```

**Preconditions:** `tree != NULL`, `key != NULL`
**Postconditions:** Returns true if inserted, false if exists
**Thread Safety:** Blocking

### bst_locked_delete

```c
bool bst_locked_delete(bst_locked_t *tree, void *key, void **old_value);
```

**Preconditions:** `tree != NULL`, `key != NULL`
**Postconditions:** Returns true if deleted
**Thread Safety:** Blocking

### bst_locked_search

```c
bool bst_locked_search(bst_locked_t *tree, void *key, void **value);
```

**Preconditions:** `tree != NULL`, `key != NULL`
**Postconditions:** Returns true if found
**Thread Safety:** Lock-free (optimistic)

## Invariants

```
INV-1: BSTProperty
    ∀ node n: left(n).key < n.key < right(n).key

INV-2: LockOrdering
    Locks acquired in traversal order (root to leaf)

INV-3: MarkedUnreachable
    Marked nodes eventually removed from tree
```

## Performance

| Operation | Complexity |
|-----------|------------|
| Insert | O(log n) expected |
| Delete | O(log n) expected |
| Search | O(log n) expected |
