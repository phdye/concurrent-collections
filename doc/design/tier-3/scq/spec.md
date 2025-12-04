# scq — Specification

## Module Identity

- **Name:** `scq`
- **Version:** 1.0.0
- **Tier:** 3 (Core Algorithms)
- **Dependencies:** `atomics`, `smr_ibr`, `mimalloc_glue`

## Behavioral Specification

### FIFO Guarantee

```
INVARIANT FIFO:
    ∀ items i1, i2:
        enqueue_order(i1) < enqueue_order(i2) ⟹
        dequeue_order(i1) < dequeue_order(i2)
```

### Linearization Points

| Operation | Linearization Point |
|-----------|---------------------|
| `enqueue` (success) | Successful CAS on slot |
| `enqueue` (full) | Read showing queue full |
| `dequeue` (success) | Successful CAS consuming slot |
| `dequeue` (empty) | Read showing queue empty |

## Function Contracts

### scq_create

```c
scq_t *scq_create(size_t capacity, smr_domain_t *smr);
```

**Preconditions:**
- `capacity > 0`
- `capacity` will be rounded to power of 2

**Postconditions:**
- Returns empty queue or NULL
- Actual capacity may exceed requested

### scq_enqueue

```c
bool scq_enqueue(scq_t *q, void *item);
```

**Preconditions:**
- `q != NULL`
- `item != NULL`

**Postconditions:**
- Returns `true`: Item enqueued
- Returns `false`: Queue full

**Thread Safety:** Lock-free

### scq_dequeue

```c
void *scq_dequeue(scq_t *q);
```

**Preconditions:**
- `q != NULL`

**Postconditions:**
- Returns item or `NULL` if empty

**Thread Safety:** Lock-free

### scq_size

```c
size_t scq_size(const scq_t *q);
```

**Postconditions:**
- Returns approximate size (may be stale)

## Invariants

```
INV-SCQ-1: BoundedCapacity
    size(q) ≤ q.capacity

INV-SCQ-2: SafeBitConsistency
    Slot valid for cycle c ⟺ safe_bit matches cycle parity

INV-SCQ-3: MonotonicPositions
    head ≤ tail
```

## Performance

| Operation | Complexity |
|-----------|------------|
| Enqueue | O(1) amortized |
| Dequeue | O(1) amortized |
| Size | O(1) |

## Error Handling

| Error | Return |
|-------|--------|
| Queue full | `false` from enqueue |
| Queue empty | `NULL` from dequeue |
| OOM | `NULL` from create |
