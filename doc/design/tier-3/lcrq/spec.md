# lcrq — Specification

## Module Identity

- **Name:** `lcrq`
- **Version:** 1.0.0
- **Tier:** 3 (Core Algorithms)
- **Platform:** x86-64 only (requires CMPXCHG16B)
- **Dependencies:** `atomics`, `smr_ibr`, `mimalloc_glue`

## Availability

```c
bool lcrq_is_supported(void);  // Runtime check
```

**Compile-time:** Only available when `__x86_64__` or `_M_X64` defined.

## Function Contracts

### lcrq_create

```c
lcrq_t *lcrq_create(smr_domain_t *smr);
```

**Preconditions:**
- `lcrq_is_supported() == true`
- `smr != NULL`

**Postconditions:**
- Returns queue with initial ring, or NULL

### lcrq_enqueue

```c
bool lcrq_enqueue(lcrq_t *q, void *item);
```

**Preconditions:**
- `q != NULL`
- `item != NULL`

**Postconditions:**
- Returns `true`: Item enqueued
- Returns `false`: OOM (ring allocation failed)

**Note:** Unbounded; never returns false due to capacity.

### lcrq_dequeue

```c
void *lcrq_dequeue(lcrq_t *q);
```

**Preconditions:**
- `q != NULL`

**Postconditions:**
- Returns item or `NULL` if empty

## Invariants

```
INV-LCRQ-1: FIFO
    Dequeue order matches enqueue order

INV-LCRQ-2: RingLinking
    Rings linked head → tail, never disconnected until retired

INV-LCRQ-3: SlotCycle
    Version counter prevents ABA
```

## Performance

| Operation | Complexity | Throughput |
|-----------|------------|------------|
| Enqueue | O(1) | ~10M ops/s |
| Dequeue | O(1) | ~10M ops/s |
