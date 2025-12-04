# wcq — Specification

## Module Identity

- **Name:** `wcq`
- **Version:** 1.0.0
- **Tier:** 3 (Core Algorithms)
- **Dependencies:** `atomics`, `mimalloc_glue`

## Behavioral Specification

### Progress Guarantee

```
THEOREM WaitFreedom:
    ∀ thread t, operation op:
        op completes in ≤ O(n) steps
        where n = number of registered threads
```

### FIFO Guarantee

```
INVARIANT FIFO:
    Dequeue order matches enqueue order
```

## Function Contracts

### wcq_create

```c
wcq_t *wcq_create(size_t capacity, size_t max_threads);
```

**Preconditions:**
- `capacity > 0`
- `max_threads > 0`

**Postconditions:**
- Returns queue with announcement array

### wcq_enqueue

```c
bool wcq_enqueue(wcq_t *q, void *item);
```

**Preconditions:**
- `q != NULL`, `item != NULL`

**Postconditions:**
- Completes in O(max_threads) steps
- Returns true if enqueued, false if full

**Progress:** Wait-free

### wcq_dequeue

```c
void *wcq_dequeue(wcq_t *q);
```

**Preconditions:**
- `q != NULL`

**Postconditions:**
- Completes in O(max_threads) steps
- Returns item or NULL if empty

**Progress:** Wait-free

## Invariants

```
INV-WCQ-1: BoundedSteps
    Every operation completes in ≤ 2n + c steps

INV-WCQ-2: AnnouncementConsistency
    Announced operations eventually complete

INV-WCQ-3: HelpingCorrectness
    Helper completes operation with correct semantics
```

## Performance

| Operation | Steps | Throughput |
|-----------|-------|------------|
| Enqueue | O(n) | ~1M ops/s |
| Dequeue | O(n) | ~1M ops/s |
