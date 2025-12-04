# treiber — Specification

## Module Identity

- **Name:** `treiber`
- **Version:** 1.0.0
- **Tier:** 3 (Core Algorithms)
- **Dependencies:** `atomics`, `smr_ibr`, `mimalloc_glue`, `backoff`

## Behavioral Specification

### LIFO Guarantee

```
INVARIANT LIFO:
    pop() returns most recently pushed item not yet popped
```

### Linearization Points

| Operation | Linearization Point |
|-----------|---------------------|
| `push` | Successful CAS on top |
| `pop` (success) | Successful CAS on top |
| `pop` (empty) | Read of top = NULL |
| `elimination` | Item exchange in slot |

## Function Contracts

### treiber_create

```c
treiber_stack_t *treiber_create(smr_domain_t *smr, const treiber_config_t *config);
```

**Preconditions:**
- `smr != NULL`

**Postconditions:**
- Returns empty stack or NULL

### treiber_push

```c
void treiber_push(treiber_stack_t *stack, void *item);
```

**Preconditions:**
- `stack != NULL`
- `item != NULL`

**Postconditions:**
- Item on stack

**Progress:** Lock-free

### treiber_pop

```c
void *treiber_pop(treiber_stack_t *stack);
```

**Preconditions:**
- `stack != NULL`

**Postconditions:**
- Returns item or NULL if empty

**Progress:** Lock-free

### treiber_peek

```c
void *treiber_peek(treiber_stack_t *stack);
```

**Postconditions:**
- Returns top item without removing, or NULL
- Item reference count NOT incremented

**Progress:** Wait-free

## Invariants

```
INV-TS-1: LIFO
    Items popped in reverse push order

INV-TS-2: EliminationCorrectness
    Eliminated push/pop pairs behave as if both executed atomically

INV-TS-3: NoLostItems
    Every pushed item eventually poppable
```

## Performance

| Operation | Complexity |
|-----------|------------|
| Push | O(1) amortized |
| Pop | O(1) amortized |
| Peek | O(1) |
