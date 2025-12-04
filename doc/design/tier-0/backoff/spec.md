# backoff — Specification

## Overview

The `backoff` module guarantees bounded spinning behavior with exponential growth. It provides platform-optimized pause instructions to reduce power consumption and cache line contention during spin-wait loops.

## Invariants

1. **Bounded Iterations**: `current` never exceeds `max`
2. **Monotonic Growth**: `current` doubles on each backoff until hitting `max`
3. **Reset Correctness**: After reset, `current` equals `min`
4. **Non-Zero Iterations**: `min` and `max` are always >= 1

## Preconditions

- Backoff state must be initialized before use
- `min` <= `max`

## Contracts by Operation

### cc_backoff_init

**Signature:**
```c
void cc_backoff_init(cc_backoff_t *b, uint32_t min, uint32_t max);
```

**Description:** Initialize backoff state with specified bounds.

**Preconditions:**
- `b` is valid pointer
- `min >= 1`
- `max >= min`

**Postconditions:**
- `b->min == min`
- `b->max == max`
- `b->current == min`

**Errors:** None (undefined behavior if preconditions violated)

**Complexity:** O(1)

**Thread Safety:** Thread-unsafe (initialize before sharing)

---

### cc_backoff

**Signature:**
```c
void cc_backoff(cc_backoff_t *b);
```

**Description:** Execute backoff by spinning for `current` iterations, then double `current`.

**Preconditions:**
- `b` initialized via `cc_backoff_init` or `CC_BACKOFF_INIT`

**Postconditions:**
- Paused for `b->current` iterations (old value)
- `b->current == min(old_current * 2, b->max)`

**Errors:** None

**Complexity:** O(current) pause operations

**Thread Safety:** Thread-unsafe (use separate state per thread)

---

### cc_backoff_reset

**Signature:**
```c
void cc_backoff_reset(cc_backoff_t *b);
```

**Description:** Reset backoff to minimum after successful operation.

**Preconditions:**
- `b` initialized

**Postconditions:**
- `b->current == b->min`

**Errors:** None

**Complexity:** O(1)

**Thread Safety:** Thread-unsafe

---

### cc_pause

**Signature:**
```c
void cc_pause(void);
```

**Description:** Execute single platform-specific pause instruction.

**Preconditions:** None

**Postconditions:**
- On x86-64: `pause` instruction executed
- On ARM64: `yield` instruction executed
- On other: No-op (empty spin)

**Errors:** None

**Complexity:** O(1)

**Thread Safety:** Thread-safe (no shared state)

## Error Handling

| Error Condition | Detection | Response |
|-----------------|-----------|----------|
| NULL pointer | Not detected | Undefined behavior |
| min > max | Not detected | Undefined behavior |
| min == 0 | Not detected | Undefined behavior |

**Design Note:** No runtime checks for performance. Debug builds may add assertions.

## Thread Safety

| Guarantee | Scope | Notes |
|-----------|-------|-------|
| `cc_pause` | Thread-safe | No shared state |
| `cc_backoff_*` | Thread-unsafe | Use thread-local backoff state |

**Usage Pattern:**
```c
// Each thread has its own backoff state
static _Thread_local cc_backoff_t my_backoff = CC_BACKOFF_INIT;

while (!try_operation()) {
    cc_backoff(&my_backoff);
}
cc_backoff_reset(&my_backoff);
```

## Memory Model

No memory ordering requirements. Backoff state is thread-local.

## Performance Bounds

| Operation | Average | Worst Case | Notes |
|-----------|---------|------------|-------|
| `cc_backoff_init` | O(1) | O(1) | Three stores |
| `cc_backoff` | O(current) | O(max) | current pause instructions |
| `cc_backoff_reset` | O(1) | O(1) | One store |
| `cc_pause` | O(1) | O(1) | Single instruction |

### Pause Instruction Timing

| Platform | Instruction | Typical Cycles |
|----------|-------------|----------------|
| x86-64 | `pause` | ~10-140 cycles |
| ARM64 | `yield` | ~1 cycle (hint) |
| Other | Empty | ~0 cycles |

## Behavioral Properties

### Exponential Growth Sequence

With `min=1, max=1024`, the sequence of `current` values:
```
1 → 2 → 4 → 8 → 16 → 32 → 64 → 128 → 256 → 512 → 1024 → 1024 → ...
```

### Total Pause Iterations

After N backoff calls without reset:
- `total_pauses = sum(min * 2^i for i in 0..N-1)` until max reached
- Approximately `2 * max` once max is reached

### Contention Adaptation

- Low contention: Few backoffs, stays near `min`
- High contention: Grows to `max`, reducing cache traffic
- Success: Reset to `min` for quick retry
