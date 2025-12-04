# backoff — Design

## Overview

The `backoff` module provides exponential backoff strategies for contention management in lock-free algorithms. It reduces cache line bouncing and improves throughput under contention.

## Dependencies

| Dependency | Purpose |
|------------|---------|
| arch_detect | Platform-specific pause instructions |

## Architecture

### Backoff State

```c
typedef struct {
    uint32_t current;     // Current backoff iterations
    uint32_t min;         // Minimum iterations (after success)
    uint32_t max;         // Maximum iterations (cap)
} cc_backoff_t;

#define CC_BACKOFF_INIT { .current = 1, .min = 1, .max = 1024 }
```

### Pause Instructions

| Platform | Instruction | Purpose |
|----------|-------------|---------|
| x86-64 | `pause` | Reduce power, hint spin-wait |
| ARM64 | `yield` | Hint spin-wait to scheduler |
| Other | Empty loop | Portable fallback |

```c
static inline void cc_pause(void) {
#if defined(__x86_64__) || defined(_M_X64)
    _mm_pause();
#elif defined(__aarch64__)
    __asm__ __volatile__("yield");
#else
    // Portable: just spin
#endif
}
```

### Exponential Backoff Algorithm

```c
static inline void cc_backoff(cc_backoff_t *b) {
    for (uint32_t i = 0; i < b->current; i++) {
        cc_pause();
    }
    // Double up to max
    if (b->current < b->max) {
        b->current *= 2;
    }
}

static inline void cc_backoff_reset(cc_backoff_t *b) {
    b->current = b->min;
}
```

## API Surface

```c
// Initialize backoff state
void cc_backoff_init(cc_backoff_t *b, uint32_t min, uint32_t max);

// Execute backoff (call after CAS failure)
void cc_backoff(cc_backoff_t *b);

// Reset after success
void cc_backoff_reset(cc_backoff_t *b);

// Single pause instruction
void cc_pause(void);
```

## Design Decisions

| Decision | Choice | Rationale |
|----------|--------|-----------|
| Default min | 1 | Quick retry for low contention |
| Default max | 1024 | Prevent excessive spinning |
| Growth factor | 2x | Standard exponential backoff |
| Pause instruction | Platform-specific | Best performance per platform |
