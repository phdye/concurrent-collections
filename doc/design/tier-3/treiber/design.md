# treiber — Design Document

## Overview

`treiber` implements Treiber's classic lock-free stack with elimination backoff. This provides a LIFO (Last-In-First-Out) data structure with lock-free push and pop operations. The elimination optimization significantly improves performance under high contention by allowing matching push/pop pairs to exchange directly.

## Algorithm: Treiber Stack with Elimination

### Core Concept

The basic Treiber stack uses a single CAS to atomically update the top pointer:
- **Push**: CAS(top, old_top, new_node) where new_node->next = old_top
- **Pop**: CAS(top, old_top, old_top->next)

### Elimination Backoff

Under contention, CAS failures waste CPU. Elimination allows a push and pop to rendezvous:
1. Failing thread enters elimination array
2. Push thread deposits item at random slot
3. Pop thread checks slots for items
4. Matching pair exchanges without touching main stack

## Data Structures

### Node Structure

```c
typedef struct treiber_node {
    void *item;
    _Atomic(struct treiber_node *) next;
} treiber_node_t;
```

### Elimination Slot

```c
typedef enum {
    SLOT_EMPTY,
    SLOT_WAITING,       // Push waiting for pop
    SLOT_BUSY           // Exchange in progress
} slot_state_t;

typedef struct elimination_slot {
    _Atomic(slot_state_t) state;
    _Atomic(void *) item;
    _Atomic(uint64_t) stamp;    // ABA prevention
} elimination_slot_t __attribute__((aligned(64)));
```

### Stack Structure

```c
#define ELIMINATION_ARRAY_SIZE 16
#define ELIMINATION_TIMEOUT_NS 1000000  // 1ms

typedef struct treiber_stack {
    _Atomic(treiber_node_t *) top;
    _Atomic(size_t) count;              // Approximate size
    smr_domain_t *smr;

    // Elimination array
    elimination_slot_t elimination[ELIMINATION_ARRAY_SIZE];
    bool elimination_enabled;

    // Profiling
    _Atomic(uint64_t) push_cas_failures;
    _Atomic(uint64_t) pop_cas_failures;
    _Atomic(uint64_t) eliminations;
} treiber_stack_t;
```

## Core Operations

### Push Operation

```c
void treiber_push(treiber_stack_t *stack, void *item) {
    if (item == NULL) return;

    treiber_node_t *node = treiber_node_alloc(item);

    smr_enter(stack->smr);

    int failures = 0;
    while (true) {
        treiber_node_t *old_top = atomic_load(&stack->top);
        atomic_store(&node->next, old_top);

        if (atomic_compare_exchange_weak(&stack->top, &old_top, node)) {
            // Success
            atomic_fetch_add(&stack->count, 1);
            smr_exit(stack->smr);
            return;
        }

        failures++;
        atomic_fetch_add(&stack->push_cas_failures, 1);

        // Try elimination after threshold
        if (stack->elimination_enabled && failures > 2) {
            if (try_elimination_push(stack, item)) {
                treiber_node_free(node);  // Item exchanged, free unused node
                smr_exit(stack->smr);
                return;
            }
        }

        // Exponential backoff
        backoff_wait(failures);
    }
}
```

### Pop Operation

```c
void *treiber_pop(treiber_stack_t *stack) {
    smr_enter(stack->smr);

    int failures = 0;
    while (true) {
        treiber_node_t *old_top = atomic_load(&stack->top);

        if (old_top == NULL) {
            smr_exit(stack->smr);
            return NULL;  // Empty
        }

        treiber_node_t *new_top = atomic_load(&old_top->next);

        if (atomic_compare_exchange_weak(&stack->top, &old_top, new_top)) {
            // Success
            void *item = old_top->item;
            atomic_fetch_sub(&stack->count, 1);

            smr_retire(stack->smr, old_top, treiber_node_free);
            smr_exit(stack->smr);
            return item;
        }

        failures++;
        atomic_fetch_add(&stack->pop_cas_failures, 1);

        // Try elimination
        if (stack->elimination_enabled && failures > 2) {
            void *item = try_elimination_pop(stack);
            if (item != NULL) {
                smr_exit(stack->smr);
                return item;
            }
        }

        backoff_wait(failures);
    }
}
```

### Elimination Push

```c
static bool try_elimination_push(treiber_stack_t *stack, void *item) {
    // Pick random slot
    size_t slot_idx = random_slot();
    elimination_slot_t *slot = &stack->elimination[slot_idx];

    uint64_t stamp = atomic_load(&slot->stamp);
    slot_state_t state = atomic_load(&slot->state);

    if (state != SLOT_EMPTY) {
        return false;  // Slot busy
    }

    // Try to claim slot for push
    if (!atomic_compare_exchange_strong(&slot->state,
            &state, SLOT_WAITING)) {
        return false;
    }

    // Deposit item
    atomic_store(&slot->item, item);

    // Wait for pop to take it
    uint64_t start = get_time_ns();
    while (get_time_ns() - start < ELIMINATION_TIMEOUT_NS) {
        if (atomic_load(&slot->item) == NULL) {
            // Pop took the item!
            atomic_store(&slot->state, SLOT_EMPTY);
            atomic_fetch_add(&slot->stamp, 1);
            atomic_fetch_add(&stack->eliminations, 1);
            return true;
        }
        cpu_pause();
    }

    // Timeout - reclaim item
    void *expected = item;
    if (atomic_compare_exchange_strong(&slot->item, &expected, NULL)) {
        // We got it back
        atomic_store(&slot->state, SLOT_EMPTY);
        atomic_fetch_add(&slot->stamp, 1);
        return false;
    }

    // Pop took it just as we timed out
    atomic_store(&slot->state, SLOT_EMPTY);
    atomic_fetch_add(&slot->stamp, 1);
    atomic_fetch_add(&stack->eliminations, 1);
    return true;
}
```

### Elimination Pop

```c
static void *try_elimination_pop(treiber_stack_t *stack) {
    // Check random slot
    size_t slot_idx = random_slot();
    elimination_slot_t *slot = &stack->elimination[slot_idx];

    slot_state_t state = atomic_load(&slot->state);
    if (state != SLOT_WAITING) {
        return NULL;  // No push waiting
    }

    void *item = atomic_load(&slot->item);
    if (item == NULL) {
        return NULL;
    }

    // Try to take item
    if (atomic_compare_exchange_strong(&slot->item, &item, NULL)) {
        atomic_fetch_add(&stack->eliminations, 1);
        return item;
    }

    return NULL;  // Race - push reclaimed it
}
```

## StackProfiler API

```python
from dataclasses import dataclass
from typing import Dict
from contextlib import contextmanager
import threading
import time

@dataclass
class StackStats:
    """Statistics for Treiber stack."""

    total_pushes: int = 0
    total_pops: int = 0
    empty_pops: int = 0

    # CAS metrics
    push_cas_attempts: int = 0
    push_cas_failures: int = 0
    pop_cas_attempts: int = 0
    pop_cas_failures: int = 0

    # Elimination metrics
    elimination_successes: int = 0
    elimination_attempts: int = 0
    elimination_rate: float = 0.0

    # Stack state
    current_size: int = 0
    peak_size: int = 0

    # Latency
    push_latency_p50: float = 0.0
    push_latency_p99: float = 0.0
    pop_latency_p50: float = 0.0
    pop_latency_p99: float = 0.0


class StackProfiler:
    """
    Profiler for Treiber stack with elimination tracking.
    """

    def __init__(
        self,
        *,
        track_latency: bool = True,
        track_cas: bool = True,
        track_elimination: bool = True,
    ):
        self.track_latency = track_latency
        self.track_cas = track_cas
        self.track_elimination = track_elimination

        self._lock = threading.Lock()
        self._reset()

    def _reset(self):
        self._push_count = 0
        self._pop_count = 0
        self._empty_pops = 0
        self._push_cas_attempts = 0
        self._push_cas_failures = 0
        self._pop_cas_attempts = 0
        self._pop_cas_failures = 0
        self._elimination_successes = 0
        self._elimination_attempts = 0
        self._current_size = 0
        self._peak_size = 0
        self._latency_push = []
        self._latency_pop = []

    @contextmanager
    def profile_push(self):
        start = time.perf_counter_ns()
        ctx = {'cas_attempts': 0, 'cas_failures': 0,
               'elimination_attempted': False, 'eliminated': False}
        try:
            yield ctx
        finally:
            elapsed = time.perf_counter_ns() - start
            with self._lock:
                self._push_count += 1
                self._current_size += 1
                self._peak_size = max(self._peak_size, self._current_size)

                if self.track_cas:
                    self._push_cas_attempts += ctx['cas_attempts']
                    self._push_cas_failures += ctx['cas_failures']

                if self.track_elimination:
                    if ctx['elimination_attempted']:
                        self._elimination_attempts += 1
                    if ctx['eliminated']:
                        self._elimination_successes += 1

                if self.track_latency:
                    self._latency_push.append(elapsed / 1000)

    @contextmanager
    def profile_pop(self):
        start = time.perf_counter_ns()
        ctx = {'cas_attempts': 0, 'cas_failures': 0,
               'empty': False, 'eliminated': False}
        try:
            yield ctx
        finally:
            elapsed = time.perf_counter_ns() - start
            with self._lock:
                if ctx['empty']:
                    self._empty_pops += 1
                else:
                    self._pop_count += 1
                    self._current_size = max(0, self._current_size - 1)

                if self.track_cas:
                    self._pop_cas_attempts += ctx['cas_attempts']
                    self._pop_cas_failures += ctx['cas_failures']

                if ctx['eliminated']:
                    self._elimination_successes += 1

                if self.track_latency:
                    self._latency_pop.append(elapsed / 1000)

    def get_stats(self) -> StackStats:
        with self._lock:
            stats = StackStats()

            stats.total_pushes = self._push_count
            stats.total_pops = self._pop_count
            stats.empty_pops = self._empty_pops

            stats.push_cas_attempts = self._push_cas_attempts
            stats.push_cas_failures = self._push_cas_failures
            stats.pop_cas_attempts = self._pop_cas_attempts
            stats.pop_cas_failures = self._pop_cas_failures

            stats.elimination_successes = self._elimination_successes
            stats.elimination_attempts = self._elimination_attempts
            if self._elimination_attempts > 0:
                stats.elimination_rate = self._elimination_successes / self._elimination_attempts

            stats.current_size = self._current_size
            stats.peak_size = self._peak_size

            if self._latency_push:
                sorted_lat = sorted(self._latency_push)
                n = len(sorted_lat)
                stats.push_latency_p50 = sorted_lat[int(n * 0.50)]
                stats.push_latency_p99 = sorted_lat[min(int(n * 0.99), n-1)]

            if self._latency_pop:
                sorted_lat = sorted(self._latency_pop)
                n = len(sorted_lat)
                stats.pop_latency_p50 = sorted_lat[int(n * 0.50)]
                stats.pop_latency_p99 = sorted_lat[min(int(n * 0.99), n-1)]

            return stats

    def analyze_elimination_effectiveness(self) -> Dict:
        """Analyze if elimination is helping."""
        stats = self.get_stats()

        total_cas_failures = stats.push_cas_failures + stats.pop_cas_failures
        total_ops = stats.total_pushes + stats.total_pops

        if total_ops == 0:
            return {'elimination_recommended': False, 'reason': 'No operations'}

        contention = total_cas_failures / max(total_ops, 1)

        if contention < 0.1:
            return {
                'elimination_recommended': False,
                'reason': 'Low contention - elimination overhead not justified',
                'contention_rate': contention,
            }

        if stats.elimination_rate > 0.3:
            return {
                'elimination_recommended': True,
                'reason': f'Elimination effective: {stats.elimination_rate:.1%} success',
                'contention_rate': contention,
            }

        return {
            'elimination_recommended': True,
            'reason': 'High contention - consider tuning array size or timeout',
            'contention_rate': contention,
            'current_elimination_rate': stats.elimination_rate,
        }

    def export_prometheus(self) -> str:
        """Export metrics in Prometheus format."""
        stats = self.get_stats()
        lines = [
            '# HELP stack_operations_total Total stack operations',
            '# TYPE stack_operations_total counter',
            f'stack_operations_total{{op="push"}} {stats.total_pushes}',
            f'stack_operations_total{{op="pop"}} {stats.total_pops}',
            f'stack_operations_total{{op="pop_empty"}} {stats.empty_pops}',
            '',
            '# HELP stack_eliminations_total Successful eliminations',
            '# TYPE stack_eliminations_total counter',
            f'stack_eliminations_total {stats.elimination_successes}',
            '',
            '# HELP stack_size Current stack size',
            '# TYPE stack_size gauge',
            f'stack_size {stats.current_size}',
        ]
        return '\n'.join(lines)
```

## Thread Safety

| Operation | Progress |
|-----------|----------|
| Push | Lock-free |
| Pop | Lock-free |
| Elimination | Lock-free |

## Memory Ordering

| Operation | Order |
|-----------|-------|
| top load | Acquire |
| top CAS | Acq-Rel |
| node.next | Release (push), Acquire (pop) |

## Configuration

```c
typedef struct treiber_config {
    bool enable_elimination;
    size_t elimination_array_size;
    uint64_t elimination_timeout_ns;
    size_t backoff_min_ns;
    size_t backoff_max_ns;
} treiber_config_t;

static const treiber_config_t TREIBER_DEFAULT_CONFIG = {
    .enable_elimination = true,
    .elimination_array_size = 16,
    .elimination_timeout_ns = 1000000,
    .backoff_min_ns = 100,
    .backoff_max_ns = 10000,
};
```

## References

- Treiber, R. K. (1986). "Systems Programming: Coping with Parallelism."
- Hendler, D., Shavit, N., & Yerushalmi, L. (2004). "A Scalable Lock-free Stack Algorithm."
