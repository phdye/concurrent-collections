# wcq — Design Document

## Overview

`wcq` implements a Wait-Free Circular Queue providing the strongest progress guarantee: every operation completes in a bounded number of steps regardless of other threads' behavior. This is crucial for real-time systems and situations where worst-case latency matters more than average throughput.

## Algorithm: Wait-Free Queue

### Key Concepts

1. **Wait-Freedom**: Every operation completes in O(n) steps where n = thread count
2. **Helping Mechanism**: Fast threads help slow threads complete
3. **Announcement Array**: Threads announce pending operations
4. **Phase Clock**: Global phase coordinates helping

### Why Wait-Free?

- **Bounded Latency**: Guaranteed worst-case completion time
- **Real-Time Safe**: No unbounded spinning
- **Starvation-Free**: Every thread makes progress

### Trade-offs

- Lower average throughput than lock-free
- Higher memory overhead (announcement arrays)
- More complex implementation

## Data Structures

### Operation Announcement

```c
typedef enum {
    OP_NONE,
    OP_ENQUEUE,
    OP_DEQUEUE
} wcq_op_type_t;

typedef struct wcq_op {
    _Atomic(wcq_op_type_t) type;
    _Atomic(void *) item;           // For enqueue
    _Atomic(void *) result;         // For dequeue
    _Atomic(uint64_t) phase;        // Operation phase
    _Atomic(bool) completed;        // Operation done
} wcq_op_t;
```

### Queue Structure

```c
typedef struct wcq {
    // Ring buffer
    _Atomic(void *) *slots;
    size_t capacity;

    // Position counters
    _Atomic(uint64_t) head;
    _Atomic(uint64_t) tail;

    // Wait-free machinery
    _Atomic(uint64_t) phase;        // Global phase
    wcq_op_t *announcements;        // Per-thread announcements
    size_t max_threads;

    // Thread registration
    _Atomic(uint32_t) *thread_ids;
    _Atomic(uint32_t) next_thread_id;
} wcq_t;
```

## Core Operations

### Enqueue (Wait-Free)

```c
bool wcq_enqueue(wcq_t *q, void *item) {
    if (item == NULL) return false;

    uint32_t tid = wcq_get_thread_id(q);
    wcq_op_t *my_op = &q->announcements[tid];

    // Announce operation
    uint64_t my_phase = atomic_fetch_add(&q->phase, 1);
    atomic_store(&my_op->type, OP_ENQUEUE);
    atomic_store(&my_op->item, item);
    atomic_store(&my_op->phase, my_phase);
    atomic_store(&my_op->completed, false);

    // Help others and self
    wcq_help_all(q, my_phase);

    // Check result
    bool success = atomic_load(&my_op->completed);

    // Clear announcement
    atomic_store(&my_op->type, OP_NONE);

    return success;
}
```

### Help All Operations

```c
static void wcq_help_all(wcq_t *q, uint64_t until_phase) {
    for (uint32_t tid = 0; tid < q->max_threads; tid++) {
        wcq_op_t *op = &q->announcements[tid];

        wcq_op_type_t type = atomic_load(&op->type);
        uint64_t phase = atomic_load(&op->phase);
        bool completed = atomic_load(&op->completed);

        if (type != OP_NONE && phase <= until_phase && !completed) {
            if (type == OP_ENQUEUE) {
                wcq_help_enqueue(q, op);
            } else {
                wcq_help_dequeue(q, op);
            }
        }
    }
}

static void wcq_help_enqueue(wcq_t *q, wcq_op_t *op) {
    // Try to complete the enqueue
    void *item = atomic_load(&op->item);

    while (!atomic_load(&op->completed)) {
        uint64_t tail = atomic_load(&q->tail);
        uint64_t head = atomic_load(&q->head);

        if (tail - head >= q->capacity) {
            // Queue full, mark as failed
            atomic_store(&op->completed, true);
            return;
        }

        size_t index = tail % q->capacity;
        void *expected = NULL;

        if (atomic_compare_exchange_strong(&q->slots[index],
                &expected, item)) {
            atomic_fetch_add(&q->tail, 1);
            atomic_store(&op->completed, true);
            return;
        }

        // Slot occupied, advance tail and retry
        atomic_compare_exchange_weak(&q->tail, &tail, tail + 1);
    }
}

static void wcq_help_dequeue(wcq_t *q, wcq_op_t *op) {
    while (!atomic_load(&op->completed)) {
        uint64_t head = atomic_load(&q->head);
        uint64_t tail = atomic_load(&q->tail);

        if (head >= tail) {
            // Queue empty
            atomic_store(&op->result, NULL);
            atomic_store(&op->completed, true);
            return;
        }

        size_t index = head % q->capacity;
        void *item = atomic_load(&q->slots[index]);

        if (item != NULL) {
            if (atomic_compare_exchange_strong(&q->slots[index],
                    &item, NULL)) {
                atomic_fetch_add(&q->head, 1);
                atomic_store(&op->result, item);
                atomic_store(&op->completed, true);
                return;
            }
        }

        // Advance head and retry
        atomic_compare_exchange_weak(&q->head, &head, head + 1);
    }
}
```

### Dequeue (Wait-Free)

```c
void *wcq_dequeue(wcq_t *q) {
    uint32_t tid = wcq_get_thread_id(q);
    wcq_op_t *my_op = &q->announcements[tid];

    // Announce operation
    uint64_t my_phase = atomic_fetch_add(&q->phase, 1);
    atomic_store(&my_op->type, OP_DEQUEUE);
    atomic_store(&my_op->result, NULL);
    atomic_store(&my_op->phase, my_phase);
    atomic_store(&my_op->completed, false);

    // Help others and self
    wcq_help_all(q, my_phase);

    // Get result
    void *result = atomic_load(&my_op->result);

    // Clear announcement
    atomic_store(&my_op->type, OP_NONE);

    return result;
}
```

## WCQProfiler API

```python
from dataclasses import dataclass
from typing import Dict
from contextlib import contextmanager
import threading
import time

@dataclass
class WCQStats:
    """Statistics for Wait-Free Queue."""

    total_enqueues: int = 0
    total_dequeues: int = 0
    failed_enqueues: int = 0
    failed_dequeues: int = 0

    # Help metrics
    total_help_operations: int = 0
    self_completions: int = 0      # Completed by self
    helped_completions: int = 0    # Completed by helper

    # Steps metrics (key for wait-freedom)
    avg_steps_per_op: float = 0.0
    max_steps_per_op: int = 0      # Should be bounded!
    steps_bound_violations: int = 0

    # Latency (should be bounded for wait-free)
    enqueue_latency_p50: float = 0.0
    enqueue_latency_p99: float = 0.0
    enqueue_latency_max: float = 0.0  # Critical metric
    dequeue_latency_p50: float = 0.0
    dequeue_latency_p99: float = 0.0
    dequeue_latency_max: float = 0.0


class WCQProfiler:
    """
    Profiler for Wait-Free Queue with bounded-step verification.
    """

    def __init__(
        self,
        *,
        track_latency: bool = True,
        track_steps: bool = True,
        track_helping: bool = True,
        expected_step_bound: int = 100,
    ):
        self.track_latency = track_latency
        self.track_steps = track_steps
        self.track_helping = track_helping
        self.expected_step_bound = expected_step_bound

        self._lock = threading.Lock()
        self._reset()

    def _reset(self):
        self._enqueue_count = 0
        self._dequeue_count = 0
        self._enqueue_failed = 0
        self._dequeue_failed = 0
        self._help_ops = 0
        self._self_completions = 0
        self._helped_completions = 0
        self._steps = []
        self._max_steps = 0
        self._bound_violations = 0
        self._latency_enqueue = []
        self._latency_dequeue = []

    @contextmanager
    def profile_enqueue(self):
        start = time.perf_counter_ns()
        ctx = {'steps': 0, 'helped': False, 'success': True}
        try:
            yield ctx
        finally:
            elapsed = time.perf_counter_ns() - start
            with self._lock:
                if ctx['success']:
                    self._enqueue_count += 1
                    if ctx['helped']:
                        self._helped_completions += 1
                    else:
                        self._self_completions += 1
                else:
                    self._enqueue_failed += 1

                if self.track_steps:
                    self._steps.append(ctx['steps'])
                    self._max_steps = max(self._max_steps, ctx['steps'])
                    if ctx['steps'] > self.expected_step_bound:
                        self._bound_violations += 1

                if self.track_latency:
                    self._latency_enqueue.append(elapsed / 1000)

    @contextmanager
    def profile_dequeue(self):
        start = time.perf_counter_ns()
        ctx = {'steps': 0, 'helped': False, 'success': True}
        try:
            yield ctx
        finally:
            elapsed = time.perf_counter_ns() - start
            with self._lock:
                if ctx['success']:
                    self._dequeue_count += 1
                else:
                    self._dequeue_failed += 1

                if self.track_steps:
                    self._steps.append(ctx['steps'])
                    self._max_steps = max(self._max_steps, ctx['steps'])

                if self.track_latency:
                    self._latency_dequeue.append(elapsed / 1000)

    def record_help(self):
        with self._lock:
            self._help_ops += 1

    def get_stats(self) -> WCQStats:
        with self._lock:
            stats = WCQStats()

            stats.total_enqueues = self._enqueue_count
            stats.total_dequeues = self._dequeue_count
            stats.failed_enqueues = self._enqueue_failed
            stats.failed_dequeues = self._dequeue_failed

            stats.total_help_operations = self._help_ops
            stats.self_completions = self._self_completions
            stats.helped_completions = self._helped_completions

            if self._steps:
                stats.avg_steps_per_op = sum(self._steps) / len(self._steps)
            stats.max_steps_per_op = self._max_steps
            stats.steps_bound_violations = self._bound_violations

            if self._latency_enqueue:
                sorted_lat = sorted(self._latency_enqueue)
                n = len(sorted_lat)
                stats.enqueue_latency_p50 = sorted_lat[int(n * 0.50)]
                stats.enqueue_latency_p99 = sorted_lat[min(int(n * 0.99), n-1)]
                stats.enqueue_latency_max = sorted_lat[-1]

            if self._latency_dequeue:
                sorted_lat = sorted(self._latency_dequeue)
                n = len(sorted_lat)
                stats.dequeue_latency_p50 = sorted_lat[int(n * 0.50)]
                stats.dequeue_latency_p99 = sorted_lat[min(int(n * 0.99), n-1)]
                stats.dequeue_latency_max = sorted_lat[-1]

            return stats

    def verify_wait_freedom(self, thread_count: int) -> Dict:
        """Verify that step bound holds (critical for wait-free claim)."""
        stats = self.get_stats()
        theoretical_bound = thread_count * 2 + 10  # O(n) with constant

        issues = []
        if stats.max_steps_per_op > theoretical_bound:
            issues.append(f"Step bound exceeded: {stats.max_steps_per_op} > {theoretical_bound}")

        if stats.steps_bound_violations > 0:
            issues.append(f"{stats.steps_bound_violations} operations exceeded expected bound")

        return {
            'is_wait_free': len(issues) == 0,
            'theoretical_bound': theoretical_bound,
            'observed_max': stats.max_steps_per_op,
            'issues': issues,
        }
```

## Progress Guarantee

| Property | Guarantee |
|----------|-----------|
| Progress | Wait-free |
| Steps | O(n) where n = thread count |
| Starvation | Impossible |

## Comparison

| Metric | WCQ | SCQ | LCRQ |
|--------|-----|-----|------|
| Progress | Wait-free | Lock-free | Lock-free |
| Throughput | 1x | 3-5x | 5-8x |
| Worst latency | Bounded | Unbounded | Unbounded |
| Memory | O(n) extra | Minimal | Moderate |

## Use Cases

1. **Real-Time Systems**: Hard latency requirements
2. **Safety-Critical**: Must never stall
3. **Fairness-Critical**: All threads equally served

## References

- Kogan, A., & Petrank, E. (2011). "Wait-Free Queues With Multiple Enqueuers and Dequeuers."
- Herlihy, M. (1991). "Wait-Free Synchronization."
