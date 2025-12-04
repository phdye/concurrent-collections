# scq — Design Document

## Overview

`scq` implements the Scalable Circular Queue (SCQ) algorithm by Nikolaev and Ravindran. This is a portable lock-free MPMC (Multi-Producer Multi-Consumer) queue that uses only single-width CAS operations, making it work on all platforms without requiring double-width atomics like CMPXCHG16B.

## Algorithm: Nikolaev-Ravindran SCQ

### Key Innovations

1. **Single-Width CAS**: Uses clever index manipulation instead of DCAS
2. **Circular Buffer**: Fixed-size ring buffer with wraparound
3. **Slot Reservation**: Threads reserve slots before writing
4. **Safe Bit**: Distinguishes valid entries from stale ones

### Why SCQ?

- **Portability**: Works on ARM64, older x86, any architecture
- **Performance**: Competitive with LCRQ for many workloads
- **Simplicity**: Easier to understand than LCRQ

## Data Structures

### Slot Structure

```c
// Slot entry combining value and metadata
typedef struct scq_slot {
    _Atomic(uint64_t) entry;
    // Bits 0-62:  data pointer or index
    // Bit 63:     safe bit (cycle validation)
} scq_slot_t;

#define SCQ_SAFE_BIT    (1ULL << 63)
#define SCQ_INDEX_MASK  (~SCQ_SAFE_BIT)
#define IS_SAFE(e)      ((e) & SCQ_SAFE_BIT)
#define GET_INDEX(e)    ((e) & SCQ_INDEX_MASK)
```

### Queue Structure

```c
typedef struct scq {
    _Atomic(uint64_t) head;         // Dequeue position
    _Atomic(uint64_t) tail;         // Enqueue position
    _Atomic(uint64_t) threshold;    // Threshold for catchup
    size_t capacity;                // Power of 2
    size_t mask;                    // capacity - 1
    scq_slot_t *slots;              // Ring buffer
    smr_domain_t *smr;              // For stored objects
} scq_t;
```

### Entry Encoding

```c
// Entry states:
// - Empty slot:     entry = (cycle << shift) | SAFE_BIT
// - Full slot:      entry = pointer | SAFE_BIT  (if cycle matches)
// - Stale slot:     entry without SAFE_BIT set for current cycle

static inline uint64_t make_entry(void *ptr, uint64_t cycle, bool safe) {
    uint64_t entry = (uint64_t)ptr;
    if (safe) entry |= SCQ_SAFE_BIT;
    return entry;
}
```

## Core Operations

### Enqueue Operation

```c
bool scq_enqueue(scq_t *q, void *item) {
    if (item == NULL) return false;

    while (true) {
        // Reserve tail slot
        uint64_t tail = atomic_fetch_add(&q->tail, 1);
        uint64_t cycle = tail / q->capacity;
        size_t index = tail & q->mask;

        scq_slot_t *slot = &q->slots[index];
        uint64_t entry = atomic_load(&slot->entry);

        // Calculate expected empty state
        uint64_t expected_cycle = cycle;
        uint64_t safe_entry = (expected_cycle << 48) | SCQ_SAFE_BIT;

        // Check if slot is available for this cycle
        if (GET_INDEX(entry) <= tail) {
            // Slot available, try to claim it
            uint64_t new_entry = make_entry(item, cycle, true);

            if (atomic_compare_exchange_strong(&slot->entry, &entry, new_entry)) {
                // Success
                return true;
            }
        }

        // Slot not available, check if queue is full
        uint64_t head = atomic_load(&q->head);
        if (tail - head >= q->capacity) {
            // Queue full
            // Try to help advance head if there are consumed entries
            scq_try_advance_head(q, head);

            // Check again
            head = atomic_load(&q->head);
            if (tail - head >= q->capacity) {
                return false;  // Still full
            }
        }

        // Retry with new tail
    }
}
```

### Dequeue Operation

```c
void *scq_dequeue(scq_t *q) {
    while (true) {
        // Reserve head slot
        uint64_t head = atomic_fetch_add(&q->head, 1);
        uint64_t cycle = head / q->capacity;
        size_t index = head & q->mask;

        scq_slot_t *slot = &q->slots[index];

        while (true) {
            uint64_t entry = atomic_load(&slot->entry);

            // Check if entry is valid for this cycle
            if (IS_SAFE(entry)) {
                void *item = (void *)GET_INDEX(entry);

                // Verify it's a valid pointer (not cycle marker)
                if (item != NULL && (uint64_t)item < (1ULL << 48)) {
                    // Try to consume
                    uint64_t consumed = make_entry(NULL, cycle + 1, true);

                    if (atomic_compare_exchange_strong(&slot->entry,
                            &entry, consumed)) {
                        return item;
                    }
                    // CAS failed, retry reading
                    continue;
                }
            }

            // Check if queue is empty
            uint64_t tail = atomic_load(&q->tail);
            if (head >= tail) {
                // Empty
                return NULL;
            }

            // Slot not ready yet, spin briefly then retry
            cpu_pause();
        }
    }
}
```

### Catchup Mechanism

```c
static void scq_try_advance_head(scq_t *q, uint64_t head) {
    // Try to advance head past consumed entries
    // This helps when dequeue threads have consumed but not yet
    // completed their CAS

    uint64_t threshold = atomic_load(&q->threshold);
    if (head < threshold) return;

    // Scan forward looking for consumed slots
    for (size_t i = 0; i < 16; i++) {
        size_t index = (head + i) & q->mask;
        uint64_t entry = atomic_load(&q->slots[index].entry);

        if (IS_SAFE(entry) && GET_INDEX(entry) == 0) {
            // Slot has been consumed, try to advance threshold
            atomic_compare_exchange_weak(&q->threshold,
                &threshold, head + i + 1);
        }
    }
}
```

## Bounded vs Unbounded

### Bounded Mode (Default)

```c
scq_t *scq_create_bounded(size_t capacity) {
    // Round up to power of 2
    capacity = next_power_of_2(capacity);

    scq_t *q = cc_alloc(sizeof(scq_t));
    q->slots = cc_alloc(sizeof(scq_slot_t) * capacity);
    q->capacity = capacity;
    q->mask = capacity - 1;

    // Initialize slots as empty
    for (size_t i = 0; i < capacity; i++) {
        q->slots[i].entry = SCQ_SAFE_BIT;  // Empty, safe
    }

    atomic_store(&q->head, 0);
    atomic_store(&q->tail, 0);
    atomic_store(&q->threshold, 0);

    return q;
}
```

### Unbounded Mode (Linked Segments)

```c
typedef struct scq_segment {
    scq_t ring;                         // Embedded ring buffer
    _Atomic(struct scq_segment *) next; // Link to next segment
    uint64_t id;                        // Segment ID
} scq_segment_t;

typedef struct scq_unbounded {
    _Atomic(scq_segment_t *) head_segment;
    _Atomic(scq_segment_t *) tail_segment;
    size_t segment_capacity;
    smr_domain_t *smr;
} scq_unbounded_t;

bool scq_unbounded_enqueue(scq_unbounded_t *q, void *item) {
    while (true) {
        scq_segment_t *tail_seg = atomic_load(&q->tail_segment);

        if (scq_enqueue(&tail_seg->ring, item)) {
            return true;  // Success
        }

        // Segment full, allocate new one
        scq_segment_t *new_seg = alloc_segment(q->segment_capacity);
        new_seg->id = tail_seg->id + 1;

        // Try to link new segment
        scq_segment_t *expected = NULL;
        if (atomic_compare_exchange_strong(&tail_seg->next,
                &expected, new_seg)) {
            // Successfully linked, update tail
            atomic_compare_exchange_strong(&q->tail_segment,
                &tail_seg, new_seg);
        } else {
            // Another thread beat us, free our segment
            free_segment(new_seg);
        }

        // Retry enqueue
    }
}
```

## QueueProfiler API

```python
from dataclasses import dataclass, field
from typing import Dict, List, Optional
from contextlib import contextmanager
import threading
import time

@dataclass
class QueueStats:
    """Statistics for concurrent queue operations."""

    # Operation counts
    total_enqueues: int = 0
    total_dequeues: int = 0
    failed_enqueues: int = 0      # Queue full
    failed_dequeues: int = 0      # Queue empty

    # CAS metrics
    enqueue_cas_attempts: int = 0
    enqueue_cas_failures: int = 0
    dequeue_cas_attempts: int = 0
    dequeue_cas_failures: int = 0

    # Contention metrics
    enqueue_retries: int = 0
    dequeue_retries: int = 0
    avg_retries_per_enqueue: float = 0.0
    avg_retries_per_dequeue: float = 0.0

    # Queue state
    current_size: int = 0
    peak_size: int = 0
    capacity: int = 0
    utilization: float = 0.0

    # Latency (microseconds)
    enqueue_latency_p50: float = 0.0
    enqueue_latency_p99: float = 0.0
    dequeue_latency_p50: float = 0.0
    dequeue_latency_p99: float = 0.0

    # Throughput
    enqueue_throughput: float = 0.0  # ops/sec
    dequeue_throughput: float = 0.0


class QueueProfiler:
    """
    Profiler for concurrent queue implementations (SCQ, LCRQ, WCQ).

    Features:
    - Operation success/failure tracking
    - CAS attempt monitoring
    - Retry analysis
    - Queue utilization metrics
    - Latency percentiles
    - Throughput measurement
    """

    def __init__(
        self,
        *,
        track_latency: bool = True,
        track_cas: bool = True,
        track_size: bool = True,
        track_throughput: bool = True,
        throughput_window_sec: float = 1.0,
    ):
        self.track_latency = track_latency
        self.track_cas = track_cas
        self.track_size = track_size
        self.track_throughput = track_throughput
        self.throughput_window = throughput_window_sec

        self._lock = threading.Lock()
        self._reset_counters()

    def _reset_counters(self):
        self._enqueue_count = 0
        self._dequeue_count = 0
        self._enqueue_failed = 0
        self._dequeue_failed = 0

        self._enqueue_cas_attempts = 0
        self._enqueue_cas_failures = 0
        self._dequeue_cas_attempts = 0
        self._dequeue_cas_failures = 0

        self._enqueue_retries = []
        self._dequeue_retries = []

        self._current_size = 0
        self._peak_size = 0
        self._capacity = 0

        self._latency_enqueue = []
        self._latency_dequeue = []

        self._throughput_enqueue = []
        self._throughput_dequeue = []
        self._start_time = time.time()

    def set_capacity(self, capacity: int):
        """Set queue capacity for utilization calculation."""
        self._capacity = capacity

    @contextmanager
    def profile_enqueue(self):
        """Profile an enqueue operation."""
        start = time.perf_counter_ns()
        ctx = {'cas_attempts': 0, 'cas_failures': 0, 'retries': 0, 'success': True}

        try:
            yield ctx
        finally:
            elapsed = time.perf_counter_ns() - start

            with self._lock:
                if ctx['success']:
                    self._enqueue_count += 1
                    self._current_size += 1
                    self._peak_size = max(self._peak_size, self._current_size)
                else:
                    self._enqueue_failed += 1

                if self.track_cas:
                    self._enqueue_cas_attempts += ctx['cas_attempts']
                    self._enqueue_cas_failures += ctx['cas_failures']

                self._enqueue_retries.append(ctx['retries'])

                if self.track_latency:
                    self._latency_enqueue.append(elapsed / 1000)

                if self.track_throughput:
                    self._throughput_enqueue.append(time.time())

    @contextmanager
    def profile_dequeue(self):
        """Profile a dequeue operation."""
        start = time.perf_counter_ns()
        ctx = {'cas_attempts': 0, 'cas_failures': 0, 'retries': 0, 'success': True}

        try:
            yield ctx
        finally:
            elapsed = time.perf_counter_ns() - start

            with self._lock:
                if ctx['success']:
                    self._dequeue_count += 1
                    self._current_size = max(0, self._current_size - 1)
                else:
                    self._dequeue_failed += 1

                if self.track_cas:
                    self._dequeue_cas_attempts += ctx['cas_attempts']
                    self._dequeue_cas_failures += ctx['cas_failures']

                self._dequeue_retries.append(ctx['retries'])

                if self.track_latency:
                    self._latency_dequeue.append(elapsed / 1000)

                if self.track_throughput:
                    self._throughput_dequeue.append(time.time())

    def get_stats(self) -> QueueStats:
        """Get current statistics."""
        with self._lock:
            stats = QueueStats()

            stats.total_enqueues = self._enqueue_count
            stats.total_dequeues = self._dequeue_count
            stats.failed_enqueues = self._enqueue_failed
            stats.failed_dequeues = self._dequeue_failed

            stats.enqueue_cas_attempts = self._enqueue_cas_attempts
            stats.enqueue_cas_failures = self._enqueue_cas_failures
            stats.dequeue_cas_attempts = self._dequeue_cas_attempts
            stats.dequeue_cas_failures = self._dequeue_cas_failures

            stats.enqueue_retries = sum(self._enqueue_retries)
            stats.dequeue_retries = sum(self._dequeue_retries)

            if self._enqueue_retries:
                stats.avg_retries_per_enqueue = stats.enqueue_retries / len(self._enqueue_retries)
            if self._dequeue_retries:
                stats.avg_retries_per_dequeue = stats.dequeue_retries / len(self._dequeue_retries)

            stats.current_size = self._current_size
            stats.peak_size = self._peak_size
            stats.capacity = self._capacity
            if self._capacity > 0:
                stats.utilization = self._peak_size / self._capacity

            # Latency percentiles
            if self._latency_enqueue:
                sorted_lat = sorted(self._latency_enqueue)
                n = len(sorted_lat)
                stats.enqueue_latency_p50 = sorted_lat[int(n * 0.50)]
                stats.enqueue_latency_p99 = sorted_lat[min(int(n * 0.99), n-1)]

            if self._latency_dequeue:
                sorted_lat = sorted(self._latency_dequeue)
                n = len(sorted_lat)
                stats.dequeue_latency_p50 = sorted_lat[int(n * 0.50)]
                stats.dequeue_latency_p99 = sorted_lat[min(int(n * 0.99), n-1)]

            # Throughput (ops in last window)
            now = time.time()
            cutoff = now - self.throughput_window

            recent_enq = sum(1 for t in self._throughput_enqueue if t > cutoff)
            recent_deq = sum(1 for t in self._throughput_dequeue if t > cutoff)

            stats.enqueue_throughput = recent_enq / self.throughput_window
            stats.dequeue_throughput = recent_deq / self.throughput_window

            return stats

    def analyze_performance(self) -> Dict:
        """Analyze queue performance and provide recommendations."""
        stats = self.get_stats()
        issues = []
        recommendations = []

        # Check failure rate
        total_ops = stats.total_enqueues + stats.failed_enqueues
        if total_ops > 0:
            failure_rate = stats.failed_enqueues / total_ops
            if failure_rate > 0.01:
                issues.append(f"High enqueue failure rate: {failure_rate:.1%}")
                recommendations.append("Increase queue capacity or add backpressure")

        # Check CAS contention
        if stats.enqueue_cas_attempts > 0:
            cas_failure_rate = stats.enqueue_cas_failures / stats.enqueue_cas_attempts
            if cas_failure_rate > 0.2:
                issues.append(f"High CAS failure rate: {cas_failure_rate:.1%}")
                recommendations.append("Consider LCRQ for x86-64 or reduce thread count")

        # Check utilization
        if stats.utilization > 0.9:
            issues.append(f"Queue near capacity: {stats.utilization:.1%}")
            recommendations.append("Increase capacity or improve consumer throughput")

        return {
            'has_issues': len(issues) > 0,
            'issues': issues,
            'recommendations': recommendations,
            'metrics': {
                'throughput_enqueue': stats.enqueue_throughput,
                'throughput_dequeue': stats.dequeue_throughput,
                'utilization': stats.utilization,
            }
        }

    def export_prometheus(self) -> str:
        """Export metrics in Prometheus format."""
        stats = self.get_stats()
        lines = [
            '# HELP queue_operations_total Total queue operations',
            '# TYPE queue_operations_total counter',
            f'queue_operations_total{{op="enqueue",result="success"}} {stats.total_enqueues}',
            f'queue_operations_total{{op="enqueue",result="failed"}} {stats.failed_enqueues}',
            f'queue_operations_total{{op="dequeue",result="success"}} {stats.total_dequeues}',
            f'queue_operations_total{{op="dequeue",result="failed"}} {stats.failed_dequeues}',
            '',
            '# HELP queue_size Current queue size',
            '# TYPE queue_size gauge',
            f'queue_size {stats.current_size}',
            '',
            '# HELP queue_throughput Operations per second',
            '# TYPE queue_throughput gauge',
            f'queue_throughput{{op="enqueue"}} {stats.enqueue_throughput:.2f}',
            f'queue_throughput{{op="dequeue"}} {stats.dequeue_throughput:.2f}',
        ]
        return '\n'.join(lines)

    def reset(self):
        """Reset all counters."""
        with self._lock:
            self._reset_counters()
```

## Memory Ordering

| Operation | Order | Rationale |
|-----------|-------|-----------|
| slot load | Acquire | See enqueued data |
| slot CAS | Acq-Rel | Synchronize enqueue/dequeue |
| head/tail FAA | Relaxed | Reservation only |

## Thread Safety

| Operation | Progress |
|-----------|----------|
| Enqueue | Lock-free |
| Dequeue | Lock-free |

## Platform Support

| Platform | Status |
|----------|--------|
| x86-64 | Full support |
| ARM64 | Full support |
| x86 (32-bit) | Limited (pointer size) |

## References

- Nikolaev, R., & Ravindran, B. (2019). "A Scalable, Portable, and Memory-Efficient Lock-Free FIFO Queue."
