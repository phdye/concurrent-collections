# lcrq — Design Document

## Overview

`lcrq` implements the Linked Concurrent Ring Queue (LCRQ) by Morrison and Afek. This is a high-performance lock-free MPMC queue that uses double-width CAS (CMPXCHG16B on x86-64) for exceptional throughput. Due to its hardware requirements, LCRQ is only available on x86-64 platforms.

## Algorithm: Morrison-Afek LCRQ

### Key Innovations

1. **Double-Width CAS**: Uses 128-bit CAS to atomically update pointer+counter
2. **Linked Ring Buffers**: Multiple ring segments for unbounded growth
3. **Safe Pointer Validation**: Prevents ABA problem with version counter

### Why LCRQ?

- **Peak Performance**: Fastest known MPMC queue on x86-64
- **Low Contention**: Ring structure spreads operations across slots
- **Unbounded Option**: Can grow dynamically via linked segments

### Platform Restriction

**x86-64 only**: Requires CMPXCHG16B instruction. On other platforms, use SCQ.

```c
#if !defined(__x86_64__) && !defined(_M_X64)
#error "LCRQ requires x86-64 with CMPXCHG16B support"
#endif
```

## Data Structures

### 128-bit Atomic Structure

```c
typedef struct {
    uint64_t ptr;       // Pointer or index
    uint64_t ver;       // Version counter
} lcrq_pair_t;

// Must be 16-byte aligned for CMPXCHG16B
typedef _Atomic(lcrq_pair_t) atomic_pair_t __attribute__((aligned(16)));
```

### Slot Structure

```c
typedef struct lcrq_slot {
    atomic_pair_t entry;    // item pointer + cycle
    uint64_t pad[6];        // Pad to cache line
} lcrq_slot_t __attribute__((aligned(64)));
```

### Ring Segment

```c
#define LCRQ_RING_SIZE 4096  // Slots per ring

typedef struct lcrq_ring {
    _Atomic(uint64_t) head;
    _Atomic(uint64_t) tail;
    _Atomic(struct lcrq_ring *) next;
    lcrq_slot_t slots[LCRQ_RING_SIZE];
} lcrq_ring_t;
```

### Queue Structure

```c
typedef struct lcrq {
    _Atomic(lcrq_ring_t *) head_ring;
    _Atomic(lcrq_ring_t *) tail_ring;
    smr_domain_t *smr;
} lcrq_t;
```

## Core Operations

### Double-Width CAS

```c
static inline bool cas128(atomic_pair_t *target,
                          lcrq_pair_t *expected,
                          lcrq_pair_t desired) {
    return __atomic_compare_exchange_16(
        target,
        expected,
        desired,
        false,
        __ATOMIC_SEQ_CST,
        __ATOMIC_SEQ_CST
    );
}
```

### Enqueue Operation

```c
bool lcrq_enqueue(lcrq_t *q, void *item) {
    if (item == NULL) return false;

    smr_enter(q->smr);

    while (true) {
        lcrq_ring_t *ring = atomic_load(&q->tail_ring);

        if (lcrq_ring_enqueue(ring, item)) {
            smr_exit(q->smr);
            return true;
        }

        // Ring full, allocate new one
        lcrq_ring_t *new_ring = lcrq_ring_create();
        if (new_ring == NULL) {
            smr_exit(q->smr);
            return false;  // OOM
        }

        // Pre-enqueue to new ring
        lcrq_ring_enqueue(new_ring, item);

        // Link new ring
        lcrq_ring_t *expected = NULL;
        if (atomic_compare_exchange_strong(&ring->next, &expected, new_ring)) {
            atomic_compare_exchange_strong(&q->tail_ring, &ring, new_ring);
            smr_exit(q->smr);
            return true;
        }

        // Another thread beat us
        lcrq_ring_destroy(new_ring);
    }
}

static bool lcrq_ring_enqueue(lcrq_ring_t *ring, void *item) {
    while (true) {
        uint64_t tail = atomic_fetch_add(&ring->tail, 1);
        uint64_t cycle = tail / LCRQ_RING_SIZE;
        size_t index = tail % LCRQ_RING_SIZE;

        lcrq_slot_t *slot = &ring->slots[index];

        lcrq_pair_t entry;
        entry = atomic_load(&slot->entry);

        // Check if slot is available
        if (entry.ver < cycle * 2) {
            // Slot available
            lcrq_pair_t new_entry = {
                .ptr = (uint64_t)item,
                .ver = cycle * 2 + 1  // Odd = full
            };

            if (cas128(&slot->entry, &entry, new_entry)) {
                return true;
            }
        }

        // Check if ring is full
        uint64_t head = atomic_load(&ring->head);
        if (tail - head >= LCRQ_RING_SIZE) {
            return false;  // Ring full
        }
    }
}
```

### Dequeue Operation

```c
void *lcrq_dequeue(lcrq_t *q) {
    smr_enter(q->smr);

    while (true) {
        lcrq_ring_t *ring = atomic_load(&q->head_ring);

        void *item = lcrq_ring_dequeue(ring);
        if (item != NULL) {
            smr_exit(q->smr);
            return item;
        }

        // Ring empty, check for next
        lcrq_ring_t *next = atomic_load(&ring->next);
        if (next == NULL) {
            smr_exit(q->smr);
            return NULL;  // Queue empty
        }

        // Advance to next ring
        if (atomic_compare_exchange_strong(&q->head_ring, &ring, next)) {
            smr_retire(q->smr, ring, lcrq_ring_destroy);
        }
    }
}

static void *lcrq_ring_dequeue(lcrq_ring_t *ring) {
    while (true) {
        uint64_t head = atomic_fetch_add(&ring->head, 1);
        uint64_t cycle = head / LCRQ_RING_SIZE;
        size_t index = head % LCRQ_RING_SIZE;

        lcrq_slot_t *slot = &ring->slots[index];

        while (true) {
            lcrq_pair_t entry = atomic_load(&slot->entry);

            // Check if slot has item for this cycle
            if (entry.ver == cycle * 2 + 1) {
                // Item present
                lcrq_pair_t consumed = {
                    .ptr = 0,
                    .ver = (cycle + 1) * 2  // Even = empty, next cycle
                };

                if (cas128(&slot->entry, &entry, consumed)) {
                    return (void *)entry.ptr;
                }
                continue;
            }

            // Check if ring is empty
            uint64_t tail = atomic_load(&ring->tail);
            if (head >= tail) {
                return NULL;
            }

            // Item not ready yet
            cpu_pause();
        }
    }
}
```

## LCRQProfiler API

```python
from dataclasses import dataclass
from typing import Dict
from contextlib import contextmanager
import threading
import time

@dataclass
class LCRQStats:
    """Statistics for LCRQ operations."""

    total_enqueues: int = 0
    total_dequeues: int = 0
    failed_enqueues: int = 0
    failed_dequeues: int = 0

    # Ring metrics
    rings_allocated: int = 0
    rings_retired: int = 0
    current_rings: int = 0

    # CAS metrics (128-bit)
    cas128_attempts: int = 0
    cas128_failures: int = 0

    # Latency
    enqueue_latency_p50: float = 0.0
    enqueue_latency_p99: float = 0.0
    dequeue_latency_p50: float = 0.0
    dequeue_latency_p99: float = 0.0

    # Throughput
    throughput_combined: float = 0.0


class LCRQProfiler:
    """Profiler for LCRQ with ring tracking."""

    def __init__(self, *, track_latency=True, track_rings=True):
        self.track_latency = track_latency
        self.track_rings = track_rings
        self._lock = threading.Lock()
        self._reset()

    def _reset(self):
        self._enqueue_count = 0
        self._dequeue_count = 0
        self._enqueue_failed = 0
        self._dequeue_failed = 0
        self._rings_allocated = 0
        self._rings_retired = 0
        self._cas128_attempts = 0
        self._cas128_failures = 0
        self._latency_enqueue = []
        self._latency_dequeue = []
        self._start_time = time.time()

    def record_ring_alloc(self):
        with self._lock:
            self._rings_allocated += 1

    def record_ring_retire(self):
        with self._lock:
            self._rings_retired += 1

    @contextmanager
    def profile_enqueue(self):
        start = time.perf_counter_ns()
        ctx = {'cas_attempts': 0, 'cas_failures': 0, 'success': True}
        try:
            yield ctx
        finally:
            elapsed = time.perf_counter_ns() - start
            with self._lock:
                if ctx['success']:
                    self._enqueue_count += 1
                else:
                    self._enqueue_failed += 1
                self._cas128_attempts += ctx['cas_attempts']
                self._cas128_failures += ctx['cas_failures']
                if self.track_latency:
                    self._latency_enqueue.append(elapsed / 1000)

    @contextmanager
    def profile_dequeue(self):
        start = time.perf_counter_ns()
        ctx = {'cas_attempts': 0, 'cas_failures': 0, 'success': True}
        try:
            yield ctx
        finally:
            elapsed = time.perf_counter_ns() - start
            with self._lock:
                if ctx['success']:
                    self._dequeue_count += 1
                else:
                    self._dequeue_failed += 1
                self._cas128_attempts += ctx['cas_attempts']
                self._cas128_failures += ctx['cas_failures']
                if self.track_latency:
                    self._latency_dequeue.append(elapsed / 1000)

    def get_stats(self) -> LCRQStats:
        with self._lock:
            stats = LCRQStats()
            stats.total_enqueues = self._enqueue_count
            stats.total_dequeues = self._dequeue_count
            stats.failed_enqueues = self._enqueue_failed
            stats.failed_dequeues = self._dequeue_failed
            stats.rings_allocated = self._rings_allocated
            stats.rings_retired = self._rings_retired
            stats.current_rings = self._rings_allocated - self._rings_retired
            stats.cas128_attempts = self._cas128_attempts
            stats.cas128_failures = self._cas128_failures

            elapsed = time.time() - self._start_time
            if elapsed > 0:
                stats.throughput_combined = (
                    self._enqueue_count + self._dequeue_count) / elapsed

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

            return stats

    def compare_with_scq(self, scq_stats) -> Dict:
        """Compare LCRQ performance with SCQ."""
        lcrq_stats = self.get_stats()

        return {
            'throughput_ratio': lcrq_stats.throughput_combined /
                               max(scq_stats.enqueue_throughput + scq_stats.dequeue_throughput, 1),
            'latency_ratio_p50': lcrq_stats.enqueue_latency_p50 /
                                max(scq_stats.enqueue_latency_p50, 0.001),
            'recommendation': 'LCRQ' if lcrq_stats.throughput_combined >
                             (scq_stats.enqueue_throughput + scq_stats.dequeue_throughput) * 1.1
                             else 'SCQ (portability)'
        }
```

## Platform Detection

```c
bool lcrq_is_supported(void) {
#if defined(__x86_64__) || defined(_M_X64)
    // Check for CMPXCHG16B support
    unsigned int eax, ebx, ecx, edx;
    __cpuid(1, eax, ebx, ecx, edx);
    return (ecx & (1 << 13)) != 0;  // CX16 bit
#else
    return false;
#endif
}
```

## Performance Comparison

| Metric | LCRQ | SCQ |
|--------|------|-----|
| Throughput (8 threads) | ~10M ops/s | ~4M ops/s |
| Latency P99 | ~200ns | ~500ns |
| Memory per slot | 64 bytes | 16 bytes |
| Portability | x86-64 only | All platforms |

## References

- Morrison, A., & Afek, Y. (2013). "Fast Concurrent Queues for x86 Processors."
