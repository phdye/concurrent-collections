# skiplist_locked — Design Document

## Overview

`skiplist_locked` implements a fine-grained locked skip list for use when the GIL is enabled or when lock-free algorithms are not preferred. This provides the same functionality as `skiplist_lockfree` but uses per-node locks instead of CAS operations, offering better worst-case latency at the cost of reduced scalability.

## Design Rationale

### Why Fine-Grained Locking?

1. **GIL Compatibility**: When Python's GIL is enabled, lock-free algorithms provide no benefit
2. **Predictable Latency**: No CAS retry loops means bounded operation time
3. **Simpler Debugging**: Lock-based code easier to reason about
4. **Fallback Option**: Works on all platforms without atomic primitives

### Lock Strategy

We use **hand-over-hand locking** (also called lock coupling):
- Acquire lock on predecessor before releasing lock on current node
- Prevents race conditions during traversal
- Allows concurrent access to disjoint parts of the list

## Data Structures

### Node Structure

```c
#define SKIPLIST_MAX_LEVEL 32

typedef struct skiplist_locked_node {
    void *key;                          // Python object reference
    void *value;                        // Python object reference
    uint32_t top_level;                 // Highest level containing this node
    bool marked;                        // Logically deleted flag
    pthread_mutex_t lock;               // Per-node lock
    struct skiplist_locked_node *next[SKIPLIST_MAX_LEVEL];
} skiplist_locked_node_t;

typedef struct skiplist_locked {
    skiplist_locked_node_t *head;       // Sentinel head
    skiplist_locked_node_t *tail;       // Sentinel tail
    size_t count;                       // Element count
    pthread_mutex_t count_lock;         // Lock for count updates
    comparator_t *comparator;           // Key comparison
    uint32_t max_level;                 // Maximum level
    uint64_t random_seed;               // PRNG state
} skiplist_locked_t;
```

### Lock Ordering

To prevent deadlocks, locks are always acquired in traversal order:
1. Lock predecessor at level n
2. Lock successor at level n
3. Perform operation
4. Release in reverse order (or hand-over-hand for traversal)

## Core Operations

### Find with Hand-Over-Hand Locking

```c
typedef struct {
    skiplist_locked_node_t *preds[SKIPLIST_MAX_LEVEL];
    skiplist_locked_node_t *succs[SKIPLIST_MAX_LEVEL];
    bool found;
    bool locks_held;  // Whether preds[0] and succs[0] are locked
} skiplist_locked_find_result_t;

bool skiplist_locked_find(skiplist_locked_t *sl, void *key,
                          skiplist_locked_find_result_t *result,
                          bool acquire_locks) {
    skiplist_locked_node_t *pred, *curr;

    pred = sl->head;

    for (int level = sl->max_level - 1; level >= 0; level--) {
        curr = pred->next[level];

        // Traverse at this level
        while (curr != sl->tail) {
            int cmp = comparator_compare(sl->comparator, curr->key, key);

            if (cmp < 0) {
                pred = curr;
                curr = curr->next[level];
            } else {
                break;
            }
        }

        result->preds[level] = pred;
        result->succs[level] = curr;
    }

    // Acquire locks at level 0 for modifications
    if (acquire_locks) {
        pthread_mutex_lock(&result->preds[0]->lock);
        pthread_mutex_lock(&result->succs[0]->lock);
        result->locks_held = true;

        // Validate: check predecessor still points to successor
        if (result->preds[0]->next[0] != result->succs[0] ||
            result->preds[0]->marked ||
            result->succs[0]->marked) {
            // Validation failed, release and retry
            pthread_mutex_unlock(&result->succs[0]->lock);
            pthread_mutex_unlock(&result->preds[0]->lock);
            result->locks_held = false;
            return skiplist_locked_find(sl, key, result, true);  // Retry
        }
    }

    // Check if found
    int cmp = comparator_compare(sl->comparator,
                                  result->succs[0]->key, key);
    result->found = (cmp == 0 && result->succs[0] != sl->tail &&
                     !result->succs[0]->marked);

    return result->found;
}
```

### Insert Operation

```c
typedef enum {
    INSERT_SUCCESS,
    INSERT_EXISTS,
    INSERT_REPLACED,
    INSERT_ERROR
} skiplist_locked_insert_result_t;

skiplist_locked_insert_result_t skiplist_locked_insert(
    skiplist_locked_t *sl,
    void *key,
    void *value,
    bool replace_if_exists
) {
    skiplist_locked_find_result_t find;
    uint32_t new_level = random_level(sl);
    skiplist_locked_node_t *new_node = NULL;

    while (true) {
        if (skiplist_locked_find(sl, key, &find, true)) {
            // Key exists
            if (!replace_if_exists) {
                pthread_mutex_unlock(&find.succs[0]->lock);
                pthread_mutex_unlock(&find.preds[0]->lock);
                return INSERT_EXISTS;
            }

            // Replace value
            void *old_value = find.succs[0]->value;
            find.succs[0]->value = value;
            Py_INCREF(value);
            Py_DECREF(old_value);

            pthread_mutex_unlock(&find.succs[0]->lock);
            pthread_mutex_unlock(&find.preds[0]->lock);
            return INSERT_REPLACED;
        }

        // Key not found, insert new node
        if (new_node == NULL) {
            new_node = skiplist_locked_node_alloc(sl, key, value, new_level);
            if (new_node == NULL) {
                if (find.locks_held) {
                    pthread_mutex_unlock(&find.succs[0]->lock);
                    pthread_mutex_unlock(&find.preds[0]->lock);
                }
                return INSERT_ERROR;
            }
        }

        // Lock higher levels and validate
        bool valid = true;
        int locked_level = 0;

        for (int level = 1; level < new_level && valid; level++) {
            pthread_mutex_lock(&find.preds[level]->lock);
            pthread_mutex_lock(&find.succs[level]->lock);
            locked_level = level;

            // Validate
            if (find.preds[level]->next[level] != find.succs[level] ||
                find.preds[level]->marked ||
                find.succs[level]->marked) {
                valid = false;
            }
        }

        if (!valid) {
            // Release all locks and retry
            for (int level = locked_level; level >= 0; level--) {
                pthread_mutex_unlock(&find.succs[level]->lock);
                pthread_mutex_unlock(&find.preds[level]->lock);
            }
            continue;  // Retry find
        }

        // All locks held and validated, perform insert
        for (int level = 0; level < new_level; level++) {
            new_node->next[level] = find.succs[level];
            find.preds[level]->next[level] = new_node;
        }

        // Update count
        pthread_mutex_lock(&sl->count_lock);
        sl->count++;
        pthread_mutex_unlock(&sl->count_lock);

        // Release all locks
        for (int level = new_level - 1; level >= 0; level--) {
            pthread_mutex_unlock(&find.succs[level]->lock);
            pthread_mutex_unlock(&find.preds[level]->lock);
        }

        return INSERT_SUCCESS;
    }
}
```

### Delete Operation

```c
bool skiplist_locked_delete(skiplist_locked_t *sl, void *key,
                            void **old_value) {
    skiplist_locked_find_result_t find;

    while (true) {
        if (!skiplist_locked_find(sl, key, &find, true)) {
            // Key not found
            if (find.locks_held) {
                pthread_mutex_unlock(&find.succs[0]->lock);
                pthread_mutex_unlock(&find.preds[0]->lock);
            }
            return false;
        }

        skiplist_locked_node_t *node_to_remove = find.succs[0];
        uint32_t top_level = node_to_remove->top_level;

        // Lock higher levels
        bool valid = true;
        int locked_level = 0;

        for (int level = 1; level < top_level && valid; level++) {
            pthread_mutex_lock(&find.preds[level]->lock);
            locked_level = level;

            // Validate
            if (find.preds[level]->next[level] != node_to_remove ||
                find.preds[level]->marked) {
                valid = false;
            }
        }

        if (!valid) {
            // Release and retry
            for (int level = locked_level; level >= 0; level--) {
                if (level > 0) {
                    pthread_mutex_unlock(&find.preds[level]->lock);
                }
            }
            pthread_mutex_unlock(&find.succs[0]->lock);
            pthread_mutex_unlock(&find.preds[0]->lock);
            continue;
        }

        // Mark node as deleted (prevents concurrent insertion)
        node_to_remove->marked = true;

        // Unlink from all levels
        for (int level = top_level - 1; level >= 0; level--) {
            find.preds[level]->next[level] = node_to_remove->next[level];
        }

        // Save old value if requested
        if (old_value) {
            *old_value = node_to_remove->value;
            Py_INCREF(*old_value);
        }

        // Update count
        pthread_mutex_lock(&sl->count_lock);
        sl->count--;
        pthread_mutex_unlock(&sl->count_lock);

        // Release locks
        for (int level = top_level - 1; level >= 0; level--) {
            if (level > 0) {
                pthread_mutex_unlock(&find.preds[level]->lock);
            }
        }
        pthread_mutex_unlock(&find.succs[0]->lock);
        pthread_mutex_unlock(&find.preds[0]->lock);

        // Free node (immediate - no SMR needed with locks)
        skiplist_locked_node_free(node_to_remove);

        return true;
    }
}
```

### Search Operation (Lock-Free Read)

```c
bool skiplist_locked_search(skiplist_locked_t *sl, void *key, void **value) {
    // Optimistic read - no locks needed for search
    // Works because:
    // 1. marked flag checked before returning
    // 2. Node not freed until all locks released

    skiplist_locked_node_t *pred = sl->head;
    skiplist_locked_node_t *curr = NULL;

    for (int level = sl->max_level - 1; level >= 0; level--) {
        curr = pred->next[level];

        while (curr != sl->tail) {
            // Memory barrier to ensure we see consistent state
            __atomic_thread_fence(__ATOMIC_ACQUIRE);

            if (curr->marked) {
                // Node being deleted, skip it
                curr = curr->next[level];
                continue;
            }

            int cmp = comparator_compare(sl->comparator, curr->key, key);

            if (cmp < 0) {
                pred = curr;
                curr = curr->next[level];
            } else {
                break;
            }
        }
    }

    // Check bottom level
    if (curr != sl->tail && !curr->marked) {
        int cmp = comparator_compare(sl->comparator, curr->key, key);
        if (cmp == 0) {
            if (value) {
                *value = curr->value;
                Py_INCREF(*value);
            }
            return true;
        }
    }

    return false;
}
```

## Range Operations

### Range Iterator

```c
typedef struct skiplist_locked_iter {
    skiplist_locked_t *sl;
    skiplist_locked_node_t *current;
    void *end_key;
    bool inclusive_end;
    bool exhausted;
} skiplist_locked_iter_t;

skiplist_locked_iter_t *skiplist_locked_iter_range(
    skiplist_locked_t *sl,
    void *start,
    void *end,
    bool inclusive_end
) {
    skiplist_locked_iter_t *iter = malloc(sizeof(skiplist_locked_iter_t));
    iter->sl = sl;
    iter->end_key = end;
    iter->inclusive_end = inclusive_end;
    iter->exhausted = false;

    // Find start position
    if (start == NULL) {
        iter->current = sl->head->next[0];
    } else {
        skiplist_locked_find_result_t find;
        skiplist_locked_find(sl, start, &find, false);
        iter->current = find.succs[0];
    }

    // Skip marked nodes
    while (iter->current != sl->tail && iter->current->marked) {
        iter->current = iter->current->next[0];
    }

    return iter;
}

bool skiplist_locked_iter_next(skiplist_locked_iter_t *iter,
                               void **key, void **value) {
    if (iter->exhausted || iter->current == iter->sl->tail) {
        iter->exhausted = true;
        return false;
    }

    // Skip marked nodes
    while (iter->current != iter->sl->tail && iter->current->marked) {
        iter->current = iter->current->next[0];
    }

    if (iter->current == iter->sl->tail) {
        iter->exhausted = true;
        return false;
    }

    // Check end bound
    if (iter->end_key != NULL) {
        int cmp = comparator_compare(iter->sl->comparator,
                                      iter->current->key, iter->end_key);
        if (cmp > 0 || (cmp == 0 && !iter->inclusive_end)) {
            iter->exhausted = true;
            return false;
        }
    }

    // Return current
    *key = iter->current->key;
    Py_INCREF(*key);
    if (value && iter->current->value) {
        *value = iter->current->value;
        Py_INCREF(*value);
    }

    iter->current = iter->current->next[0];
    return true;
}
```

## Memory Management

### No SMR Required

Unlike the lock-free variant, the locked implementation can use immediate deallocation:
- Locks ensure no concurrent access during deletion
- Node freed immediately after unlinking
- Simpler memory management

### Node Allocation

```c
static skiplist_locked_node_t *skiplist_locked_node_alloc(
    skiplist_locked_t *sl,
    void *key,
    void *value,
    uint32_t level
) {
    size_t size = sizeof(skiplist_locked_node_t) +
                  (level - 1) * sizeof(skiplist_locked_node_t *);

    skiplist_locked_node_t *node = cc_alloc(size);
    if (node == NULL) return NULL;

    node->key = key;
    node->value = value;
    node->top_level = level;
    node->marked = false;

    pthread_mutex_init(&node->lock, NULL);

    Py_INCREF(key);
    if (value) Py_INCREF(value);

    return node;
}

static void skiplist_locked_node_free(skiplist_locked_node_t *node) {
    pthread_mutex_destroy(&node->lock);
    Py_DECREF(node->key);
    if (node->value) Py_DECREF(node->value);
    cc_free(node);
}
```

## SkipListLockedProfiler API

```python
from dataclasses import dataclass, field
from typing import Dict, List, Optional
from contextlib import contextmanager
import threading
import time

@dataclass
class SkipListLockedStats:
    """Statistics for locked skip list operations."""

    # Operation counts
    total_inserts: int = 0
    total_deletes: int = 0
    total_searches: int = 0
    total_range_queries: int = 0

    # Lock contention metrics
    total_lock_acquisitions: int = 0
    total_lock_contentions: int = 0
    contention_rate: float = 0.0

    # Retry metrics (validation failures)
    validation_failures: int = 0
    avg_retries_per_insert: float = 0.0
    avg_retries_per_delete: float = 0.0

    # Lock hold times (microseconds)
    avg_lock_hold_time: float = 0.0
    max_lock_hold_time: float = 0.0

    # Latency percentiles (microseconds)
    insert_latency_p50: float = 0.0
    insert_latency_p99: float = 0.0
    search_latency_p50: float = 0.0
    search_latency_p99: float = 0.0
    delete_latency_p50: float = 0.0
    delete_latency_p99: float = 0.0

    # Per-thread breakdown
    per_thread_stats: Dict[int, 'PerThreadLockedStats'] = field(default_factory=dict)


@dataclass
class PerThreadLockedStats:
    """Per-thread statistics."""
    thread_id: int
    operations: int = 0
    lock_acquisitions: int = 0
    contentions: int = 0
    retries: int = 0


class SkipListLockedProfiler:
    """
    Profiler for fine-grained locked skip list.

    Features:
    - Lock contention monitoring
    - Validation failure tracking
    - Lock hold time measurement
    - Latency percentiles
    - Per-thread breakdown
    """

    def __init__(
        self,
        *,
        track_latency: bool = True,
        track_contention: bool = True,
        track_hold_time: bool = False,
        track_per_thread: bool = False,
        high_contention_threshold: float = 0.1,
    ):
        self.track_latency = track_latency
        self.track_contention = track_contention
        self.track_hold_time = track_hold_time
        self.track_per_thread = track_per_thread
        self.high_contention_threshold = high_contention_threshold

        self._lock = threading.Lock()
        self._reset_counters()

    def _reset_counters(self):
        self._insert_count = 0
        self._delete_count = 0
        self._search_count = 0

        self._lock_acquisitions = 0
        self._lock_contentions = 0
        self._validation_failures = 0

        self._insert_retries = []
        self._delete_retries = []
        self._hold_times = []

        self._latency_insert = []
        self._latency_search = []
        self._latency_delete = []

        self._per_thread = {}

    @contextmanager
    def profile_insert(self):
        """Profile an insert operation."""
        start = time.perf_counter_ns()
        ctx = {'retries': 0, 'lock_acquisitions': 0, 'contentions': 0}

        try:
            yield ctx
        finally:
            elapsed = time.perf_counter_ns() - start

            with self._lock:
                self._insert_count += 1
                self._insert_retries.append(ctx['retries'])
                self._lock_acquisitions += ctx['lock_acquisitions']
                self._lock_contentions += ctx['contentions']
                self._validation_failures += ctx['retries']

                if self.track_latency:
                    self._latency_insert.append(elapsed / 1000)

                if self.track_per_thread:
                    tid = threading.current_thread().ident
                    if tid not in self._per_thread:
                        self._per_thread[tid] = PerThreadLockedStats(thread_id=tid)
                    self._per_thread[tid].operations += 1
                    self._per_thread[tid].lock_acquisitions += ctx['lock_acquisitions']
                    self._per_thread[tid].contentions += ctx['contentions']
                    self._per_thread[tid].retries += ctx['retries']

    @contextmanager
    def profile_search(self):
        """Profile a search operation."""
        start = time.perf_counter_ns()

        try:
            yield
        finally:
            elapsed = time.perf_counter_ns() - start

            with self._lock:
                self._search_count += 1
                if self.track_latency:
                    self._latency_search.append(elapsed / 1000)

    @contextmanager
    def profile_delete(self):
        """Profile a delete operation."""
        start = time.perf_counter_ns()
        ctx = {'retries': 0, 'lock_acquisitions': 0, 'contentions': 0}

        try:
            yield ctx
        finally:
            elapsed = time.perf_counter_ns() - start

            with self._lock:
                self._delete_count += 1
                self._delete_retries.append(ctx['retries'])
                self._lock_acquisitions += ctx['lock_acquisitions']
                self._lock_contentions += ctx['contentions']

                if self.track_latency:
                    self._latency_delete.append(elapsed / 1000)

    @contextmanager
    def profile_lock_hold(self):
        """Measure lock hold duration."""
        if not self.track_hold_time:
            yield
            return

        start = time.perf_counter_ns()
        try:
            yield
        finally:
            elapsed = (time.perf_counter_ns() - start) / 1000
            with self._lock:
                self._hold_times.append(elapsed)

    def get_stats(self) -> SkipListLockedStats:
        """Get current statistics."""
        with self._lock:
            stats = SkipListLockedStats()

            stats.total_inserts = self._insert_count
            stats.total_deletes = self._delete_count
            stats.total_searches = self._search_count

            stats.total_lock_acquisitions = self._lock_acquisitions
            stats.total_lock_contentions = self._lock_contentions
            if self._lock_acquisitions > 0:
                stats.contention_rate = self._lock_contentions / self._lock_acquisitions

            stats.validation_failures = self._validation_failures

            if self._insert_retries:
                stats.avg_retries_per_insert = sum(self._insert_retries) / len(self._insert_retries)
            if self._delete_retries:
                stats.avg_retries_per_delete = sum(self._delete_retries) / len(self._delete_retries)

            if self._hold_times:
                stats.avg_lock_hold_time = sum(self._hold_times) / len(self._hold_times)
                stats.max_lock_hold_time = max(self._hold_times)

            # Percentiles
            if self._latency_insert:
                sorted_lat = sorted(self._latency_insert)
                n = len(sorted_lat)
                stats.insert_latency_p50 = sorted_lat[int(n * 0.50)]
                stats.insert_latency_p99 = sorted_lat[min(int(n * 0.99), n-1)]

            if self._latency_search:
                sorted_lat = sorted(self._latency_search)
                n = len(sorted_lat)
                stats.search_latency_p50 = sorted_lat[int(n * 0.50)]
                stats.search_latency_p99 = sorted_lat[min(int(n * 0.99), n-1)]

            if self._latency_delete:
                sorted_lat = sorted(self._latency_delete)
                n = len(sorted_lat)
                stats.delete_latency_p50 = sorted_lat[int(n * 0.50)]
                stats.delete_latency_p99 = sorted_lat[min(int(n * 0.99), n-1)]

            if self.track_per_thread:
                stats.per_thread_stats = dict(self._per_thread)

            return stats

    def analyze_contention(self) -> Dict:
        """Analyze lock contention patterns."""
        stats = self.get_stats()
        issues = []
        recommendations = []

        if stats.contention_rate > self.high_contention_threshold:
            issues.append(f"High lock contention: {stats.contention_rate:.1%}")
            recommendations.append("Consider using lock-free variant")

        if stats.avg_retries_per_insert > 0.5:
            issues.append(f"High validation failures: {stats.avg_retries_per_insert:.2f} retries/insert")
            recommendations.append("Hot spots detected in key space")

        if stats.max_lock_hold_time > 1000:  # 1ms
            issues.append(f"Long lock holds: {stats.max_lock_hold_time:.0f}μs max")
            recommendations.append("Check for expensive comparators")

        return {
            'has_issues': len(issues) > 0,
            'issues': issues,
            'recommendations': recommendations,
            'contention_rate': stats.contention_rate,
        }

    def reset(self):
        """Reset all counters."""
        with self._lock:
            self._reset_counters()
```

## Thread Safety

| Operation | Safety | Lock Scope |
|-----------|--------|------------|
| Insert | Thread-safe | Predecessors/successors at affected levels |
| Delete | Thread-safe | Same as insert |
| Search | Thread-safe | Lock-free (optimistic read) |
| Range iter | Weakly consistent | Snapshot at iteration start |

## Performance Characteristics

### Complexity

| Operation | Average | Worst Case |
|-----------|---------|------------|
| Insert | O(log n) | O(n) with contention |
| Delete | O(log n) | O(n) with contention |
| Search | O(log n) | O(n) |

### Scalability

| Threads | Read-heavy | Write-heavy |
|---------|------------|-------------|
| 1 | 1x | 1x |
| 2 | ~1.8x | ~1.5x |
| 4 | ~3x | ~2x |
| 8 | ~4x | ~2.5x |
| 16 | ~5x | ~3x |

Note: Lock-free variant scales better for write-heavy workloads.

## Configuration

```c
typedef struct skiplist_locked_config {
    uint32_t max_level;             // Default: 32
    float level_probability;        // Default: 0.25
    bool enable_profiling;          // Default: false
} skiplist_locked_config_t;
```

## Comparison with Lock-Free Variant

| Aspect | skiplist_locked | skiplist_lockfree |
|--------|-----------------|-------------------|
| Progress guarantee | Blocking | Lock-free |
| Read scalability | Good | Excellent |
| Write scalability | Moderate | Good |
| Latency variance | Low | Higher (CAS retries) |
| Memory management | Immediate free | SMR required |
| Complexity | Lower | Higher |
| Debug difficulty | Easier | Harder |

## References

- Herlihy, M., & Shavit, N. (2012). "The Art of Multiprocessor Programming." Chapter 9.
- Pugh, W. (1990). "Concurrent Maintenance of Skip Lists."
