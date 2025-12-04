# skiplist_lockfree — Design Document

## Overview

`skiplist_lockfree` implements Fraser's lock-free skip list algorithm, providing an ordered key-value store with O(log n) expected time complexity for insert, delete, and search operations. This implementation serves as the foundation for `SkipListMap` and `SkipListSet` in the public API.

## Algorithm: Fraser's Lock-Free Skip List

### Core Concept

The skip list is a probabilistic data structure consisting of multiple levels of linked lists. The bottom level contains all elements; each higher level is a subset with probabilistically smaller size. Lock-freedom is achieved through CAS operations on node pointers.

### Key Innovations

1. **Logical Deletion**: Nodes are first marked for deletion (logical) before physical removal
2. **CAS-based Insert**: New nodes inserted atomically using CAS on predecessor's next pointer
3. **Helping Mechanism**: Concurrent threads help complete pending deletions

## Data Structures

### Node Structure

```c
#define SKIPLIST_MAX_LEVEL 32

typedef struct skiplist_node {
    void *key;                          // Python object reference
    void *value;                        // Python object reference (NULL for sets)
    _Atomic(uint32_t) top_level;        // Highest level containing this node
    _Atomic(struct skiplist_node *) next[SKIPLIST_MAX_LEVEL];
    // Next pointers use low bit for mark flag
} skiplist_node_t;

// Mark bit extraction
#define IS_MARKED(ptr)    ((uintptr_t)(ptr) & 1)
#define MARK(ptr)         ((skiplist_node_t *)((uintptr_t)(ptr) | 1))
#define UNMARK(ptr)       ((skiplist_node_t *)((uintptr_t)(ptr) & ~1))
#define GET_PTR(ptr)      UNMARK(ptr)

typedef struct skiplist {
    skiplist_node_t *head;              // Sentinel head (never deleted)
    skiplist_node_t *tail;              // Sentinel tail (never deleted)
    _Atomic(size_t) count;              // Approximate element count
    comparator_t *comparator;           // Key comparison function
    smr_domain_t *smr;                  // SMR domain for safe reclamation
    uint32_t max_level;                 // Maximum level (typically 32)
    uint64_t random_seed;               // Per-list PRNG state
} skiplist_t;
```

### Level Selection

```c
// Geometric distribution for level selection
static inline uint32_t random_level(skiplist_t *sl) {
    uint32_t level = 1;
    uint64_t rand = xorshift64(&sl->random_seed);

    // P = 0.25 for each additional level
    while ((rand & 3) == 0 && level < sl->max_level) {
        level++;
        rand >>= 2;
    }
    return level;
}
```

## Core Operations

### Find Operation

The find operation locates a key and returns arrays of predecessors and successors at each level. This is the foundation for insert, delete, and search.

```c
typedef struct {
    skiplist_node_t *preds[SKIPLIST_MAX_LEVEL];
    skiplist_node_t *succs[SKIPLIST_MAX_LEVEL];
    bool found;
} skiplist_find_result_t;

bool skiplist_find(skiplist_t *sl, void *key, skiplist_find_result_t *result) {
    skiplist_node_t *pred, *curr, *succ;
    bool marked;

retry:
    pred = sl->head;

    for (int level = sl->max_level - 1; level >= 0; level--) {
        curr = GET_PTR(atomic_load(&pred->next[level]));

        while (true) {
            // Load curr's successor and check mark
            skiplist_node_t *raw = atomic_load(&curr->next[level]);
            succ = GET_PTR(raw);
            marked = IS_MARKED(raw);

            // Help remove marked nodes
            while (marked) {
                // CAS to physically remove marked node
                if (!atomic_compare_exchange_weak(&pred->next[level],
                        &curr, succ)) {
                    goto retry;  // Restart if CAS fails
                }

                // Successfully removed, move to next
                curr = succ;
                raw = atomic_load(&curr->next[level]);
                succ = GET_PTR(raw);
                marked = IS_MARKED(raw);
            }

            // Compare keys
            int cmp = comparator_compare(sl->comparator, curr->key, key);
            if (cmp < 0) {
                // curr->key < key, continue forward
                pred = curr;
                curr = succ;
            } else {
                // curr->key >= key, go down
                break;
            }
        }

        result->preds[level] = pred;
        result->succs[level] = curr;
    }

    // Check if found at bottom level
    int cmp = comparator_compare(sl->comparator,
                                  result->succs[0]->key, key);
    result->found = (cmp == 0 && result->succs[0] != sl->tail);
    return result->found;
}
```

### Insert Operation

```c
typedef enum {
    INSERT_SUCCESS,
    INSERT_EXISTS,
    INSERT_REPLACED
} skiplist_insert_result_t;

skiplist_insert_result_t skiplist_insert(skiplist_t *sl,
                                          void *key, void *value,
                                          bool replace_if_exists) {
    smr_enter(sl->smr);

    skiplist_node_t *new_node = NULL;
    uint32_t new_level = random_level(sl);
    skiplist_find_result_t find;

    while (true) {
        if (skiplist_find(sl, key, &find)) {
            // Key exists
            if (!replace_if_exists) {
                smr_exit(sl->smr);
                return INSERT_EXISTS;
            }

            // Replace value (CAS loop for atomicity)
            skiplist_node_t *existing = find.succs[0];
            void *old_val = atomic_load(&existing->value);
            while (!atomic_compare_exchange_weak(&existing->value,
                    &old_val, value)) {
                // Retry CAS
            }
            Py_INCREF(value);
            Py_DECREF(old_val);
            smr_exit(sl->smr);
            return INSERT_REPLACED;
        }

        // Allocate new node if needed
        if (new_node == NULL) {
            new_node = skiplist_node_alloc(sl, key, value, new_level);
            if (new_node == NULL) {
                smr_exit(sl->smr);
                return INSERT_ERROR;  // OOM
            }
        }

        // Set successors for new node
        for (uint32_t i = 0; i < new_level; i++) {
            new_node->next[i] = find.succs[i];
        }

        // CAS into bottom level first (linearization point)
        if (!atomic_compare_exchange_strong(&find.preds[0]->next[0],
                &find.succs[0], new_node)) {
            continue;  // Retry find
        }

        // Link into higher levels
        for (uint32_t i = 1; i < new_level; i++) {
            while (true) {
                skiplist_node_t *pred = find.preds[i];
                skiplist_node_t *succ = find.succs[i];

                // Check if new_node was marked while linking
                if (IS_MARKED(atomic_load(&new_node->next[i]))) {
                    // Node was deleted, stop linking
                    goto done;
                }

                if (atomic_compare_exchange_strong(&pred->next[i],
                        &succ, new_node)) {
                    break;  // Success, next level
                }

                // CAS failed, re-find
                skiplist_find(sl, key, &find);
            }
        }

done:
        atomic_fetch_add(&sl->count, 1);
        smr_exit(sl->smr);
        return INSERT_SUCCESS;
    }
}
```

### Delete Operation

```c
bool skiplist_delete(skiplist_t *sl, void *key, void **old_value) {
    smr_enter(sl->smr);

    skiplist_find_result_t find;
    skiplist_node_t *node_to_remove;

    while (true) {
        if (!skiplist_find(sl, key, &find)) {
            smr_exit(sl->smr);
            return false;  // Key not found
        }

        node_to_remove = find.succs[0];
        uint32_t top_level = atomic_load(&node_to_remove->top_level);

        // Mark from top level down to level 1
        for (int level = top_level - 1; level >= 1; level--) {
            skiplist_node_t *succ = atomic_load(&node_to_remove->next[level]);

            while (!IS_MARKED(succ)) {
                // Try to mark this level
                atomic_compare_exchange_weak(&node_to_remove->next[level],
                    &succ, MARK(succ));
            }
        }

        // Mark level 0 (linearization point for delete)
        skiplist_node_t *succ = atomic_load(&node_to_remove->next[0]);
        while (true) {
            if (IS_MARKED(succ)) {
                // Already marked by another thread
                smr_exit(sl->smr);
                return false;
            }

            if (atomic_compare_exchange_strong(&node_to_remove->next[0],
                    &succ, MARK(succ))) {
                // Successfully marked - we own the deletion
                break;
            }
        }

        // Return old value if requested
        if (old_value) {
            *old_value = node_to_remove->value;
            Py_INCREF(*old_value);
        }

        // Help physical removal
        skiplist_find(sl, key, &find);

        // Retire node for SMR
        smr_retire(sl->smr, node_to_remove, skiplist_node_free);

        atomic_fetch_sub(&sl->count, 1);
        smr_exit(sl->smr);
        return true;
    }
}
```

### Search Operation

```c
bool skiplist_search(skiplist_t *sl, void *key, void **value) {
    smr_enter(sl->smr);

    skiplist_node_t *pred = sl->head;
    skiplist_node_t *curr = NULL;
    skiplist_node_t *succ = NULL;

    for (int level = sl->max_level - 1; level >= 0; level--) {
        curr = GET_PTR(atomic_load(&pred->next[level]));

        while (true) {
            succ = GET_PTR(atomic_load(&curr->next[level]));
            bool marked = IS_MARKED(atomic_load(&curr->next[level]));

            // Skip marked nodes
            while (marked) {
                curr = succ;
                succ = GET_PTR(atomic_load(&curr->next[level]));
                marked = IS_MARKED(atomic_load(&curr->next[level]));
            }

            int cmp = comparator_compare(sl->comparator, curr->key, key);
            if (cmp < 0) {
                pred = curr;
                curr = succ;
            } else {
                break;
            }
        }
    }

    // Check bottom level
    int cmp = comparator_compare(sl->comparator, curr->key, key);
    if (cmp == 0 && curr != sl->tail) {
        if (value) {
            *value = curr->value;
            Py_INCREF(*value);
        }
        smr_exit(sl->smr);
        return true;
    }

    smr_exit(sl->smr);
    return false;
}
```

## Range Operations

### Range Iterator

```c
typedef struct skiplist_iter {
    skiplist_t *sl;
    skiplist_node_t *current;
    void *start_key;        // NULL for unbounded
    void *end_key;          // NULL for unbounded
    bool inclusive_end;
    bool exhausted;
} skiplist_iter_t;

skiplist_iter_t *skiplist_iter_range(skiplist_t *sl,
                                      void *start, void *end,
                                      bool inclusive_end) {
    skiplist_iter_t *iter = malloc(sizeof(skiplist_iter_t));
    iter->sl = sl;
    iter->start_key = start;
    iter->end_key = end;
    iter->inclusive_end = inclusive_end;
    iter->exhausted = false;

    // Find starting position
    smr_enter(sl->smr);

    if (start == NULL) {
        iter->current = GET_PTR(atomic_load(&sl->head->next[0]));
    } else {
        skiplist_find_result_t find;
        skiplist_find(sl, start, &find);
        iter->current = find.succs[0];
    }

    // Skip marked nodes
    while (iter->current != sl->tail &&
           IS_MARKED(atomic_load(&iter->current->next[0]))) {
        iter->current = GET_PTR(atomic_load(&iter->current->next[0]));
    }

    smr_exit(sl->smr);
    return iter;
}

bool skiplist_iter_next(skiplist_iter_t *iter, void **key, void **value) {
    if (iter->exhausted) return false;

    smr_enter(iter->sl->smr);

    // Skip marked nodes
    while (iter->current != iter->sl->tail &&
           IS_MARKED(atomic_load(&iter->current->next[0]))) {
        iter->current = GET_PTR(atomic_load(&iter->current->next[0]));
    }

    if (iter->current == iter->sl->tail) {
        iter->exhausted = true;
        smr_exit(iter->sl->smr);
        return false;
    }

    // Check end bound
    if (iter->end_key != NULL) {
        int cmp = comparator_compare(iter->sl->comparator,
                                      iter->current->key, iter->end_key);
        if (cmp > 0 || (cmp == 0 && !iter->inclusive_end)) {
            iter->exhausted = true;
            smr_exit(iter->sl->smr);
            return false;
        }
    }

    // Return current item
    *key = iter->current->key;
    Py_INCREF(*key);
    if (value && iter->current->value) {
        *value = iter->current->value;
        Py_INCREF(*value);
    }

    // Advance
    iter->current = GET_PTR(atomic_load(&iter->current->next[0]));

    smr_exit(iter->sl->smr);
    return true;
}
```

## Ordered Operations

### Floor/Ceiling Key

```c
// Find greatest key <= search_key
bool skiplist_floor_key(skiplist_t *sl, void *key, void **floor_key) {
    smr_enter(sl->smr);

    skiplist_node_t *pred = sl->head;
    skiplist_node_t *curr = NULL;
    skiplist_node_t *floor_node = NULL;

    for (int level = sl->max_level - 1; level >= 0; level--) {
        curr = GET_PTR(atomic_load(&pred->next[level]));

        while (curr != sl->tail) {
            if (IS_MARKED(atomic_load(&curr->next[level]))) {
                curr = GET_PTR(atomic_load(&curr->next[level]));
                continue;
            }

            int cmp = comparator_compare(sl->comparator, curr->key, key);
            if (cmp <= 0) {
                floor_node = curr;  // Candidate
                pred = curr;
                curr = GET_PTR(atomic_load(&curr->next[level]));
            } else {
                break;
            }
        }
    }

    if (floor_node != NULL && floor_node != sl->tail) {
        *floor_key = floor_node->key;
        Py_INCREF(*floor_key);
        smr_exit(sl->smr);
        return true;
    }

    smr_exit(sl->smr);
    return false;
}

// Find smallest key >= search_key
bool skiplist_ceiling_key(skiplist_t *sl, void *key, void **ceiling_key) {
    smr_enter(sl->smr);

    skiplist_find_result_t find;
    skiplist_find(sl, key, &find);

    skiplist_node_t *node = find.succs[0];

    // Skip marked nodes
    while (node != sl->tail && IS_MARKED(atomic_load(&node->next[0]))) {
        node = GET_PTR(atomic_load(&node->next[0]));
    }

    if (node != sl->tail) {
        *ceiling_key = node->key;
        Py_INCREF(*ceiling_key);
        smr_exit(sl->smr);
        return true;
    }

    smr_exit(sl->smr);
    return false;
}
```

## SMR Integration

### Node Lifecycle

```c
static void skiplist_node_free(void *ptr) {
    skiplist_node_t *node = (skiplist_node_t *)ptr;

    // Decrement Python references
    Py_DECREF(node->key);
    if (node->value != NULL) {
        Py_DECREF(node->value);
    }

    cc_free(node);
}
```

### Hazard Considerations

1. **Read-side Protection**: All traversals within `smr_enter()`/`smr_exit()`
2. **Deferred Free**: Deleted nodes retired via `smr_retire()`
3. **No Reuse Until Safe**: Freed memory only reused when no thread can access

## SkipListProfiler API

```python
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple
from contextlib import contextmanager
from collections import defaultdict
import threading
import time

@dataclass
class SkipListStats:
    """Comprehensive skip list performance statistics."""

    # Operation counts
    total_inserts: int = 0
    total_deletes: int = 0
    total_searches: int = 0
    total_range_queries: int = 0

    # CAS metrics
    total_cas_attempts: int = 0
    total_cas_failures: int = 0
    cas_failure_rate: float = 0.0

    # Retry metrics
    find_retries: int = 0
    insert_retries: int = 0
    delete_retries: int = 0

    # Level distribution
    level_distribution: Dict[int, int] = field(default_factory=dict)
    avg_node_level: float = 0.0
    max_level_used: int = 0

    # Traversal metrics
    avg_nodes_traversed_insert: float = 0.0
    avg_nodes_traversed_search: float = 0.0
    avg_nodes_traversed_delete: float = 0.0

    # Helping metrics (assisting other deletions)
    total_help_operations: int = 0
    marked_nodes_encountered: int = 0

    # Latency percentiles (microseconds)
    insert_latency_p50: float = 0.0
    insert_latency_p99: float = 0.0
    insert_latency_p999: float = 0.0
    search_latency_p50: float = 0.0
    search_latency_p99: float = 0.0
    search_latency_p999: float = 0.0
    delete_latency_p50: float = 0.0
    delete_latency_p99: float = 0.0
    delete_latency_p999: float = 0.0

    # Per-thread breakdown
    per_thread_stats: Dict[int, 'PerThreadStats'] = field(default_factory=dict)


@dataclass
class PerThreadStats:
    """Per-thread skip list statistics."""
    thread_id: int
    inserts: int = 0
    deletes: int = 0
    searches: int = 0
    cas_failures: int = 0
    retries: int = 0
    help_ops: int = 0


@dataclass
class TraversalTrace:
    """Detailed trace of a single operation."""
    operation: str  # 'insert', 'delete', 'search'
    key: any
    timestamp_start_ns: int
    timestamp_end_ns: int
    levels_visited: List[int]
    nodes_traversed: int
    cas_attempts: int
    cas_failures: int
    retries: int
    helped_deletions: int
    success: bool


class SkipListProfiler:
    """
    Comprehensive profiler for lock-free skip list operations.

    Features:
    - Operation latency tracking with percentiles
    - CAS success/failure monitoring
    - Retry analysis
    - Level distribution statistics
    - Traversal depth analysis
    - Per-thread breakdown
    - Operation tracing
    - Contention detection
    """

    def __init__(
        self,
        *,
        track_latency: bool = True,
        track_cas: bool = True,
        track_traversal: bool = True,
        track_levels: bool = True,
        track_per_thread: bool = False,
        enable_tracing: bool = False,
        trace_sample_rate: float = 0.01,
        contention_threshold: float = 0.1,  # CAS failure rate threshold
    ):
        """
        Initialize the SkipListProfiler.

        Args:
            track_latency: Enable operation latency measurement
            track_cas: Track CAS success/failure rates
            track_traversal: Count nodes traversed per operation
            track_levels: Track level distribution of nodes
            track_per_thread: Break down stats by thread
            enable_tracing: Enable detailed operation tracing
            trace_sample_rate: Fraction of operations to trace
            contention_threshold: CAS failure rate to flag as high contention
        """
        self.track_latency = track_latency
        self.track_cas = track_cas
        self.track_traversal = track_traversal
        self.track_levels = track_levels
        self.track_per_thread = track_per_thread
        self.enable_tracing = enable_tracing
        self.trace_sample_rate = trace_sample_rate
        self.contention_threshold = contention_threshold

        self._lock = threading.Lock()
        self._reset_counters()

    def _reset_counters(self):
        """Reset all internal counters."""
        self._insert_count = 0
        self._delete_count = 0
        self._search_count = 0
        self._range_query_count = 0

        self._cas_attempts = 0
        self._cas_failures = 0

        self._find_retries = 0
        self._insert_retries = 0
        self._delete_retries = 0

        self._level_counts = defaultdict(int)
        self._help_ops = 0
        self._marked_encountered = 0

        self._traversal_insert = []
        self._traversal_search = []
        self._traversal_delete = []

        self._latency_insert = []
        self._latency_search = []
        self._latency_delete = []

        self._per_thread = defaultdict(lambda: PerThreadStats(
            thread_id=threading.current_thread().ident))

        self._traces = []

    def attach(self, skiplist) -> None:
        """Attach profiler to a skip list instance."""
        skiplist._profiler = self

    def detach(self, skiplist) -> None:
        """Detach profiler from a skip list instance."""
        skiplist._profiler = None

    @contextmanager
    def profile_insert(self, key):
        """Context manager for profiling insert operations."""
        start = time.perf_counter_ns()
        ctx = {'cas_attempts': 0, 'cas_failures': 0, 'retries': 0,
               'nodes': 0, 'helped': 0, 'levels': []}

        try:
            yield ctx
        finally:
            elapsed = time.perf_counter_ns() - start

            with self._lock:
                self._insert_count += 1

                if self.track_latency:
                    self._latency_insert.append(elapsed / 1000)  # to μs

                if self.track_cas:
                    self._cas_attempts += ctx['cas_attempts']
                    self._cas_failures += ctx['cas_failures']

                self._insert_retries += ctx['retries']
                self._help_ops += ctx['helped']

                if self.track_traversal:
                    self._traversal_insert.append(ctx['nodes'])

                if self.track_per_thread:
                    tid = threading.current_thread().ident
                    self._per_thread[tid].inserts += 1
                    self._per_thread[tid].cas_failures += ctx['cas_failures']
                    self._per_thread[tid].retries += ctx['retries']

    @contextmanager
    def profile_search(self, key):
        """Context manager for profiling search operations."""
        start = time.perf_counter_ns()
        ctx = {'nodes': 0, 'marked_encountered': 0}

        try:
            yield ctx
        finally:
            elapsed = time.perf_counter_ns() - start

            with self._lock:
                self._search_count += 1

                if self.track_latency:
                    self._latency_search.append(elapsed / 1000)

                if self.track_traversal:
                    self._traversal_search.append(ctx['nodes'])

                self._marked_encountered += ctx['marked_encountered']

                if self.track_per_thread:
                    tid = threading.current_thread().ident
                    self._per_thread[tid].searches += 1

    @contextmanager
    def profile_delete(self, key):
        """Context manager for profiling delete operations."""
        start = time.perf_counter_ns()
        ctx = {'cas_attempts': 0, 'cas_failures': 0, 'retries': 0,
               'nodes': 0, 'helped': 0}

        try:
            yield ctx
        finally:
            elapsed = time.perf_counter_ns() - start

            with self._lock:
                self._delete_count += 1

                if self.track_latency:
                    self._latency_delete.append(elapsed / 1000)

                if self.track_cas:
                    self._cas_attempts += ctx['cas_attempts']
                    self._cas_failures += ctx['cas_failures']

                self._delete_retries += ctx['retries']
                self._help_ops += ctx['helped']

                if self.track_traversal:
                    self._traversal_delete.append(ctx['nodes'])

                if self.track_per_thread:
                    tid = threading.current_thread().ident
                    self._per_thread[tid].deletes += 1
                    self._per_thread[tid].cas_failures += ctx['cas_failures']

    def record_level(self, level: int) -> None:
        """Record the level of a newly inserted node."""
        if self.track_levels:
            with self._lock:
                self._level_counts[level] += 1

    def get_stats(self) -> SkipListStats:
        """Get current statistics snapshot."""
        with self._lock:
            stats = SkipListStats()

            stats.total_inserts = self._insert_count
            stats.total_deletes = self._delete_count
            stats.total_searches = self._search_count
            stats.total_range_queries = self._range_query_count

            stats.total_cas_attempts = self._cas_attempts
            stats.total_cas_failures = self._cas_failures
            if self._cas_attempts > 0:
                stats.cas_failure_rate = self._cas_failures / self._cas_attempts

            stats.find_retries = self._find_retries
            stats.insert_retries = self._insert_retries
            stats.delete_retries = self._delete_retries

            stats.level_distribution = dict(self._level_counts)
            if self._level_counts:
                total_nodes = sum(self._level_counts.values())
                total_levels = sum(l * c for l, c in self._level_counts.items())
                stats.avg_node_level = total_levels / total_nodes
                stats.max_level_used = max(self._level_counts.keys())

            if self._traversal_insert:
                stats.avg_nodes_traversed_insert = sum(self._traversal_insert) / len(self._traversal_insert)
            if self._traversal_search:
                stats.avg_nodes_traversed_search = sum(self._traversal_search) / len(self._traversal_search)
            if self._traversal_delete:
                stats.avg_nodes_traversed_delete = sum(self._traversal_delete) / len(self._traversal_delete)

            stats.total_help_operations = self._help_ops
            stats.marked_nodes_encountered = self._marked_encountered

            # Compute percentiles
            if self._latency_insert:
                sorted_lat = sorted(self._latency_insert)
                n = len(sorted_lat)
                stats.insert_latency_p50 = sorted_lat[int(n * 0.50)]
                stats.insert_latency_p99 = sorted_lat[min(int(n * 0.99), n-1)]
                stats.insert_latency_p999 = sorted_lat[min(int(n * 0.999), n-1)]

            if self._latency_search:
                sorted_lat = sorted(self._latency_search)
                n = len(sorted_lat)
                stats.search_latency_p50 = sorted_lat[int(n * 0.50)]
                stats.search_latency_p99 = sorted_lat[min(int(n * 0.99), n-1)]
                stats.search_latency_p999 = sorted_lat[min(int(n * 0.999), n-1)]

            if self._latency_delete:
                sorted_lat = sorted(self._latency_delete)
                n = len(sorted_lat)
                stats.delete_latency_p50 = sorted_lat[int(n * 0.50)]
                stats.delete_latency_p99 = sorted_lat[min(int(n * 0.99), n-1)]
                stats.delete_latency_p999 = sorted_lat[min(int(n * 0.999), n-1)]

            if self.track_per_thread:
                stats.per_thread_stats = dict(self._per_thread)

            return stats

    def detect_contention(self) -> Dict[str, any]:
        """Analyze contention patterns and return recommendations."""
        stats = self.get_stats()
        issues = []
        recommendations = []

        # Check CAS failure rate
        if stats.cas_failure_rate > self.contention_threshold:
            issues.append(f"High CAS failure rate: {stats.cas_failure_rate:.1%}")
            recommendations.append("Consider increasing backoff or reducing concurrency")

        # Check retry rates
        total_ops = stats.total_inserts + stats.total_deletes
        if total_ops > 0:
            retry_rate = (stats.insert_retries + stats.delete_retries) / total_ops
            if retry_rate > 0.5:
                issues.append(f"High retry rate: {retry_rate:.1f} retries/op")
                recommendations.append("Hot spots detected - consider key distribution")

        # Check help operation frequency
        if stats.total_deletes > 0:
            help_ratio = stats.total_help_operations / stats.total_deletes
            if help_ratio > 2.0:
                issues.append(f"High helping overhead: {help_ratio:.1f}x")
                recommendations.append("Many concurrent deletions - consider batching")

        return {
            'has_issues': len(issues) > 0,
            'issues': issues,
            'recommendations': recommendations,
            'cas_failure_rate': stats.cas_failure_rate,
            'avg_retries': (stats.insert_retries + stats.delete_retries) / max(total_ops, 1),
        }

    def export_prometheus(self) -> str:
        """Export metrics in Prometheus format."""
        stats = self.get_stats()
        lines = [
            '# HELP skiplist_operations_total Total skip list operations',
            '# TYPE skiplist_operations_total counter',
            f'skiplist_operations_total{{op="insert"}} {stats.total_inserts}',
            f'skiplist_operations_total{{op="delete"}} {stats.total_deletes}',
            f'skiplist_operations_total{{op="search"}} {stats.total_searches}',
            '',
            '# HELP skiplist_cas_total Total CAS operations',
            '# TYPE skiplist_cas_total counter',
            f'skiplist_cas_total{{result="success"}} {stats.total_cas_attempts - stats.total_cas_failures}',
            f'skiplist_cas_total{{result="failure"}} {stats.total_cas_failures}',
            '',
            '# HELP skiplist_latency_microseconds Operation latency',
            '# TYPE skiplist_latency_microseconds summary',
            f'skiplist_latency_microseconds{{op="insert",quantile="0.5"}} {stats.insert_latency_p50:.2f}',
            f'skiplist_latency_microseconds{{op="insert",quantile="0.99"}} {stats.insert_latency_p99:.2f}',
            f'skiplist_latency_microseconds{{op="search",quantile="0.5"}} {stats.search_latency_p50:.2f}',
            f'skiplist_latency_microseconds{{op="search",quantile="0.99"}} {stats.search_latency_p99:.2f}',
            '',
            '# HELP skiplist_avg_level Average node level',
            '# TYPE skiplist_avg_level gauge',
            f'skiplist_avg_level {stats.avg_node_level:.2f}',
        ]
        return '\n'.join(lines)

    def reset(self) -> None:
        """Reset all profiler state."""
        with self._lock:
            self._reset_counters()
```

## Thread Safety

| Operation | Progress Guarantee | Notes |
|-----------|-------------------|-------|
| Insert | Lock-free | CAS may fail, always retries successfully |
| Delete | Lock-free | Two-phase: mark then physical remove |
| Search | Wait-free | Read-only traversal, no CAS needed |
| Range iter | Weakly consistent | May see concurrent modifications |

## Memory Ordering

| Operation | Memory Order | Rationale |
|-----------|-------------|-----------|
| Node allocation | N/A | Single-threaded before publish |
| next[] store (new node) | Release | Publish node contents |
| next[] load | Acquire | Observe node contents |
| Mark bit CAS | Acq-Rel | Synchronize deletion |
| Value replace CAS | Acq-Rel | Atomic value update |

## Configuration

```c
typedef struct skiplist_config {
    uint32_t max_level;         // Default: 32
    float level_probability;    // Default: 0.25
    bool enable_profiling;      // Default: false
    size_t initial_capacity;    // Hint for allocator (unused)
} skiplist_config_t;

static const skiplist_config_t SKIPLIST_DEFAULT_CONFIG = {
    .max_level = 32,
    .level_probability = 0.25f,
    .enable_profiling = false,
    .initial_capacity = 0,
};
```

## Platform Considerations

| Platform | Notes |
|----------|-------|
| x86-64 | Strong memory model reduces fence overhead |
| ARM64 | Explicit barriers needed; use LSE atomics when available |
| Windows | MSVC intrinsics for atomics |

## References

- Fraser, K. (2004). "Practical Lock-Freedom." PhD Thesis, University of Cambridge.
- Herlihy, M., & Shavit, N. (2012). "The Art of Multiprocessor Programming." Chapter 14.
- Pugh, W. (1990). "Skip Lists: A Probabilistic Alternative to Balanced Trees."
