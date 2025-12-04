# bst_lockfree — Design Document

## Overview

`bst_lockfree` implements the Natarajan-Mittal lock-free external binary search tree. This algorithm provides linearizable insert, delete, and search operations without locks, using CAS operations for synchronization. The tree serves as the foundation for `TreeMap` and `TreeSet` in the public API.

## Algorithm: Natarajan-Mittal External BST

### Key Concepts

1. **External Tree**: Keys stored only in leaf nodes; internal nodes are routing nodes
2. **Edge Marking**: Deleted nodes marked via edge flags, not node flags
3. **Three-Phase Delete**: Flag → Mark → Physical removal
4. **Helping Mechanism**: Threads help complete pending operations

### Why External Tree?

- Simplifies deletion (no in-place key removal)
- Internal nodes have exactly 2 children (or are being deleted)
- Easier to maintain tree invariants

## Data Structures

### Node Types

```c
typedef enum {
    NODE_INTERNAL,
    NODE_LEAF
} bst_node_type_t;

// Edge state (embedded in pointer low bits)
#define EDGE_CLEAN   0x0
#define EDGE_INTENT  0x1  // Intent to delete
#define EDGE_MARKED  0x2  // Marked for deletion

#define GET_FLAG(ptr)     ((uintptr_t)(ptr) & 0x3)
#define GET_PTR(ptr)      ((void *)((uintptr_t)(ptr) & ~0x3))
#define SET_FLAG(ptr, f)  ((void *)((uintptr_t)GET_PTR(ptr) | (f)))

typedef struct bst_internal_node {
    void *key;                          // Routing key
    _Atomic(struct bst_node *) left;    // Left child (with edge flags)
    _Atomic(struct bst_node *) right;   // Right child (with edge flags)
    _Atomic(struct bst_internal_node *) update;  // For helping
} bst_internal_node_t;

typedef struct bst_leaf_node {
    void *key;                          // Actual key
    void *value;                        // Associated value
} bst_leaf_node_t;

typedef union bst_node {
    struct {
        bst_node_type_t type;
    } common;
    bst_internal_node_t internal;
    bst_leaf_node_t leaf;
} bst_node_t;

typedef struct bst {
    bst_internal_node_t *root;          // Root internal node
    bst_leaf_node_t *left_sentinel;     // Left sentinel (key = -∞)
    bst_leaf_node_t *right_sentinel;    // Right sentinel (key = +∞)
    _Atomic(size_t) count;              // Element count
    comparator_t *comparator;           // Key comparison
    smr_domain_t *smr;                  // SMR for safe reclamation
} bst_t;
```

### Search Record

```c
typedef struct bst_search_record {
    bst_internal_node_t *gp;            // Grandparent
    bst_internal_node_t *p;             // Parent
    bst_node_t *l;                      // Current leaf
    void *gp_edge;                      // Edge to parent (with flags)
    void *p_edge;                       // Edge to leaf (with flags)
    bool p_is_left;                     // Is parent left child of gp?
    bool l_is_left;                     // Is leaf left child of parent?
} bst_search_record_t;
```

## Core Operations

### Search Operation

```c
bool bst_search(bst_t *tree, void *key, void **value) {
    smr_enter(tree->smr);

    bst_node_t *curr = (bst_node_t *)tree->root;

    while (curr->common.type == NODE_INTERNAL) {
        bst_internal_node_t *internal = &curr->internal;
        int cmp = comparator_compare(tree->comparator, key, internal->key);

        if (cmp < 0) {
            curr = GET_PTR(atomic_load(&internal->left));
        } else {
            curr = GET_PTR(atomic_load(&internal->right));
        }
    }

    // At leaf
    bst_leaf_node_t *leaf = &curr->leaf;
    int cmp = comparator_compare(tree->comparator, key, leaf->key);

    if (cmp == 0 && leaf != tree->left_sentinel && leaf != tree->right_sentinel) {
        if (value) {
            *value = leaf->value;
            Py_INCREF(*value);
        }
        smr_exit(tree->smr);
        return true;
    }

    smr_exit(tree->smr);
    return false;
}

// Full search with parent tracking
void bst_search_full(bst_t *tree, void *key, bst_search_record_t *rec) {
    rec->gp = NULL;
    rec->p = tree->root;

    int cmp = comparator_compare(tree->comparator, key, tree->root->key);
    if (cmp < 0) {
        rec->gp_edge = atomic_load(&tree->root->left);
        rec->p_is_left = true;
    } else {
        rec->gp_edge = atomic_load(&tree->root->right);
        rec->p_is_left = false;
    }

    bst_node_t *curr = GET_PTR(rec->gp_edge);

    while (curr->common.type == NODE_INTERNAL) {
        rec->gp = rec->p;
        rec->p = &curr->internal;

        cmp = comparator_compare(tree->comparator, key, curr->internal.key);

        if (cmp < 0) {
            rec->p_edge = atomic_load(&curr->internal.left);
            rec->l_is_left = true;
        } else {
            rec->p_edge = atomic_load(&curr->internal.right);
            rec->l_is_left = false;
        }

        rec->gp_edge = rec->l_is_left ?
            atomic_load(&rec->gp->left) : atomic_load(&rec->gp->right);
        rec->p_is_left = rec->l_is_left;

        curr = GET_PTR(rec->p_edge);
    }

    rec->l = curr;
}
```

### Insert Operation

```c
typedef enum {
    BST_INSERT_SUCCESS,
    BST_INSERT_EXISTS,
    BST_INSERT_REPLACED,
    BST_INSERT_ERROR
} bst_insert_result_t;

bst_insert_result_t bst_insert(bst_t *tree, void *key, void *value,
                                bool replace) {
    smr_enter(tree->smr);

    while (true) {
        bst_search_record_t rec;
        bst_search_full(tree, key, &rec);

        bst_leaf_node_t *leaf = &rec.l->leaf;

        // Check if key exists
        int cmp = comparator_compare(tree->comparator, key, leaf->key);
        if (cmp == 0 && leaf != tree->left_sentinel &&
            leaf != tree->right_sentinel) {
            if (!replace) {
                smr_exit(tree->smr);
                return BST_INSERT_EXISTS;
            }
            // Replace value atomically
            void *old_val = leaf->value;
            leaf->value = value;
            Py_INCREF(value);
            Py_DECREF(old_val);
            smr_exit(tree->smr);
            return BST_INSERT_REPLACED;
        }

        // Check for pending operation on parent edge
        if (GET_FLAG(rec.p_edge) != EDGE_CLEAN) {
            help(tree, rec.p, rec.p_edge);
            continue;
        }

        // Allocate new nodes
        bst_leaf_node_t *new_leaf = alloc_leaf(key, value);
        bst_internal_node_t *new_internal = alloc_internal();

        if (!new_leaf || !new_internal) {
            if (new_leaf) free_leaf(new_leaf);
            if (new_internal) free_internal(new_internal);
            smr_exit(tree->smr);
            return BST_INSERT_ERROR;
        }

        // Set up new internal node
        if (cmp < 0) {
            new_internal->key = leaf->key;
            new_internal->left = new_leaf;
            new_internal->right = leaf;
        } else {
            new_internal->key = key;
            new_internal->left = leaf;
            new_internal->right = new_leaf;
        }

        // CAS to insert
        void **target = rec.l_is_left ?
            (void **)&rec.p->left : (void **)&rec.p->right;

        if (atomic_compare_exchange_strong(target, &rec.p_edge, new_internal)) {
            atomic_fetch_add(&tree->count, 1);
            smr_exit(tree->smr);
            return BST_INSERT_SUCCESS;
        }

        // CAS failed, free and retry
        free_leaf(new_leaf);
        free_internal(new_internal);
    }
}
```

### Delete Operation (Three-Phase)

```c
bool bst_delete(bst_t *tree, void *key, void **old_value) {
    smr_enter(tree->smr);

    while (true) {
        bst_search_record_t rec;
        bst_search_full(tree, key, &rec);

        bst_leaf_node_t *leaf = &rec.l->leaf;

        // Check if key exists
        int cmp = comparator_compare(tree->comparator, key, leaf->key);
        if (cmp != 0 || leaf == tree->left_sentinel ||
            leaf == tree->right_sentinel) {
            smr_exit(tree->smr);
            return false;  // Key not found
        }

        // Check for pending operation
        if (GET_FLAG(rec.p_edge) != EDGE_CLEAN) {
            help(tree, rec.p, rec.p_edge);
            continue;
        }

        // Phase 1: Set intent flag on parent edge
        void *intended = SET_FLAG(rec.l, EDGE_INTENT);
        void **p_target = rec.l_is_left ?
            (void **)&rec.p->left : (void **)&rec.p->right;

        if (!atomic_compare_exchange_strong(p_target, &rec.p_edge, intended)) {
            continue;  // Retry
        }

        // Phase 2: Mark grandparent edge
        bool phase2_success = false;

        if (rec.gp != NULL) {
            void *gp_edge = rec.p_is_left ?
                atomic_load(&rec.gp->left) : atomic_load(&rec.gp->right);

            if (GET_PTR(gp_edge) == rec.p && GET_FLAG(gp_edge) == EDGE_CLEAN) {
                void *marked = SET_FLAG(rec.p, EDGE_MARKED);
                void **gp_target = rec.p_is_left ?
                    (void **)&rec.gp->left : (void **)&rec.gp->right;

                phase2_success = atomic_compare_exchange_strong(
                    gp_target, &gp_edge, marked);
            }
        }

        // Phase 3: Physical removal (swing sibling up)
        if (phase2_success || rec.gp == NULL) {
            bst_node_t *sibling = rec.l_is_left ?
                GET_PTR(atomic_load(&rec.p->right)) :
                GET_PTR(atomic_load(&rec.p->left));

            void **gp_target = rec.p_is_left ?
                (void **)&rec.gp->left : (void **)&rec.gp->right;

            void *expected = SET_FLAG(rec.p, EDGE_MARKED);
            atomic_compare_exchange_strong(gp_target, &expected, sibling);

            // Save old value
            if (old_value) {
                *old_value = leaf->value;
                Py_INCREF(*old_value);
            }

            // Retire deleted nodes
            smr_retire(tree->smr, rec.p, free_internal);
            smr_retire(tree->smr, leaf, free_leaf);

            atomic_fetch_sub(&tree->count, 1);
        }

        smr_exit(tree->smr);
        return true;
    }
}
```

### Helping Mechanism

```c
void help(bst_t *tree, bst_internal_node_t *p, void *p_edge) {
    uint8_t flag = GET_FLAG(p_edge);

    if (flag == EDGE_INTENT) {
        // Help complete the intent phase
        help_intent(tree, p, p_edge);
    } else if (flag == EDGE_MARKED) {
        // Help complete the physical removal
        help_marked(tree, p, p_edge);
    }
}

void help_intent(bst_t *tree, bst_internal_node_t *p, void *p_edge) {
    // Find grandparent and mark its edge
    // (Simplified - full implementation tracks update pointer)
    bst_search_record_t rec;
    bst_leaf_node_t *leaf = GET_PTR(p_edge);
    bst_search_full(tree, leaf->key, &rec);

    if (rec.p == p) {
        // Try to mark grandparent edge
        void *gp_edge = rec.p_is_left ?
            atomic_load(&rec.gp->left) : atomic_load(&rec.gp->right);

        if (GET_PTR(gp_edge) == p && GET_FLAG(gp_edge) == EDGE_CLEAN) {
            void *marked = SET_FLAG(p, EDGE_MARKED);
            void **target = rec.p_is_left ?
                (void **)&rec.gp->left : (void **)&rec.gp->right;
            atomic_compare_exchange_strong(target, &gp_edge, marked);
        }
    }
}

void help_marked(bst_t *tree, bst_internal_node_t *p, void *gp_edge) {
    // Complete physical removal
    bst_internal_node_t *gp = /* find grandparent */;

    // Get sibling
    void *left_edge = atomic_load(&p->left);
    void *right_edge = atomic_load(&p->right);

    bst_node_t *sibling;
    if (GET_FLAG(left_edge) == EDGE_INTENT) {
        sibling = GET_PTR(right_edge);
    } else {
        sibling = GET_PTR(left_edge);
    }

    // CAS sibling into grandparent
    void **target = /* appropriate gp child pointer */;
    atomic_compare_exchange_strong(target, &gp_edge, sibling);
}
```

## BSTProfiler API

```python
from dataclasses import dataclass, field
from typing import Dict, List, Optional
from contextlib import contextmanager
import threading
import time

@dataclass
class BSTStats:
    """Statistics for lock-free BST operations."""

    # Operation counts
    total_inserts: int = 0
    total_deletes: int = 0
    total_searches: int = 0

    # CAS metrics
    total_cas_attempts: int = 0
    total_cas_failures: int = 0
    cas_failure_rate: float = 0.0

    # Helping metrics
    total_help_intent: int = 0
    total_help_marked: int = 0
    help_operations_per_delete: float = 0.0

    # Tree structure
    current_height: int = 0
    internal_nodes: int = 0
    leaf_nodes: int = 0

    # Traversal depth
    avg_search_depth: float = 0.0
    avg_insert_depth: float = 0.0
    max_depth_observed: int = 0

    # Latency percentiles (microseconds)
    insert_latency_p50: float = 0.0
    insert_latency_p99: float = 0.0
    search_latency_p50: float = 0.0
    search_latency_p99: float = 0.0
    delete_latency_p50: float = 0.0
    delete_latency_p99: float = 0.0

    # Balance metrics
    balance_factor: float = 0.0  # Ratio of actual to optimal height


class BSTProfiler:
    """
    Profiler for Natarajan-Mittal lock-free BST.

    Features:
    - Operation latency tracking
    - CAS success/failure monitoring
    - Helping operation analysis
    - Tree height and balance metrics
    - Traversal depth analysis
    """

    def __init__(
        self,
        *,
        track_latency: bool = True,
        track_cas: bool = True,
        track_depth: bool = True,
        track_helping: bool = True,
        track_balance: bool = False,  # Expensive - samples tree
        balance_sample_interval: int = 1000,
    ):
        self.track_latency = track_latency
        self.track_cas = track_cas
        self.track_depth = track_depth
        self.track_helping = track_helping
        self.track_balance = track_balance
        self.balance_sample_interval = balance_sample_interval

        self._lock = threading.Lock()
        self._reset_counters()

    def _reset_counters(self):
        self._insert_count = 0
        self._delete_count = 0
        self._search_count = 0

        self._cas_attempts = 0
        self._cas_failures = 0

        self._help_intent = 0
        self._help_marked = 0

        self._search_depths = []
        self._insert_depths = []
        self._max_depth = 0

        self._latency_insert = []
        self._latency_search = []
        self._latency_delete = []

        self._ops_since_balance = 0
        self._last_height = 0
        self._last_balance = 1.0

    @contextmanager
    def profile_insert(self):
        """Profile an insert operation."""
        start = time.perf_counter_ns()
        ctx = {'cas_attempts': 0, 'cas_failures': 0, 'depth': 0}

        try:
            yield ctx
        finally:
            elapsed = time.perf_counter_ns() - start

            with self._lock:
                self._insert_count += 1

                if self.track_latency:
                    self._latency_insert.append(elapsed / 1000)

                if self.track_cas:
                    self._cas_attempts += ctx['cas_attempts']
                    self._cas_failures += ctx['cas_failures']

                if self.track_depth:
                    self._insert_depths.append(ctx['depth'])
                    self._max_depth = max(self._max_depth, ctx['depth'])

    @contextmanager
    def profile_search(self):
        """Profile a search operation."""
        start = time.perf_counter_ns()
        ctx = {'depth': 0}

        try:
            yield ctx
        finally:
            elapsed = time.perf_counter_ns() - start

            with self._lock:
                self._search_count += 1

                if self.track_latency:
                    self._latency_search.append(elapsed / 1000)

                if self.track_depth:
                    self._search_depths.append(ctx['depth'])

    @contextmanager
    def profile_delete(self):
        """Profile a delete operation."""
        start = time.perf_counter_ns()
        ctx = {'cas_attempts': 0, 'cas_failures': 0,
               'help_intent': 0, 'help_marked': 0}

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

                if self.track_helping:
                    self._help_intent += ctx['help_intent']
                    self._help_marked += ctx['help_marked']

    def record_tree_stats(self, height: int, internal: int, leaves: int):
        """Record tree structure statistics."""
        with self._lock:
            self._last_height = height
            if leaves > 0:
                import math
                optimal_height = math.ceil(math.log2(leaves + 1))
                self._last_balance = optimal_height / max(height, 1)

    def get_stats(self) -> BSTStats:
        """Get current statistics."""
        with self._lock:
            stats = BSTStats()

            stats.total_inserts = self._insert_count
            stats.total_deletes = self._delete_count
            stats.total_searches = self._search_count

            stats.total_cas_attempts = self._cas_attempts
            stats.total_cas_failures = self._cas_failures
            if self._cas_attempts > 0:
                stats.cas_failure_rate = self._cas_failures / self._cas_attempts

            stats.total_help_intent = self._help_intent
            stats.total_help_marked = self._help_marked
            if self._delete_count > 0:
                stats.help_operations_per_delete = (
                    (self._help_intent + self._help_marked) / self._delete_count
                )

            stats.current_height = self._last_height
            stats.max_depth_observed = self._max_depth
            stats.balance_factor = self._last_balance

            if self._search_depths:
                stats.avg_search_depth = sum(self._search_depths) / len(self._search_depths)
            if self._insert_depths:
                stats.avg_insert_depth = sum(self._insert_depths) / len(self._insert_depths)

            # Percentiles
            for name, data in [('insert', self._latency_insert),
                               ('search', self._latency_search),
                               ('delete', self._latency_delete)]:
                if data:
                    sorted_lat = sorted(data)
                    n = len(sorted_lat)
                    setattr(stats, f'{name}_latency_p50', sorted_lat[int(n * 0.50)])
                    setattr(stats, f'{name}_latency_p99', sorted_lat[min(int(n * 0.99), n-1)])

            return stats

    def analyze_balance(self) -> Dict:
        """Analyze tree balance and provide recommendations."""
        stats = self.get_stats()
        issues = []
        recommendations = []

        if stats.balance_factor < 0.5:
            issues.append(f"Poor tree balance: {stats.balance_factor:.2f}")
            recommendations.append("Consider periodic rebalancing or self-balancing variant")

        if stats.avg_search_depth > 2 * (stats.current_height ** 0.5):
            issues.append("Search depth exceeds expected for balanced tree")
            recommendations.append("Key distribution may be causing imbalance")

        if stats.help_operations_per_delete > 2.0:
            issues.append(f"High helping overhead: {stats.help_operations_per_delete:.1f}x")
            recommendations.append("Many concurrent deletes - consider batching")

        return {
            'has_issues': len(issues) > 0,
            'issues': issues,
            'recommendations': recommendations,
            'balance_factor': stats.balance_factor,
            'avg_depth': stats.avg_search_depth,
        }

    def export_prometheus(self) -> str:
        """Export metrics in Prometheus format."""
        stats = self.get_stats()
        lines = [
            '# HELP bst_operations_total Total BST operations',
            '# TYPE bst_operations_total counter',
            f'bst_operations_total{{op="insert"}} {stats.total_inserts}',
            f'bst_operations_total{{op="delete"}} {stats.total_deletes}',
            f'bst_operations_total{{op="search"}} {stats.total_searches}',
            '',
            '# HELP bst_height Current tree height',
            '# TYPE bst_height gauge',
            f'bst_height {stats.current_height}',
            '',
            '# HELP bst_balance_factor Tree balance factor',
            '# TYPE bst_balance_factor gauge',
            f'bst_balance_factor {stats.balance_factor:.3f}',
        ]
        return '\n'.join(lines)

    def reset(self):
        """Reset all counters."""
        with self._lock:
            self._reset_counters()
```

## Memory Ordering

| Operation | Memory Order | Rationale |
|-----------|-------------|-----------|
| Edge load | Acquire | See node contents |
| Edge CAS | Acq-Rel | Synchronize modification |
| Count update | Relaxed | Approximate is fine |

## Thread Safety

| Operation | Progress Guarantee |
|-----------|-------------------|
| Insert | Lock-free |
| Delete | Lock-free (with helping) |
| Search | Wait-free |

## References

- Natarajan, A., & Mittal, N. (2014). "Fast Concurrent Lock-Free Binary Search Trees."
- Howley, S., & Jones, J. (2012). "A Non-Blocking Internal Binary Search Tree."
