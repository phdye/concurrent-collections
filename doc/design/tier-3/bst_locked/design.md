# bst_locked — Design Document

## Overview

`bst_locked` implements a fine-grained locked binary search tree using hand-over-hand locking. This provides the same functionality as `bst_lockfree` but uses per-node locks, offering predictable latency and simpler implementation at the cost of reduced scalability.

## Design Rationale

### Why Locked BST?

1. **GIL Compatibility**: Lock-free provides no benefit with GIL
2. **Predictable Latency**: No CAS retry variance
3. **Simpler Correctness**: Easier to verify
4. **Fallback Option**: Works universally

### Lock Strategy: Hand-Over-Hand

- Acquire lock on next node before releasing current
- Prevents race conditions during traversal
- Classic "coupling" technique from concurrent data structures

## Data Structures

### Node Structure

```c
typedef struct bst_locked_node {
    void *key;
    void *value;
    struct bst_locked_node *left;
    struct bst_locked_node *right;
    pthread_mutex_t lock;
    bool marked;                    // Logically deleted
} bst_locked_node_t;

typedef struct bst_locked {
    bst_locked_node_t *root;        // Root node (sentinel)
    size_t count;
    pthread_mutex_t count_lock;
    comparator_t *comparator;
} bst_locked_t;
```

## Core Operations

### Hand-Over-Hand Traversal

```c
typedef struct {
    bst_locked_node_t *parent;
    bst_locked_node_t *current;
    bool is_left_child;
} bst_locked_position_t;

void bst_locked_traverse(bst_locked_t *tree, void *key,
                         bst_locked_position_t *pos) {
    pos->parent = NULL;
    pos->current = tree->root;
    pthread_mutex_lock(&pos->current->lock);

    while (pos->current->left != NULL || pos->current->right != NULL) {
        int cmp = comparator_compare(tree->comparator, key, pos->current->key);

        bst_locked_node_t *next;
        if (cmp < 0) {
            next = pos->current->left;
            pos->is_left_child = true;
        } else if (cmp > 0) {
            next = pos->current->right;
            pos->is_left_child = false;
        } else {
            break;  // Found exact match
        }

        if (next == NULL) break;

        // Hand-over-hand: lock next, unlock parent
        pthread_mutex_lock(&next->lock);

        if (pos->parent != NULL) {
            pthread_mutex_unlock(&pos->parent->lock);
        }

        pos->parent = pos->current;
        pos->current = next;
    }
}
```

### Insert Operation

```c
bool bst_locked_insert(bst_locked_t *tree, void *key, void *value) {
    bst_locked_position_t pos;
    bst_locked_traverse(tree, key, &pos);

    // Check if key exists
    if (pos.current->key != NULL) {
        int cmp = comparator_compare(tree->comparator, key, pos.current->key);
        if (cmp == 0 && !pos.current->marked) {
            // Key exists
            release_locks(&pos);
            return false;
        }
    }

    // Create new node
    bst_locked_node_t *new_node = alloc_node(key, value);

    // Link into tree
    int cmp = comparator_compare(tree->comparator, key, pos.current->key);
    if (cmp < 0) {
        pos.current->left = new_node;
    } else {
        pos.current->right = new_node;
    }

    // Update count
    pthread_mutex_lock(&tree->count_lock);
    tree->count++;
    pthread_mutex_unlock(&tree->count_lock);

    release_locks(&pos);
    return true;
}
```

### Delete Operation

```c
bool bst_locked_delete(bst_locked_t *tree, void *key, void **old_value) {
    bst_locked_position_t pos;
    bst_locked_traverse(tree, key, &pos);

    // Check if found
    int cmp = comparator_compare(tree->comparator, key, pos.current->key);
    if (cmp != 0 || pos.current->marked) {
        release_locks(&pos);
        return false;
    }

    // Save old value
    if (old_value) {
        *old_value = pos.current->value;
        Py_INCREF(*old_value);
    }

    // Mark as deleted
    pos.current->marked = true;

    // Physical removal depends on children count
    if (pos.current->left == NULL && pos.current->right == NULL) {
        // No children: unlink directly
        if (pos.is_left_child) {
            pos.parent->left = NULL;
        } else {
            pos.parent->right = NULL;
        }
        free_node(pos.current);
    } else if (pos.current->left == NULL || pos.current->right == NULL) {
        // One child: bypass
        bst_locked_node_t *child = pos.current->left ?
            pos.current->left : pos.current->right;
        if (pos.is_left_child) {
            pos.parent->left = child;
        } else {
            pos.parent->right = child;
        }
        free_node(pos.current);
    } else {
        // Two children: find successor, swap, delete
        bst_locked_node_t *succ_parent = pos.current;
        bst_locked_node_t *succ = pos.current->right;

        pthread_mutex_lock(&succ->lock);
        while (succ->left != NULL) {
            pthread_mutex_lock(&succ->left->lock);
            pthread_mutex_unlock(&succ_parent->lock);
            succ_parent = succ;
            succ = succ->left;
        }

        // Swap key/value
        pos.current->key = succ->key;
        pos.current->value = succ->value;
        pos.current->marked = false;

        // Unlink successor
        if (succ_parent == pos.current) {
            succ_parent->right = succ->right;
        } else {
            succ_parent->left = succ->right;
        }

        pthread_mutex_unlock(&succ->lock);
        free_node(succ);
    }

    pthread_mutex_lock(&tree->count_lock);
    tree->count--;
    pthread_mutex_unlock(&tree->count_lock);

    release_locks(&pos);
    return true;
}
```

### Search Operation (Lock-Free Read)

```c
bool bst_locked_search(bst_locked_t *tree, void *key, void **value) {
    // Optimistic traversal without locks
    bst_locked_node_t *curr = tree->root;

    while (curr != NULL) {
        // Memory barrier for visibility
        __atomic_thread_fence(__ATOMIC_ACQUIRE);

        if (curr->marked) {
            // Node deleted, restart from root
            curr = tree->root;
            continue;
        }

        int cmp = comparator_compare(tree->comparator, key, curr->key);

        if (cmp == 0) {
            if (!curr->marked) {
                if (value) {
                    *value = curr->value;
                    Py_INCREF(*value);
                }
                return true;
            }
            return false;
        } else if (cmp < 0) {
            curr = curr->left;
        } else {
            curr = curr->right;
        }
    }

    return false;
}
```

## BSTLockedProfiler API

```python
from dataclasses import dataclass
from contextlib import contextmanager
import threading
import time

@dataclass
class BSTLockedStats:
    """Statistics for locked BST."""
    total_inserts: int = 0
    total_deletes: int = 0
    total_searches: int = 0

    lock_acquisitions: int = 0
    lock_contentions: int = 0
    contention_rate: float = 0.0

    avg_traversal_depth: float = 0.0
    max_traversal_depth: int = 0

    insert_latency_p50: float = 0.0
    insert_latency_p99: float = 0.0
    search_latency_p50: float = 0.0
    search_latency_p99: float = 0.0


class BSTLockedProfiler:
    """Profiler for fine-grained locked BST."""

    def __init__(self, *, track_latency=True, track_contention=True,
                 track_depth=True):
        self.track_latency = track_latency
        self.track_contention = track_contention
        self.track_depth = track_depth
        self._lock = threading.Lock()
        self._reset()

    def _reset(self):
        self._insert_count = 0
        self._delete_count = 0
        self._search_count = 0
        self._lock_acquisitions = 0
        self._lock_contentions = 0
        self._depths = []
        self._latency_insert = []
        self._latency_search = []

    @contextmanager
    def profile_insert(self):
        start = time.perf_counter_ns()
        ctx = {'depth': 0, 'lock_acquisitions': 0, 'contentions': 0}
        try:
            yield ctx
        finally:
            elapsed = time.perf_counter_ns() - start
            with self._lock:
                self._insert_count += 1
                self._lock_acquisitions += ctx['lock_acquisitions']
                self._lock_contentions += ctx['contentions']
                if self.track_depth:
                    self._depths.append(ctx['depth'])
                if self.track_latency:
                    self._latency_insert.append(elapsed / 1000)

    @contextmanager
    def profile_search(self):
        start = time.perf_counter_ns()
        ctx = {'depth': 0}
        try:
            yield ctx
        finally:
            elapsed = time.perf_counter_ns() - start
            with self._lock:
                self._search_count += 1
                if self.track_depth:
                    self._depths.append(ctx['depth'])
                if self.track_latency:
                    self._latency_search.append(elapsed / 1000)

    def get_stats(self) -> BSTLockedStats:
        with self._lock:
            stats = BSTLockedStats()
            stats.total_inserts = self._insert_count
            stats.total_deletes = self._delete_count
            stats.total_searches = self._search_count
            stats.lock_acquisitions = self._lock_acquisitions
            stats.lock_contentions = self._lock_contentions

            if self._lock_acquisitions > 0:
                stats.contention_rate = self._lock_contentions / self._lock_acquisitions

            if self._depths:
                stats.avg_traversal_depth = sum(self._depths) / len(self._depths)
                stats.max_traversal_depth = max(self._depths)

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

            return stats
```

## Thread Safety

| Operation | Safety | Notes |
|-----------|--------|-------|
| Insert | Blocking | Hand-over-hand locking |
| Delete | Blocking | Same |
| Search | Lock-free | Optimistic read |

## Performance

| Operation | Expected | Notes |
|-----------|----------|-------|
| Insert | O(log n) | Balanced tree |
| Delete | O(log n) | May require successor find |
| Search | O(log n) | Lock-free traversal |

## Comparison with Lock-Free

| Aspect | bst_locked | bst_lockfree |
|--------|------------|--------------|
| Progress | Blocking | Lock-free |
| Latency variance | Low | Higher |
| Scalability | Moderate | Better |
| Complexity | Lower | Higher |
| Memory management | Immediate | SMR required |
