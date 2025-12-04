# smr_ibr — Design

## Overview

The `smr_ibr` module implements Interval-Based Reclamation (IBR), a safe memory reclamation scheme for lock-free data structures. IBR solves the fundamental problem of determining when it's safe to free memory that may still be accessed by concurrent readers.

## Dependencies

| Dependency | Purpose |
|------------|---------|
| atomics | Atomic operations for epoch tracking |
| config | Runtime configuration, thread detection |
| mimalloc_glue | Actual memory allocation/deallocation |

## The Problem: Safe Memory Reclamation

In lock-free data structures:
```
Thread A                    Thread B
────────                    ────────
node = find(key)
                           delete(key)
                           // When can we free node?
read(node->value)          // Thread A still holds reference!
                           free(node)  // CRASH: use-after-free
```

**Challenge**: Thread B cannot know when Thread A is done accessing the node.

**Solution**: Defer freeing until we can prove no thread holds a reference.

## Architecture

### Core Concept: Epochs

IBR divides time into epochs. Each thread records which epoch it entered:

```
Global Epoch:  [1]─────────[2]─────────[3]─────────[4]
                    │           │           │
Thread 1:      ▓▓▓▓▓▓▓▓[2]──────────────────────▓▓▓▓▓
Thread 2:      ▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓[2]──────[3]──────────
Thread 3:      ▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓[3]───────

Legend: ▓▓▓ = outside critical section, [N] = in epoch N
```

**Key Insight**: A node retired in epoch E can only be freed when NO thread is in epoch ≤ E.

### Data Structures

```c
// Global state
typedef struct {
    atomic_uint64_t global_epoch;           // Current global epoch
    atomic_uint64_t thread_epochs[MAX_THREADS]; // Per-thread epoch
    atomic_bool thread_active[MAX_THREADS];  // Thread in critical section?
} smr_global_t;

// Per-thread state
typedef struct {
    uint64_t local_epoch;                   // Cached local epoch
    retire_list_t* retire_lists[3];         // Limbo lists per epoch (ring buffer)
    uint32_t retire_count;                  // Items in current limbo list
    uint32_t thread_id;                     // Thread's slot in global arrays
} smr_thread_t;

// Retired node entry
typedef struct {
    void* ptr;                              // Pointer to retired node
    size_t size;                            // Node size (for stats)
    void (*free_fn)(void*, size_t);         // Free callback
} retire_entry_t;

// Limbo list (nodes pending reclamation)
typedef struct retire_list {
    retire_entry_t* entries;
    uint32_t count;
    uint32_t capacity;
    uint64_t epoch;                         // Epoch when nodes were retired
} retire_list_t;
```

### IBR Algorithm

#### Enter Critical Section

```c
void smr_enter(smr_thread_t* thr) {
    // Load current global epoch
    uint64_t epoch = atomic_load_explicit(&g_smr.global_epoch, memory_order_acquire);

    // Record that this thread is in this epoch
    thr->local_epoch = epoch;
    atomic_store_explicit(&g_smr.thread_epochs[thr->thread_id], epoch, memory_order_release);
    atomic_store_explicit(&g_smr.thread_active[thr->thread_id], true, memory_order_release);

    // Memory barrier ensures epoch is visible before any data access
    atomic_thread_fence(memory_order_seq_cst);
}
```

#### Exit Critical Section

```c
void smr_exit(smr_thread_t* thr) {
    // Clear active flag - we're no longer holding references
    atomic_store_explicit(&g_smr.thread_active[thr->thread_id], false, memory_order_release);

    // Opportunistically try to reclaim
    if (thr->retire_count >= RETIRE_THRESHOLD) {
        smr_poll(thr);
    }
}
```

#### Retire a Node

```c
void smr_retire(smr_thread_t* thr, void* ptr, size_t size, void (*free_fn)(void*, size_t)) {
    // Get current limbo list (indexed by epoch mod 3)
    uint64_t epoch = thr->local_epoch;
    retire_list_t* list = thr->retire_lists[epoch % 3];

    // Add to limbo list
    list->entries[list->count++] = (retire_entry_t){ptr, size, free_fn};
    thr->retire_count++;

    // Try to advance epoch if we've retired enough
    if (thr->retire_count >= RETIRE_THRESHOLD) {
        smr_try_advance_epoch(thr);
        smr_poll(thr);
    }
}
```

#### Poll for Reclamation

```c
void smr_poll(smr_thread_t* thr) {
    uint64_t safe_epoch = smr_compute_safe_epoch();

    // Free nodes from epochs older than safe_epoch
    for (int i = 0; i < 3; i++) {
        retire_list_t* list = thr->retire_lists[i];
        if (list->epoch < safe_epoch && list->count > 0) {
            // Safe to free all nodes in this list
            for (uint32_t j = 0; j < list->count; j++) {
                retire_entry_t* e = &list->entries[j];
                e->free_fn(e->ptr, e->size);
            }
            list->count = 0;
            thr->retire_count -= list->count;
        }
    }
}

uint64_t smr_compute_safe_epoch(void) {
    uint64_t min_epoch = UINT64_MAX;

    for (int t = 0; t < MAX_THREADS; t++) {
        if (atomic_load_explicit(&g_smr.thread_active[t], memory_order_acquire)) {
            uint64_t epoch = atomic_load_explicit(&g_smr.thread_epochs[t], memory_order_acquire);
            if (epoch < min_epoch) {
                min_epoch = epoch;
            }
        }
    }

    return min_epoch;
}
```

#### Advance Global Epoch

```c
void smr_try_advance_epoch(smr_thread_t* thr) {
    uint64_t current = atomic_load_explicit(&g_smr.global_epoch, memory_order_acquire);
    uint64_t safe = smr_compute_safe_epoch();

    // Can only advance if all active threads have caught up
    if (safe >= current) {
        // CAS to avoid duplicate advances
        atomic_compare_exchange_strong(&g_smr.global_epoch, &current, current + 1);
    }
}
```

### Memory Bound Analysis

With T threads and retire threshold R:
- Each thread can have up to 3R nodes in limbo (3 epoch lists)
- Worst case: 3 × T × R nodes pending
- Memory bound: O(T²R) in pathological cases where all threads retire simultaneously

**Typical case**: Much better, as epochs advance and nodes are reclaimed promptly.

### Handling Stalled Threads

A stalled thread (blocking I/O, long computation) holds an old epoch, blocking reclamation.

**Detection:**
```c
bool smr_is_stalled(int thread_id, uint64_t threshold_epochs) {
    if (!atomic_load(&g_smr.thread_active[thread_id])) {
        return false;  // Not active, not stalled
    }

    uint64_t global = atomic_load(&g_smr.global_epoch);
    uint64_t thread_epoch = atomic_load(&g_smr.thread_epochs[thread_id]);

    return (global - thread_epoch) > threshold_epochs;
}
```

**Mitigation Strategies:**
1. **Cooperative Exit**: Document that threads should exit SMR during long operations
2. **Epoch Timeout**: Force-advance epoch after timeout (with caution)
3. **Thread Cleanup**: Unregister threads that exit/crash

## API Surface

### C API

```c
// Global initialization
int smr_init(void);
void smr_shutdown(void);

// Thread registration (must call before using SMR)
smr_thread_t* smr_thread_register(void);
void smr_thread_unregister(smr_thread_t* thr);

// Critical section
void smr_enter(smr_thread_t* thr);
void smr_exit(smr_thread_t* thr);

// Node retirement
void smr_retire(smr_thread_t* thr, void* ptr, size_t size, void (*free_fn)(void*, size_t));

// Manual reclamation poll
void smr_poll(smr_thread_t* thr);

// Diagnostics
uint64_t smr_get_epoch(void);
uint64_t smr_pending_count(smr_thread_t* thr);
```

### Python Integration

```python
# Automatic per-thread registration via TLS
# User doesn't interact with SMR directly

# Diagnostic access via config
from concurrent_collections import config

config.smr_scheme = 'ibr'  # Default
config.retire_threshold = 64
config.max_reclaim_per_poll = 32

# Statistics (if enabled)
stats = config.smr_stats()
print(f"Global epoch: {stats.global_epoch}")
print(f"Pending nodes: {stats.pending_count}")
```

## Integration with Containers

### SkipListMap Example

```c
// In SkipListMap delete operation
static PyObject* skiplist_delete(SkipListMapObject* self, PyObject* key) {
    smr_thread_t* smr = get_thread_smr();
    smr_enter(smr);

    SkipListNode* node = find_and_unlink(self, key);
    if (node) {
        // Node is unlinked but may still be accessed by concurrent readers
        smr_retire(smr, node, sizeof(SkipListNode), skiplist_node_free);
    }

    smr_exit(smr);
    Py_RETURN_NONE;
}

// Free callback
static void skiplist_node_free(void* ptr, size_t size) {
    SkipListNode* node = (SkipListNode*)ptr;
    Py_DECREF(node->key);
    Py_DECREF(node->value);
    cc_free(ptr, size);
}
```

## Design Decisions

| Decision | Choice | Rationale |
|----------|--------|-----------|
| Epoch representation | uint64_t | Effectively infinite (no overflow in practice) |
| Limbo list count | 3 (ring buffer) | Sufficient for 2-epoch lag + current |
| Thread tracking | Array | Simple, O(1) lookup, fixed max threads |
| Retirement trigger | Count-based | Amortizes reclamation cost |
| Free callback | Function pointer | Flexible for different node types |

## Configuration

| Parameter | Default | Description |
|-----------|---------|-------------|
| `retire_threshold` | 64 | Nodes before triggering reclamation |
| `max_reclaim_per_poll` | 32 | Max nodes freed per poll |
| `max_threads` | 256 | Maximum concurrent threads |
| `stall_threshold_epochs` | 100 | Epochs before thread considered stalled |

## Performance Characteristics

### Overhead

| Operation | Cost | Notes |
|-----------|------|-------|
| `smr_enter` | ~5-10ns | One atomic load, one store, fence |
| `smr_exit` | ~5ns | One atomic store |
| `smr_retire` | ~20ns | List append, occasional poll |
| `smr_poll` | ~50ns-5μs | Depends on nodes to free |

### Scalability

- Thread-local retire lists minimize contention
- Global epoch read is shared (cache line)
- Epoch advance is CAS-based (single writer wins)
- Scales well to 32+ threads

## Instrumentation & Profiling

### SMRProfiler

The `SMRProfiler` provides comprehensive analysis of safe memory reclamation behavior, helping users understand memory lifecycle, identify stalls, and optimize reclamation timing.

#### Features Overview

| Feature | Purpose | Overhead |
|---------|---------|----------|
| **Epoch Timeline** | Visualize epoch advancement over time | Low |
| **Limbo List Depth** | Track pending nodes per thread | Low |
| **Reclamation Latency** | Time between retire and free | Medium |
| **Safe Epoch Lag** | Gap between global and safe epoch | Low |
| **Stalled Thread Detection** | Identify blocking threads | Low |
| **Poll Efficiency** | Nodes freed per poll call | Low |
| **Memory Pressure** | Pending bytes trending toward bound | Low |
| **Per-Thread Activity** | Enter/exit/retire patterns | Medium |
| **Epoch Stall Analyzer** | Diagnose reclamation delays | Medium |

#### Data Structures

```python
@dataclass
class EpochEvent:
    """Record of an epoch-related event."""
    timestamp: float
    event_type: str           # "advance", "enter", "exit", "retire", "reclaim"
    thread_id: int
    epoch: int
    details: dict | None      # Event-specific data

@dataclass
class LimboSnapshot:
    """Point-in-time limbo list state."""
    timestamp: float
    thread_id: int
    epoch_0_count: int        # Nodes in epoch % 3 == 0
    epoch_1_count: int        # Nodes in epoch % 3 == 1
    epoch_2_count: int        # Nodes in epoch % 3 == 2
    total_count: int
    total_bytes: int

@dataclass
class ReclamationRecord:
    """Record of a node's lifecycle."""
    retire_time: float
    retire_epoch: int
    retire_thread: int
    reclaim_time: float | None      # None if still pending
    reclaim_epoch: int | None
    reclaim_thread: int | None
    latency_ns: int | None          # reclaim_time - retire_time
    size: int

@dataclass
class ThreadSMRStats:
    """Per-thread SMR statistics."""
    thread_id: int
    thread_name: str | None

    # Activity counts
    enter_count: int
    exit_count: int
    retire_count: int
    poll_count: int
    reclaim_count: int

    # Time in critical section
    total_cs_time_ns: int           # Total time in critical section
    avg_cs_time_ns: float
    max_cs_time_ns: int

    # Limbo stats
    peak_limbo_count: int
    peak_limbo_bytes: int

    # Stall info
    stall_count: int                # Times this thread was considered stalled
    caused_stall_epochs: int        # Epochs this thread blocked advancement

@dataclass
class StallEvent:
    """Record of a stall event."""
    timestamp: float
    stalled_thread_id: int
    stalled_at_epoch: int
    global_epoch: int
    epoch_lag: int
    duration_ns: int | None         # How long until resolved
    resolution: str                 # "exited", "advanced", "neutralized"

@dataclass
class SMRProfilerReport:
    """Complete SMR profiler report."""
    # Global epoch statistics
    start_epoch: int
    end_epoch: int
    epoch_advances: int
    avg_epoch_duration_ns: float

    # Safe epoch statistics
    safe_epoch_lag_avg: float       # Average lag behind global
    safe_epoch_lag_max: int

    # Reclamation statistics
    total_retired: int
    total_reclaimed: int
    pending_count: int
    pending_bytes: int

    # Latency percentiles (retire to reclaim, nanoseconds)
    reclaim_latency_p50: float
    reclaim_latency_p95: float
    reclaim_latency_p99: float
    reclaim_latency_p999: float
    reclaim_latency_max: float

    # Poll statistics
    poll_count: int
    nodes_per_poll_avg: float
    nodes_per_poll_max: int
    empty_poll_pct: float           # Polls that freed nothing

    # Memory pressure
    peak_pending_count: int
    peak_pending_bytes: int
    memory_bound_utilization: float  # peak / theoretical_max

    # Thread statistics
    thread_stats: list[ThreadSMRStats]

    # Stall analysis
    stall_events: list[StallEvent]
    total_stall_time_ns: int
    stall_count: int

    # Timeline (if enabled)
    epoch_timeline: list[EpochEvent] | None
    limbo_snapshots: list[LimboSnapshot] | None

    # Timing
    duration_seconds: float
    start_time: datetime
    end_time: datetime
```

#### Profiler API

```python
class SMRProfiler:
    def __init__(
        self,
        *,
        track_timeline: bool = False,       # Full event timeline (high overhead)
        track_per_thread: bool = True,
        track_latency: bool = True,
        track_limbo_snapshots: bool = False,
        snapshot_interval_ms: float = 100,  # For limbo snapshots
        sample_rate: float = 1.0,
        stall_threshold_epochs: int = 10,   # Epochs before considered stalled
    ):
        """Initialize SMR profiler."""
        ...

    def __enter__(self) -> 'SMRProfiler':
        """Start profiling."""
        ...

    def __exit__(self, *args) -> None:
        """Stop profiling."""
        ...

    def start(self) -> None:
        """Start profiling."""
        ...

    def stop(self) -> None:
        """Stop profiling."""
        ...

    def snapshot(self) -> SMRProfilerReport:
        """Get current statistics without stopping."""
        ...

    def report(self) -> SMRProfilerReport:
        """Get final report."""
        ...

    def reset(self) -> None:
        """Reset all statistics."""
        ...

    # Analysis methods
    def analyze_stalls(self) -> list[dict]:
        """Detailed stall analysis with recommendations."""
        ...

    def find_slow_threads(self, threshold_epochs: int = 5) -> list[int]:
        """Find threads that frequently cause epoch lag."""
        ...

    def memory_pressure_events(self, threshold_pct: float = 0.8) -> list[dict]:
        """Find times when pending memory exceeded threshold."""
        ...

    # Export methods
    def to_json(self, path: str | Path) -> None:
        """Export report to JSON."""
        ...

    def to_html(self, path: str | Path) -> None:
        """Generate HTML dashboard report."""
        ...

    def to_prometheus(self) -> str:
        """Export metrics in Prometheus format."""
        ...
```

#### Usage Examples

```python
from concurrent_collections import SMRProfiler, SkipListMap
import threading

# Basic SMR profiling
with SMRProfiler() as prof:
    m = SkipListMap()

    def worker(n):
        for i in range(n):
            m[f"key_{threading.current_thread().ident}_{i}"] = i
            if i % 2 == 0:
                m.pop(f"key_{threading.current_thread().ident}_{i-1}", None)

    threads = [threading.Thread(target=worker, args=(10000,)) for _ in range(8)]
    for t in threads:
        t.start()
    for t in threads:
        t.join()

report = prof.report()
print(f"Epoch advances: {report.epoch_advances}")
print(f"Reclaim latency P99: {report.reclaim_latency_p99 / 1000:.1f} µs")
print(f"Peak pending: {report.peak_pending_count} nodes ({report.peak_pending_bytes / 1024:.1f} KB)")
print(f"Memory bound utilization: {report.memory_bound_utilization:.1%}")

# Stall analysis
if report.stall_events:
    print(f"\nStall events: {len(report.stall_events)}")
    for stall in report.stall_events[:3]:
        print(f"  Thread {stall.stalled_thread_id} stalled for {stall.duration_ns/1e6:.1f} ms "
              f"at epoch {stall.stalled_at_epoch} (lag: {stall.epoch_lag})")

# Per-thread breakdown
print("\nPer-thread stats:")
for ts in sorted(report.thread_stats, key=lambda x: -x.retire_count)[:5]:
    print(f"  Thread {ts.thread_id}: {ts.retire_count} retires, "
          f"{ts.avg_cs_time_ns/1000:.1f} µs avg CS time, "
          f"{ts.stall_count} stalls caused")

# Detailed stall analysis
stall_analysis = prof.analyze_stalls()
for analysis in stall_analysis:
    print(f"\nStall pattern: {analysis['pattern']}")
    print(f"  Frequency: {analysis['frequency']}")
    print(f"  Recommendation: {analysis['recommendation']}")

# Export to HTML with visualizations
prof.to_html("smr_report.html")
```

#### HTML Dashboard

The HTML report includes interactive visualizations:

1. **Epoch Timeline** - Global epoch over time with advances marked
2. **Safe Epoch Lag Chart** - Gap between global and safe epoch
3. **Limbo Depth Heatmap** - Per-thread pending nodes over time
4. **Reclamation Latency Histogram** - Distribution of retire-to-free times
5. **Thread Activity Timeline** - Enter/exit patterns per thread
6. **Memory Pressure Gauge** - Current vs maximum pending memory
7. **Stall Event Log** - Detailed stall events with context
8. **Recommendations Panel** - Automated suggestions

#### Prometheus Metrics

```prometheus
# Epoch metrics
cc_smr_global_epoch 12345
cc_smr_safe_epoch 12343
cc_smr_epoch_advances_total 12344
cc_smr_epoch_lag 2

# Reclamation metrics
cc_smr_retired_total 9876543
cc_smr_reclaimed_total 9876500
cc_smr_pending_count 43
cc_smr_pending_bytes 5432

# Latency histogram (nanoseconds)
cc_smr_reclaim_latency_bucket{le="1000"} 5000000
cc_smr_reclaim_latency_bucket{le="10000"} 8000000
cc_smr_reclaim_latency_bucket{le="100000"} 9500000
cc_smr_reclaim_latency_bucket{le="+Inf"} 9876543

# Poll metrics
cc_smr_poll_total 123456
cc_smr_poll_empty_total 12345
cc_smr_nodes_per_poll_avg 80.1

# Stall metrics
cc_smr_stall_events_total 5
cc_smr_stall_time_total_ns 50000000

# Memory pressure
cc_smr_peak_pending_count 1024
cc_smr_memory_bound_utilization 0.67
```

#### Debugging Tools

```python
# Epoch stall analyzer
from concurrent_collections.debug import EpochStallAnalyzer

analyzer = EpochStallAnalyzer()
analyzer.attach()  # Start monitoring

# ... run workload ...

# Get detailed diagnosis
diagnosis = analyzer.diagnose()
print(f"Stall cause: {diagnosis.primary_cause}")
print(f"Blocking thread: {diagnosis.blocking_thread}")
print(f"Thread state: {diagnosis.thread_state}")
print(f"Recommendation: {diagnosis.recommendation}")

# Thread activity heatmap
from concurrent_collections.debug import ThreadActivityMonitor

monitor = ThreadActivityMonitor()
with monitor:
    # ... run workload ...
    pass

# Generate heatmap showing enter/exit patterns
monitor.plot_heatmap("thread_activity.png")
```

### Jupyter Notebook Integration

See `examples/smr_performance_analysis.ipynb` for interactive analysis including:
- Epoch timeline visualization
- Limbo depth analysis
- Stall pattern detection
- Memory pressure monitoring
- Optimization recommendations

See `examples/memory_subsystem_comparison.ipynb` for comparing IBR vs DEBRA+ performance.

## Open Questions

| Question | Options | Impact |
|----------|---------|--------|
| Thread registration | Explicit vs automatic | API complexity vs safety |
| Stalled thread handling | Timeout vs signal | Complexity vs reliability |
| Per-container vs global SMR | Separate vs shared | Memory vs simplicity |
