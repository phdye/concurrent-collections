# mimalloc_glue — Design

## Overview

The `mimalloc_glue` module provides a thin abstraction layer over the mimalloc allocator for node allocation in lock-free data structures. It handles allocation, deferred freeing (in coordination with SMR), and cross-thread memory operations.

## Dependencies

| Dependency | Purpose |
|------------|---------|
| config | Runtime configuration for allocator selection |
| mimalloc (external) | High-performance allocator with thread-local heaps |

## Architecture

### Role in the Memory System

```
┌───────────────────────────────────────────────────────────────┐
│                    Lock-Free Data Structures                   │
│              (SkipListNode, BSTNode, QueueNode)               │
└───────────────────────────────────────────────────────────────┘
                              │
                    ┌─────────┴─────────┐
                    │    SMR Layer      │
                    │  (IBR or DEBRA+)  │
                    └─────────┬─────────┘
                              │
                    ┌─────────┴─────────┐
                    │   mimalloc_glue   │  ◄── This module
                    └─────────┬─────────┘
                              │
                    ┌─────────┴─────────┐
                    │     mimalloc      │
                    │  Thread-local     │
                    │     heaps         │
                    └───────────────────┘
```

### Design Rationale

**Why mimalloc?**
1. **Default in CPython 3.13t**: mimalloc is CPython's default allocator in free-threaded mode
2. **Thread-Local Heaps**: Reduces contention on allocation paths
3. **Cross-Thread Free Handling**: Internally handles freeing memory allocated by another thread
4. **Performance**: Excellent performance for concurrent workloads
5. **No Configuration Required**: Works out of the box

**Why a glue layer?**
1. **Abstraction**: Isolates allocator-specific code
2. **Statistics**: Optional allocation tracking
3. **Future Flexibility**: Could support alternative allocators
4. **Testing**: Enables mock allocators for testing

### Core Data Structure

```c
// Allocation context (optional, for statistics)
typedef struct {
    atomic_uint64_t alloc_count;
    atomic_uint64_t free_count;
    atomic_uint64_t alloc_bytes;
    atomic_uint64_t free_bytes;
    bool statistics_enabled;
} cc_alloc_stats_t;

// Global allocation context
static cc_alloc_stats_t g_alloc_stats = {0};
```

### Memory Operations

```c
#include <mimalloc.h>

// Allocate memory for a node
static inline void* cc_alloc(size_t size) {
    void* ptr = mi_malloc(size);

    #if CC_ALLOC_STATS
    if (ptr && g_alloc_stats.statistics_enabled) {
        atomic_fetch_add_explicit(&g_alloc_stats.alloc_count, 1, memory_order_relaxed);
        atomic_fetch_add_explicit(&g_alloc_stats.alloc_bytes, size, memory_order_relaxed);
    }
    #endif

    return ptr;
}

// Allocate zeroed memory
static inline void* cc_calloc(size_t count, size_t size) {
    void* ptr = mi_calloc(count, size);

    #if CC_ALLOC_STATS
    if (ptr && g_alloc_stats.statistics_enabled) {
        atomic_fetch_add_explicit(&g_alloc_stats.alloc_count, 1, memory_order_relaxed);
        atomic_fetch_add_explicit(&g_alloc_stats.alloc_bytes, count * size, memory_order_relaxed);
    }
    #endif

    return ptr;
}

// Allocate aligned memory (for cache-line alignment)
static inline void* cc_alloc_aligned(size_t size, size_t alignment) {
    void* ptr = mi_malloc_aligned(size, alignment);

    #if CC_ALLOC_STATS
    if (ptr && g_alloc_stats.statistics_enabled) {
        atomic_fetch_add_explicit(&g_alloc_stats.alloc_count, 1, memory_order_relaxed);
        atomic_fetch_add_explicit(&g_alloc_stats.alloc_bytes, size, memory_order_relaxed);
    }
    #endif

    return ptr;
}

// Free memory (may be called from any thread)
static inline void cc_free(void* ptr, size_t size) {
    if (ptr) {
        #if CC_ALLOC_STATS
        if (g_alloc_stats.statistics_enabled) {
            atomic_fetch_add_explicit(&g_alloc_stats.free_count, 1, memory_order_relaxed);
            atomic_fetch_add_explicit(&g_alloc_stats.free_bytes, size, memory_order_relaxed);
        }
        #endif

        mi_free(ptr);
    }
}

// Free without size tracking (for compatibility)
static inline void cc_free_unsized(void* ptr) {
    if (ptr) {
        #if CC_ALLOC_STATS
        if (g_alloc_stats.statistics_enabled) {
            atomic_fetch_add_explicit(&g_alloc_stats.free_count, 1, memory_order_relaxed);
        }
        #endif

        mi_free(ptr);
    }
}
```

### Cross-Thread Free Handling

mimalloc internally handles the complexity of freeing memory from a different thread than allocated:

```
Thread A                      Thread B
────────                      ────────
ptr = mi_malloc(64)
                              // Thread B can safely call:
                              mi_free(ptr)
                              // mimalloc handles internal transfer
```

This is crucial for SMR, where nodes are often:
1. Allocated by thread A (during insert)
2. Retired by thread B (during delete)
3. Reclaimed by thread C (during SMR poll)

### Cache-Line Alignment

For lock-free structures, nodes should be cache-line aligned to prevent false sharing:

```c
#define CC_CACHE_LINE_SIZE 64

// Allocate cache-line aligned node
static inline void* cc_alloc_node(size_t size) {
    // Round up to cache line boundary
    size_t aligned_size = (size + CC_CACHE_LINE_SIZE - 1) & ~(CC_CACHE_LINE_SIZE - 1);
    return cc_alloc_aligned(aligned_size, CC_CACHE_LINE_SIZE);
}
```

### Statistics API

```c
// Enable/disable statistics collection
void cc_alloc_stats_enable(bool enable);

// Get current statistics
typedef struct {
    uint64_t alloc_count;
    uint64_t free_count;
    uint64_t alloc_bytes;
    uint64_t free_bytes;
    uint64_t current_allocated;  // alloc_bytes - free_bytes
} cc_alloc_snapshot_t;

cc_alloc_snapshot_t cc_alloc_stats_snapshot(void);

// Reset statistics
void cc_alloc_stats_reset(void);
```

## API Surface

### C API

```c
// Core allocation functions
void* cc_alloc(size_t size);
void* cc_calloc(size_t count, size_t size);
void* cc_alloc_aligned(size_t size, size_t alignment);
void* cc_alloc_node(size_t size);  // Cache-line aligned

// Deallocation
void cc_free(void* ptr, size_t size);
void cc_free_unsized(void* ptr);

// Statistics
void cc_alloc_stats_enable(bool enable);
cc_alloc_snapshot_t cc_alloc_stats_snapshot(void);
void cc_alloc_stats_reset(void);
```

### Python API

```python
from concurrent_collections import config

# Enable allocation statistics
config.enable_alloc_statistics = True

# Get allocation snapshot
stats = config.alloc_stats()
print(f"Allocated: {stats.alloc_count} blocks, {stats.alloc_bytes} bytes")
print(f"Freed: {stats.free_count} blocks, {stats.free_bytes} bytes")
print(f"Current: {stats.current_allocated} bytes")

# Reset statistics
config.reset_alloc_stats()
```

## Integration with SMR

The SMR layer uses `mimalloc_glue` for deferred freeing:

```c
// In SMR reclamation callback
static void smr_free_callback(void* node) {
    // SMR has determined it's safe to free this node
    cc_free(node, sizeof(SkipListNode));
}

// Node retirement (called when node is logically removed)
void smr_retire(smr_context_t* ctx, void* node, size_t size) {
    // Add to deferred list - NOT freed yet
    retire_list_add(ctx->retire_list, node, size, smr_free_callback);
}

// Reclamation (called periodically)
void smr_poll(smr_context_t* ctx) {
    // Free nodes that are safe to reclaim
    retire_list_t* safe = get_safe_nodes(ctx);
    for_each(safe, node) {
        node->free_callback(node->ptr);  // Calls cc_free via callback
    }
}
```

## Design Decisions

| Decision | Choice | Rationale |
|----------|--------|-----------|
| Allocator | mimalloc | CPython 3.13t default, excellent concurrent perf |
| Statistics | Optional (compile-time) | Zero overhead when disabled |
| Size tracking | Optional | mimalloc tracks internally; we track for stats |
| Alignment | Cache-line (64 bytes) | Prevents false sharing in lock-free structs |
| Cross-thread | Rely on mimalloc | mimalloc handles this internally |

## Performance Considerations

### Allocation Overhead

| Operation | Cost | Notes |
|-----------|------|-------|
| `cc_alloc` | ~10-50ns | mimalloc thread-local fast path |
| `cc_alloc_aligned` | ~15-60ns | Slight overhead for alignment |
| `cc_free` | ~10-40ns | Fast if same thread allocated |
| Cross-thread free | ~50-100ns | mimalloc internal transfer |

### Memory Overhead

| Overhead Type | Size | Notes |
|---------------|------|-------|
| mimalloc metadata | ~8-16 bytes/alloc | Internal tracking |
| Cache-line padding | Up to 63 bytes/node | For alignment |
| Statistics (if enabled) | ~0 bytes | Uses atomics, no per-alloc |

## Configuration

```c
// Compile-time options
#define CC_ALLOC_STATS 1        // Enable statistics (default: 0 in release)
#define CC_CACHE_LINE_SIZE 64   // Cache line size (auto-detected if possible)
```

## Thread Safety

All functions are thread-safe:
- `cc_alloc*` functions are thread-safe via mimalloc's thread-local heaps
- `cc_free` is thread-safe for cross-thread freeing
- Statistics use atomic operations with relaxed ordering (sufficient for counters)

## Error Handling

| Error | Detection | Response |
|-------|-----------|----------|
| Allocation failure | `mi_malloc` returns NULL | Return NULL, caller handles |
| Invalid size (0) | Size check | Return NULL |
| Double free | Not detected | Undefined behavior (rely on ASAN in tests) |
| Invalid pointer | Not detected | Undefined behavior (rely on ASAN in tests) |

## Testing Strategy

See `tests.md` for detailed test coverage.

## Instrumentation & Profiling

### MemoryProfiler

The `MemoryProfiler` provides comprehensive memory allocation analysis for performance tuning and debugging.

#### Features Overview

| Feature | Purpose | Overhead |
|---------|---------|----------|
| **Allocation Histogram** | Distribution of allocation sizes | Low |
| **Cross-Thread Tracking** | Frees on different thread than alloc | Medium |
| **Fragmentation Metrics** | Internal/external fragmentation | Low |
| **Peak Memory Watermark** | Maximum memory usage over time | Low |
| **Allocation Rate** | Allocs/sec with moving average | Low |
| **Latency Percentiles** | P50/P95/P99/P99.9 for alloc/free | Medium |
| **Per-Thread Breakdown** | Stats per thread (free-threaded) | Medium |
| **Leak Detection** | Track allocations never freed | High |

#### Data Structures

```python
@dataclass
class AllocationRecord:
    """Individual allocation tracking (when leak detection enabled)."""
    ptr: int                    # Memory address
    size: int                   # Allocation size
    timestamp: float            # When allocated
    thread_id: int              # Allocating thread
    stack_trace: list[str] | None  # Optional call stack

@dataclass
class SizeHistogram:
    """Distribution of allocation sizes."""
    buckets: dict[str, int]     # "1-8": count, "9-16": count, etc.
    total_count: int
    total_bytes: int

    def hot_sizes(self, top_n: int = 5) -> list[tuple[str, int]]:
        """Return most frequent allocation size ranges."""
        ...

@dataclass
class ThreadMemoryStats:
    """Per-thread memory statistics."""
    thread_id: int
    thread_name: str | None
    alloc_count: int
    free_count: int
    alloc_bytes: int
    free_bytes: int
    cross_thread_frees_sent: int      # Frees of ptrs allocated by this thread
    cross_thread_frees_received: int  # Frees this thread did for other threads

@dataclass
class FragmentationMetrics:
    """Memory fragmentation analysis."""
    internal_fragmentation: float     # Wasted space within allocations (padding)
    external_fragmentation: float     # Wasted space between allocations
    largest_free_block: int           # Bytes
    free_block_count: int
    utilization: float                # allocated / (allocated + free)

@dataclass
class MemoryProfilerReport:
    """Complete memory profiler report."""
    # Basic statistics
    alloc_count: int
    free_count: int
    alloc_bytes: int
    free_bytes: int
    current_allocated: int
    peak_allocated: int

    # Rate metrics
    alloc_rate: float                 # Allocations per second
    free_rate: float                  # Frees per second
    bytes_rate: float                 # Bytes allocated per second

    # Latency percentiles (nanoseconds)
    alloc_latency_p50: float
    alloc_latency_p95: float
    alloc_latency_p99: float
    alloc_latency_p999: float
    free_latency_p50: float
    free_latency_p95: float
    free_latency_p99: float
    free_latency_p999: float

    # Cross-thread analysis
    cross_thread_free_count: int
    cross_thread_free_pct: float

    # Distributions
    size_histogram: SizeHistogram
    thread_stats: list[ThreadMemoryStats]
    fragmentation: FragmentationMetrics

    # Leak detection (if enabled)
    leaked_allocations: list[AllocationRecord] | None
    leaked_bytes: int

    # Timing
    duration_seconds: float
    start_time: datetime
    end_time: datetime
```

#### Profiler API

```python
class MemoryProfiler:
    def __init__(
        self,
        *,
        track_sizes: bool = True,
        track_latency: bool = True,
        track_per_thread: bool = False,
        track_cross_thread: bool = True,
        detect_leaks: bool = False,
        capture_stacks: bool = False,      # For leak detection
        sample_rate: float = 1.0,          # 1.0 = all, 0.1 = 10%
        latency_buckets: int = 1000,       # For percentile calculation
    ):
        """Initialize memory profiler with specified features."""
        ...

    def __enter__(self) -> 'MemoryProfiler':
        """Start profiling."""
        ...

    def __exit__(self, *args) -> None:
        """Stop profiling."""
        ...

    def start(self) -> None:
        """Start profiling (alternative to context manager)."""
        ...

    def stop(self) -> None:
        """Stop profiling."""
        ...

    def snapshot(self) -> MemoryProfilerReport:
        """Get current statistics without stopping."""
        ...

    def report(self) -> MemoryProfilerReport:
        """Get final report (call after stop)."""
        ...

    def reset(self) -> None:
        """Reset all statistics."""
        ...

    # Export methods
    def to_json(self, path: str | Path) -> None:
        """Export report to JSON."""
        ...

    def to_csv(self, path: str | Path) -> None:
        """Export report to CSV."""
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
from concurrent_collections import MemoryProfiler, SkipListMap

# Basic profiling
with MemoryProfiler() as prof:
    m = SkipListMap()
    for i in range(100000):
        m[f"key_{i}"] = f"value_{i}"

report = prof.report()
print(f"Peak memory: {report.peak_allocated / 1024**2:.1f} MB")
print(f"Alloc latency P99: {report.alloc_latency_p99:.0f} ns")
print(f"Cross-thread frees: {report.cross_thread_free_pct:.1f}%")

# Size distribution analysis
print("\nHot allocation sizes:")
for size_range, count in report.size_histogram.hot_sizes(5):
    print(f"  {size_range}: {count:,} allocations")

# Leak detection
with MemoryProfiler(detect_leaks=True, capture_stacks=True) as prof:
    # ... workload that might leak ...
    pass

report = prof.report()
if report.leaked_bytes > 0:
    print(f"LEAK: {report.leaked_bytes} bytes in {len(report.leaked_allocations)} allocations")
    for leak in report.leaked_allocations[:5]:
        print(f"  {leak.size} bytes at {leak.timestamp}")
        if leak.stack_trace:
            for frame in leak.stack_trace[:3]:
                print(f"    {frame}")

# Per-thread analysis (free-threaded Python)
with MemoryProfiler(track_per_thread=True) as prof:
    # ... multi-threaded workload ...
    pass

report = prof.report()
for ts in report.thread_stats:
    print(f"Thread {ts.thread_id}: {ts.alloc_count} allocs, "
          f"{ts.cross_thread_frees_sent} cross-thread frees sent")

# Export to HTML dashboard
prof.to_html("memory_report.html")
```

#### HTML Dashboard

The HTML report includes interactive visualizations:

1. **Memory Timeline** - Allocated bytes over time with peak marker
2. **Allocation Size Heatmap** - Size distribution visualization
3. **Latency Distribution** - Histogram of alloc/free latencies
4. **Thread Activity** - Per-thread allocation patterns
5. **Cross-Thread Flow** - Sankey diagram of cross-thread frees
6. **Fragmentation Gauge** - Current fragmentation level
7. **Recommendations** - Automated suggestions based on findings

#### Prometheus Metrics

```prometheus
# Memory allocation metrics
cc_memory_alloc_total 1523456
cc_memory_free_total 1523400
cc_memory_alloc_bytes_total 98765432
cc_memory_free_bytes_total 98760000
cc_memory_current_bytes 5432
cc_memory_peak_bytes 102400000

# Latency metrics (histogram)
cc_memory_alloc_latency_bucket{le="10"} 1000000
cc_memory_alloc_latency_bucket{le="50"} 1400000
cc_memory_alloc_latency_bucket{le="100"} 1500000
cc_memory_alloc_latency_bucket{le="+Inf"} 1523456

# Cross-thread metrics
cc_memory_cross_thread_free_total 45678
cc_memory_cross_thread_free_ratio 0.03

# Fragmentation
cc_memory_fragmentation_internal 0.12
cc_memory_fragmentation_external 0.05
```

### Jupyter Notebook Integration

See `examples/memory_performance_analysis.ipynb` for interactive analysis.

## Open Questions

| Question | Options | Current Leaning |
|----------|---------|-----------------|
| Custom allocator support | Support / Not support | Not support (keep simple) |
| Per-container stats | Aggregate / Per-container | Aggregate (simpler) |
| Debug fill patterns | Enable / Disable | Enable in debug builds only |
