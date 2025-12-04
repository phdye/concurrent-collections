# comparator — Design

## Overview

The `comparator` module provides a unified comparison dispatch system for ordered containers. It allows users to customize key ordering through multiple mechanisms: natural ordering via `__lt__`, Python callables, key functions, and high-performance native function pointers. The design prioritizes the common case (natural ordering) while providing efficient paths for performance-critical custom ordering via Rust closures or C/Cython functions.

## Dependencies

| Dependency | Purpose |
|------------|---------|
| config | Runtime configuration for comparison behavior |
| PyO3 | Python-Rust bindings (if Rust implementation) |
| Python C API | `PyObject_RichCompareBool`, exception handling (if C implementation) |

## Implementation Language Note

This design supports multiple implementation approaches (decision pending):
- **Rust with PyO3**: Native Rust comparators via trait objects/closures
- **C extension**: C function pointers via Cython or direct C
- **C++ with pybind11**: C++ functors

The examples below show both C and Rust implementations. The final choice will be made during implementation planning.

## Architecture

### Core Data Structure

```c
// Function pointer type for C comparators
// Returns: negative if a < b, zero if a == b, positive if a > b
typedef int (*cc_cmp_func)(PyObject *a, PyObject *b, void *context);

// Comparator types
typedef enum {
    CC_CMP_NATURAL,     // Use PyObject_RichCompareBool (default)
    CC_CMP_C_FUNC,      // C function pointer (fastest custom)
    CC_CMP_KEY_FUNC,    // Python key function (extract once)
    CC_CMP_PYTHON       // Python callable (slowest)
} cc_cmp_type_t;

// Comparator structure
typedef struct {
    PyObject_HEAD
    cc_cmp_type_t type;
    union {
        cc_cmp_func c_func;       // For CC_CMP_C_FUNC
        PyObject *py_callable;    // For CC_CMP_PYTHON or CC_CMP_KEY_FUNC
    };
    void *context;                // Optional context for C func
    PyObject *context_ref;        // Python object to prevent GC
    bool owns_context;            // Whether to free context on dealloc
} ComparatorObject;
```

### Comparison Dispatch

```c
static inline int cc_compare(ComparatorObject *cmp, PyObject *a, PyObject *b) {
    switch (cmp->type) {
        case CC_CMP_NATURAL:
            return cc_compare_natural(a, b);

        case CC_CMP_C_FUNC:
            // Fastest path - direct C function call
            return cmp->c_func(a, b, cmp->context);

        case CC_CMP_KEY_FUNC:
            // Extract keys, then compare naturally
            return cc_compare_by_key(cmp, a, b);

        case CC_CMP_PYTHON:
            // Slowest - full Python call protocol
            return cc_compare_python(cmp, a, b);
    }
    return 0;  // Should never reach
}

static inline int cc_compare_natural(PyObject *a, PyObject *b) {
    // Three-way comparison using rich compare
    int lt = PyObject_RichCompareBool(a, b, Py_LT);
    if (lt < 0) return 0;  // Exception
    if (lt) return -1;

    int gt = PyObject_RichCompareBool(a, b, Py_GT);
    if (gt < 0) return 0;  // Exception
    if (gt) return 1;

    return 0;  // Equal
}
```

### Built-in C Comparators

```c
// Reverse ordering comparator
static int cmp_reverse(PyObject *a, PyObject *b, void *ctx) {
    return -cc_compare_natural(a, b);
}

// Optimized numeric comparator (avoids rich compare for int/float)
static int cmp_numeric(PyObject *a, PyObject *b, void *ctx) {
    // Fast path for same-type comparisons
    if (PyLong_Check(a) && PyLong_Check(b)) {
        long va = PyLong_AsLong(a);
        long vb = PyLong_AsLong(b);
        return (va > vb) - (va < vb);
    }
    if (PyFloat_Check(a) && PyFloat_Check(b)) {
        double va = PyFloat_AS_DOUBLE(a);
        double vb = PyFloat_AS_DOUBLE(b);
        return (va > vb) - (va < vb);
    }
    // Fall back to natural comparison
    return cc_compare_natural(a, b);
}

// Optimized string comparator (locale-unaware)
static int cmp_string(PyObject *a, PyObject *b, void *ctx) {
    if (PyUnicode_Check(a) && PyUnicode_Check(b)) {
        return PyUnicode_Compare(a, b);
    }
    return cc_compare_natural(a, b);
}
```

### Key Function Handling

For key functions (like `sorted(key=...)`), keys are extracted at insertion time and stored with the node:

```c
// In SkipListNode
typedef struct SkipListNode {
    PyObject *key;          // Original key
    PyObject *sort_key;     // Extracted sort key (if using key function)
    PyObject *value;
    // ...
} SkipListNode;

// Extraction at insertion
PyObject *sort_key = key;
if (cmp->type == CC_CMP_KEY_FUNC) {
    sort_key = PyObject_CallOneArg(cmp->py_callable, key);
    if (!sort_key) return -1;  // Exception
}
// Store sort_key in node

// Comparison uses sort_key
int result = cc_compare(cmp, node_a->sort_key, node_b->sort_key);
```

## API Surface

### Python API

```python
class Comparator:
    """Key comparison dispatcher for ordered containers."""

    # Built-in comparators (return Comparator instances)
    @staticmethod
    def natural() -> Comparator:
        """Default __lt__ ordering."""

    @staticmethod
    def reverse() -> Comparator:
        """Reverse of natural ordering."""

    @staticmethod
    def numeric() -> Comparator:
        """Optimized for int/float keys."""

    @staticmethod
    def string() -> Comparator:
        """Optimized for str keys (locale-unaware)."""

    # Custom comparators
    @staticmethod
    def from_cfunc(func_ptr: int, context=None, prevent_gc: bool = False) -> Comparator:
        """
        Create comparator from C function pointer.

        Args:
            func_ptr: Address of C function with signature:
                      int cmp(PyObject *a, PyObject *b, void *context)
            context: Optional context passed to each comparison
            prevent_gc: If True, hold reference to context to prevent GC
        """

    # Properties
    @property
    def type(self) -> str:
        """Return comparator type: 'natural', 'c_func', 'key_func', or 'python'."""
```

## User Options for Custom Comparators

Users have multiple options for creating custom comparators, each with different trade-offs:

### Option Comparison

| Option | Performance | Ease of Use | Build Requirements | Best For |
|--------|-------------|-------------|-------------------|----------|
| Python callable | ~10% | Easiest | None | Prototyping, non-critical |
| Key function | ~100% | Easy | None | Transform-based ordering |
| Cython function | ~80-95% | Moderate | Cython build | Performance-critical Python projects |
| Rust comparator | ~80-95% | Moderate | Rust build | Rust extension developers |
| C ABI function | ~80-95% | Advanced | C/Rust/other compiler | Maximum interop, any language |

### Option 1: Python Callable (Easiest)

```python
# No build step required
m = SkipListMap(cmp=lambda a, b: len(a) - len(b))

# Or a function
def by_priority(a, b):
    return a.priority - b.priority

m = SkipListMap(cmp=by_priority)
```

**Pros:** No compilation, works immediately
**Cons:** ~10x slower per comparison

### Option 2: Key Function (Familiar)

```python
# Like sorted(key=...)
m = SkipListMap(key=str.lower)           # Case-insensitive
m = SkipListMap(key=lambda x: -x)        # Reverse numeric
m = SkipListMap(key=lambda x: x.name)    # By attribute
```

**Pros:** No compilation, keys extracted once (amortized cost)
**Cons:** Key stored per entry (memory overhead)

### Option 3: Cython Function (High Performance)

```cython
# my_comparators.pyx
cdef int reverse_cmp(PyObject* a, PyObject* b, void* ctx) noexcept nogil:
    cdef long va = (<object>a)
    cdef long vb = (<object>b)
    return (vb > va) - (vb < va)

def get_reverse():
    from concurrent_collections import Comparator
    return Comparator.from_cfunc(<Py_uintptr_t>reverse_cmp)
```

```python
# Usage
from my_comparators import get_reverse
m = SkipListMap(cmp=get_reverse())
```

**Pros:** Near-native performance, Python ecosystem
**Cons:** Requires Cython build step

### Option 4: Rust Comparator (Type-Safe)

```rust
// For Rust extension developers
impl PyComparator for MyComparator {
    fn compare(&self, py: Python, a: &PyAny, b: &PyAny) -> PyResult<Ordering> {
        // Custom logic with Rust type safety
    }
}
```

**Pros:** Memory safety, Rust tooling
**Cons:** Requires Rust build, PyO3 knowledge

### Option 5: C ABI Function (Maximum Interop)

Any language that can produce C ABI functions works. The C ABI is the universal interface that all options ultimately use.

**Required C ABI Signature:**
```c
int cmp_func(PyObject *a, PyObject *b, void *context);
// Returns: negative if a < b, zero if a == b, positive if a > b
```

#### Rust with C ABI (Recommended for Rust Users)

```rust
// my_comparators/src/lib.rs
use std::os::raw::{c_int, c_void};
use pyo3::ffi::PyObject;
use pyo3::Python;

/// Reverse numeric comparator with C ABI
///
/// # Safety
/// Caller must ensure a and b are valid PyObject pointers
#[no_mangle]
pub extern "C" fn reverse_numeric_cmp(
    a: *mut PyObject,
    b: *mut PyObject,
    _ctx: *mut c_void,
) -> c_int {
    if a.is_null() || b.is_null() {
        return 0;
    }

    Python::with_gil(|py| {
        unsafe {
            let a_any = pyo3::PyAny::from_borrowed_ptr(py, a);
            let b_any = pyo3::PyAny::from_borrowed_ptr(py, b);

            // Try fast path for integers
            if let (Ok(va), Ok(vb)) = (a_any.extract::<i64>(), b_any.extract::<i64>()) {
                return match vb.cmp(&va) {
                    std::cmp::Ordering::Less => -1,
                    std::cmp::Ordering::Equal => 0,
                    std::cmp::Ordering::Greater => 1,
                };
            }

            // Fallback to Python comparison (reversed)
            if b_any.lt(a_any).unwrap_or(false) { -1 }
            else if b_any.gt(a_any).unwrap_or(false) { 1 }
            else { 0 }
        }
    })
}

/// Case-insensitive string comparator
#[no_mangle]
pub extern "C" fn case_insensitive_cmp(
    a: *mut PyObject,
    b: *mut PyObject,
    _ctx: *mut c_void,
) -> c_int {
    Python::with_gil(|py| {
        unsafe {
            let a_any = pyo3::PyAny::from_borrowed_ptr(py, a);
            let b_any = pyo3::PyAny::from_borrowed_ptr(py, b);

            match (a_any.extract::<String>(), b_any.extract::<String>()) {
                (Ok(sa), Ok(sb)) => {
                    match sa.to_lowercase().cmp(&sb.to_lowercase()) {
                        std::cmp::Ordering::Less => -1,
                        std::cmp::Ordering::Equal => 0,
                        std::cmp::Ordering::Greater => 1,
                    }
                }
                _ => 0,
            }
        }
    })
}

/// Get function pointer for Python registration
#[no_mangle]
pub extern "C" fn get_reverse_numeric_ptr() -> usize {
    reverse_numeric_cmp as usize
}

#[no_mangle]
pub extern "C" fn get_case_insensitive_ptr() -> usize {
    case_insensitive_cmp as usize
}
```

**Python wrapper module:**
```python
# my_comparators/__init__.py
import ctypes
from pathlib import Path
from concurrent_collections import Comparator

# Load the Rust shared library
_lib_path = Path(__file__).parent / "libmy_comparators.so"
_lib = ctypes.CDLL(str(_lib_path))

# Get function pointers
_lib.get_reverse_numeric_ptr.restype = ctypes.c_size_t
_lib.get_case_insensitive_ptr.restype = ctypes.c_size_t

def reverse_numeric() -> Comparator:
    """Reverse numeric ordering comparator."""
    return Comparator.from_cfunc(_lib.get_reverse_numeric_ptr())

def case_insensitive() -> Comparator:
    """Case-insensitive string comparator."""
    return Comparator.from_cfunc(_lib.get_case_insensitive_ptr())
```

**Usage:**
```python
from concurrent_collections import SkipListMap
from my_comparators import reverse_numeric, case_insensitive

# Reverse numeric ordering
m = SkipListMap(cmp=reverse_numeric())
m[1], m[10], m[5] = "a", "b", "c"
list(m.keys())  # [10, 5, 1]

# Case-insensitive strings
m2 = SkipListMap(cmp=case_insensitive())
m2["Apple"] = 1
m2["banana"] = 2
list(m2.keys())  # ['Apple', 'banana'] - sorted case-insensitively
```

#### Pure C

```c
// my_comparators.c
#include <Python.h>

int reverse_numeric_cmp(PyObject *a, PyObject *b, void *ctx) {
    if (PyLong_Check(a) && PyLong_Check(b)) {
        long va = PyLong_AsLong(a);
        long vb = PyLong_AsLong(b);
        return (vb > va) - (vb < va);  // Reversed
    }
    // Fallback to Python comparison
    int result = PyObject_RichCompareBool(b, a, Py_LT);
    if (result > 0) return -1;
    result = PyObject_RichCompareBool(b, a, Py_GT);
    if (result > 0) return 1;
    return 0;
}
```

#### Zig

```zig
// my_comparators.zig
const std = @import("std");
const py = @cImport(@cInclude("Python.h"));

export fn reverse_numeric_cmp(
    a: *py.PyObject,
    b: *py.PyObject,
    ctx: ?*anyopaque,
) callconv(.C) c_int {
    _ = ctx;
    // Implementation using Python C API
    // ...
}
```

**Pros:** Works from any language, maximum performance, universal compatibility
**Cons:** Requires external build, manual memory management, ctypes loading

### Recommendation Flow

```
Need custom ordering?
    │
    ├─► Prototyping/testing?
    │       └─► Use Python callable
    │
    ├─► Just need to sort by a field/transform?
    │       └─► Use key function
    │
    ├─► Performance critical?
    │       │
    │       ├─► Already using Cython?
    │       │       └─► Use Cython function
    │       │
    │       ├─► Already using Rust?
    │       │       └─► Use Rust comparator
    │       │
    │       └─► Other language / maximum control?
    │               └─► Use C ABI function
    │
    └─► Use natural ordering (default)
```

## Measuring Comparator Performance

Before investing time in writing a custom C ABI comparator, users should measure whether comparison overhead is actually a bottleneck. This section provides tools and techniques for making data-driven optimization decisions.

### When to Consider Optimization

| Scenario | Comparisons/sec | Comparison % of Time | Recommendation |
|----------|-----------------|----------------------|----------------|
| Low-volume API | < 10K | < 1% | Keep Python callable |
| Moderate throughput | 10K-100K | 1-10% | Consider key function |
| High throughput | 100K-1M | 10-30% | Consider native comparator |
| Ultra-high throughput | > 1M | > 30% | Definitely optimize |

### Quick Benchmark: Is Comparison Your Bottleneck?

```python
import time
from concurrent_collections import SkipListMap

def benchmark_comparator(map_class, cmp, n_items=100_000, n_ops=100_000):
    """Benchmark comparison overhead for a given comparator."""
    import random

    # Setup: populate map
    m = map_class(cmp=cmp) if cmp else map_class()
    keys = [random.randint(0, n_items * 10) for _ in range(n_items)]
    for k in keys:
        m[k] = k

    # Benchmark: random lookups
    lookup_keys = [random.randint(0, n_items * 10) for _ in range(n_ops)]

    start = time.perf_counter()
    for k in lookup_keys:
        _ = m.get(k)
    elapsed = time.perf_counter() - start

    ops_per_sec = n_ops / elapsed
    ns_per_op = (elapsed / n_ops) * 1e9

    return {
        'ops_per_sec': ops_per_sec,
        'ns_per_op': ns_per_op,
        'total_time': elapsed,
    }

# Compare different comparator types
results = {}

# Natural ordering (baseline)
results['natural'] = benchmark_comparator(SkipListMap, None)

# Python callable
results['python'] = benchmark_comparator(
    SkipListMap,
    lambda a, b: (a > b) - (a < b)
)

# Key function
results['key'] = benchmark_comparator(
    SkipListMap,
    None,  # Use key= parameter instead
)

# Print comparison
print(f"{'Type':<15} {'ops/sec':>12} {'ns/op':>10} {'vs natural':>12}")
print("-" * 52)
baseline = results['natural']['ops_per_sec']
for name, r in results.items():
    ratio = r['ops_per_sec'] / baseline
    print(f"{name:<15} {r['ops_per_sec']:>12,.0f} {r['ns_per_op']:>10.1f} {ratio:>11.1%}")
```

**Example output:**
```
Type              ops/sec      ns/op   vs natural
----------------------------------------------------
natural         1,250,000       800.0      100.0%
python            125,000     8,000.0       10.0%
key             1,100,000       909.0       88.0%
```

### Detailed Profiling with cProfile

```python
import cProfile
import pstats
from concurrent_collections import SkipListMap

def profile_comparator_usage():
    """Profile to see where time is spent."""
    m = SkipListMap(cmp=lambda a, b: (a > b) - (a < b))

    # Your workload
    for i in range(100_000):
        m[i] = i
    for i in range(100_000):
        _ = m.get(i)

# Profile and analyze
profiler = cProfile.Profile()
profiler.enable()
profile_comparator_usage()
profiler.disable()

# Show top time consumers
stats = pstats.Stats(profiler)
stats.sort_stats('cumulative')
stats.print_stats(20)

# Look for comparison-related entries:
# - <lambda> calls indicate Python comparator overhead
# - Large cumtime in comparison functions = optimization target
```

### Micro-benchmark: Comparator Function Alone

```python
import timeit

# Isolate just the comparison function overhead
def benchmark_cmp_function(cmp_func, a, b, iterations=1_000_000):
    """Benchmark raw comparator function call overhead."""

    def test():
        cmp_func(a, b)

    time_per_call = timeit.timeit(test, number=iterations) / iterations
    return time_per_call * 1e9  # nanoseconds

# Test different comparison approaches
a, b = 42, 100

# Natural Python comparison
natural_ns = benchmark_cmp_function(lambda a, b: (a > b) - (a < b), a, b)

# Your custom comparator
def my_complex_cmp(a, b):
    # Simulate complex comparison logic
    return (a > b) - (a < b)

custom_ns = benchmark_cmp_function(my_complex_cmp, a, b)

print(f"Natural comparison: {natural_ns:.1f} ns/call")
print(f"Custom comparison:  {custom_ns:.1f} ns/call")
print(f"Overhead: {custom_ns - natural_ns:.1f} ns/call")

# Rule of thumb: if overhead > 100ns and you do >100K comparisons/sec,
# consider a native comparator
```

### Container-Level Statistics

The library provides built-in statistics for measuring comparison overhead:

```python
from concurrent_collections import SkipListMap, config

# Enable statistics collection
config.enable_statistics = True

m = SkipListMap(cmp=my_comparator)

# Your workload...
for i in range(10_000):
    m[i] = i

# Get statistics
stats = m.statistics()
print(f"Total comparisons: {stats['comparison_count']:,}")
print(f"Avg comparisons per put: {stats['avg_comparisons_per_put']:.1f}")
print(f"Total comparison time: {stats['comparison_time_ns'] / 1e6:.2f} ms")
print(f"Comparison % of total: {stats['comparison_time_pct']:.1f}%")

# Reset for next measurement
m.reset_statistics()
```

### Real-World Decision Example

```python
from concurrent_collections import SkipListMap
import time

# Scenario: Case-insensitive string map with 1M entries
N = 1_000_000

# Option 1: Python callable
def py_case_insensitive(a, b):
    a_lower, b_lower = a.lower(), b.lower()
    return (a_lower > b_lower) - (a_lower < b_lower)

# Option 2: Key function (extract once)
# m = SkipListMap(key=str.lower)

# Measure Option 1
start = time.perf_counter()
m1 = SkipListMap(cmp=py_case_insensitive)
for i in range(N):
    m1[f"Key{i:07d}"] = i
insert_time = time.perf_counter() - start

print(f"Python callable: {N:,} inserts in {insert_time:.2f}s")
print(f"  = {N/insert_time:,.0f} inserts/sec")

# Calculate: is optimization worth it?
# With ~20 comparisons per insert (log2(1M) ≈ 20):
comparisons = N * 20
comparison_overhead_estimate = comparisons * 500e-9  # ~500ns per Python call
print(f"  Estimated comparison overhead: {comparison_overhead_estimate:.2f}s")
print(f"  Comparison % of insert time: {comparison_overhead_estimate/insert_time*100:.0f}%")

# If comparison % > 30%, optimization will help significantly
if comparison_overhead_estimate / insert_time > 0.3:
    print("  → RECOMMENDATION: Consider native comparator")
else:
    print("  → RECOMMENDATION: Python callable is fine")
```

### Profiling Native Comparators

For users who implement C ABI comparators, validate the improvement:

```python
def compare_implementations(implementations: dict, n_items=100_000):
    """Compare multiple comparator implementations."""
    import random

    results = {}
    test_keys = [f"key{random.randint(0, n_items*10):08d}" for _ in range(n_items)]

    for name, cmp in implementations.items():
        m = SkipListMap(cmp=cmp) if cmp else SkipListMap()

        # Measure insert
        start = time.perf_counter()
        for k in test_keys:
            m[k] = 1
        insert_time = time.perf_counter() - start

        # Measure lookup
        start = time.perf_counter()
        for k in test_keys:
            _ = m.get(k)
        lookup_time = time.perf_counter() - start

        results[name] = {
            'insert_ops_sec': n_items / insert_time,
            'lookup_ops_sec': n_items / lookup_time,
        }

    # Print comparison table
    print(f"{'Implementation':<20} {'Insert ops/s':>15} {'Lookup ops/s':>15} {'Speedup':>10}")
    print("-" * 65)

    baseline = results.get('python', list(results.values())[0])
    for name, r in results.items():
        speedup = r['lookup_ops_sec'] / baseline['lookup_ops_sec']
        print(f"{name:<20} {r['insert_ops_sec']:>15,.0f} {r['lookup_ops_sec']:>15,.0f} {speedup:>9.1f}x")

# Usage
from my_rust_comparators import case_insensitive_native

compare_implementations({
    'python': lambda a, b: (a.lower() > b.lower()) - (a.lower() < b.lower()),
    'key_func': None,  # Would use key=str.lower
    'native': case_insensitive_native(),
})
```

### Instrumentation API: Point-to-Point Measurement

The library provides an instrumentation API to measure comparator resource consumption relative to your overall program:

```python
from concurrent_collections import SkipListMap
from concurrent_collections.instrumentation import ComparatorProfiler

# Create container with your comparator
m = SkipListMap(cmp=my_custom_comparator)

# === Point A: Start measurement ===
profiler = ComparatorProfiler()
profiler.start()

# Your actual workload (not a synthetic benchmark)
for record in database_records:
    m[record.key] = record

results = []
for query in user_queries:
    results.append(m.get(query.key))

# === Point B: End measurement ===
report = profiler.stop()

# Get resource breakdown
print(report)
```

**Example output:**
```
ComparatorProfiler Report
=========================
Wall time:              2.345 sec
  Comparator time:      0.412 sec (17.6%)
  Other time:           1.933 sec (82.4%)

Comparisons:            1,234,567
  Avg per comparison:   334 ns

CPU time:               2.280 sec
  Comparator CPU:       0.398 sec (17.5%)

Memory allocated:       0 bytes (comparator uses no heap)

Recommendation: Comparator overhead is MODERATE (10-30%)
                Consider key function if not already using one.
```

#### Profiler API

```python
class ComparatorProfiler:
    """Measure comparator resource consumption relative to total program."""

    def __init__(
        self,
        *,
        sample_rate: float = 1.0,           # 1.0 = all comparisons, 0.01 = 1%
        trace_samples: int = 0,             # Number of comparisons to capture for debugging
        track_percentiles: bool = True,     # Compute P50/P95/P99 (slight overhead)
        logger: logging.Logger | None = None,
        log_interval: float | None = None,  # Log stats every N seconds
        threshold_pct: float | None = None, # Alert threshold (percentage)
        on_threshold: Callable[[ProfilerReport], None] | None = None,
    ):
        """
        Args:
            sample_rate: Fraction of comparisons to time (1.0 = all, 0.01 = 1%)
            trace_samples: Capture N comparison samples with operands for debugging
            track_percentiles: Whether to compute latency percentiles (adds overhead)
            logger: Logger for periodic stats during long workloads
            log_interval: Seconds between log messages (requires logger)
            threshold_pct: Alert when comparator overhead exceeds this percentage
            on_threshold: Callback when threshold exceeded
        """

    def start(self) -> None:
        """Begin profiling. Call at point A."""

    def stop(self) -> ProfilerReport:
        """End profiling. Call at point B. Returns report."""

    def reset(self) -> None:
        """Reset counters without stopping."""

    @property
    def report(self) -> ProfilerReport:
        """Get current report without stopping."""

    # Context manager support
    def __enter__(self) -> 'ComparatorProfiler':
        self.start()
        return self

    def __exit__(self, *args) -> None:
        self.stop()


class ProfilerReport:
    """Resource consumption report."""

    # Timing
    wall_time_sec: float           # Total wall clock time (A to B)
    comparator_time_sec: float     # Time spent in comparator functions
    comparator_time_pct: float     # comparator_time / wall_time * 100

    # Comparison counts
    comparison_count: int          # Total comparisons performed
    avg_comparison_ns: float       # Average nanoseconds per comparison

    # Latency percentiles (nanoseconds)
    p50_comparison_ns: float       # Median comparison latency
    p95_comparison_ns: float       # 95th percentile latency
    p99_comparison_ns: float       # 99th percentile latency
    p999_comparison_ns: float      # 99.9th percentile (tail latency)
    max_comparison_ns: float       # Maximum observed latency

    # CPU time (if available)
    cpu_time_sec: float | None
    comparator_cpu_sec: float | None
    comparator_cpu_pct: float | None

    # Memory (if tracked)
    comparator_alloc_bytes: int

    # Per-container breakdown
    containers: dict[str, ContainerStats]

    # Per-thread breakdown (for free-threaded Python)
    threads: dict[int, ThreadStats]

    # Sampled comparison traces (if tracing enabled)
    traces: list[ComparisonTrace]

    def __str__(self) -> str:
        """Human-readable report."""

    def to_dict(self) -> dict:
        """Machine-readable format."""

    def to_json(self, path: str | Path | None = None) -> str:
        """Export as JSON. If path provided, writes to file and returns path."""

    def to_csv(self, path: str | Path) -> None:
        """Export timing data as CSV for spreadsheet analysis."""

    def to_dataframe(self) -> 'pandas.DataFrame':
        """Export as pandas DataFrame for analysis in Jupyter/notebooks."""

    def to_html(self, path: str | Path) -> None:
        """Generate visual HTML report with charts."""

    def recommendation(self) -> str:
        """Suggest optimization based on measurements."""


class ThreadStats:
    """Per-thread comparison statistics."""
    thread_id: int
    thread_name: str | None
    comparison_count: int
    time_sec: float
    time_pct: float                # Percentage of total comparator time
    avg_comparison_ns: float


class ComparisonTrace:
    """Record of a sampled comparison for debugging."""
    timestamp_ns: int              # When comparison occurred
    container_name: str | None     # Which container
    a: object                      # First operand (repr, not actual object)
    b: object                      # Second operand (repr)
    result: int                    # Comparison result (-1, 0, 1)
    duration_ns: int               # How long this comparison took
    thread_id: int                 # Which thread
```

#### Context Manager Usage

```python
from concurrent_collections.instrumentation import ComparatorProfiler

m = SkipListMap(cmp=my_comparator)

# Simple context manager
with ComparatorProfiler() as profiler:
    # Point A (entering context)

    process_batch(m, data)

    # Point B (exiting context)

print(profiler.report)
print(f"Comparator consumed {profiler.report.comparator_time_pct:.1f}% of total time")
```

#### Multiple Containers

```python
from concurrent_collections import SkipListMap, TreeMap
from concurrent_collections.instrumentation import ComparatorProfiler

# Multiple containers with different comparators
map1 = SkipListMap(cmp=cmp_a, name="users")
map2 = TreeMap(cmp=cmp_b, name="orders")

with ComparatorProfiler() as profiler:
    # Your workload using both containers
    for user in users:
        map1[user.id] = user
    for order in orders:
        map2[order.id] = order

    # Queries
    for query in queries:
        user = map1.get(query.user_id)
        orders = map2.range(query.start, query.end)

# Per-container breakdown
for name, stats in profiler.report.containers.items():
    print(f"{name}: {stats.comparison_count:,} comparisons, "
          f"{stats.time_sec:.3f}s ({stats.time_pct:.1f}%)")
```

**Output:**
```
users: 50,000 comparisons, 0.125s (5.3%)
orders: 1,200,000 comparisons, 0.892s (37.8%)
```

#### Integration with Standard Profiling Tools

```python
import cProfile
from concurrent_collections.instrumentation import ComparatorProfiler

# Layer our profiler with cProfile for full picture
profiler = ComparatorProfiler()
cprofiler = cProfile.Profile()

profiler.start()
cprofiler.enable()

# Your workload
run_application()

cprofiler.disable()
report = profiler.stop()

# Now you have:
# 1. cProfile for overall hotspots
# 2. ComparatorProfiler for comparator-specific breakdown

print(f"\n=== Comparator Impact ===")
print(f"Comparator: {report.comparator_time_pct:.1f}% of wall time")
print(f"If this is high, see recommendations below:")
print(report.recommendation())
```

#### Lightweight Sampling Mode

For production use with minimal overhead:

```python
from concurrent_collections.instrumentation import ComparatorProfiler

# Sample 1% of comparisons (low overhead)
with ComparatorProfiler(sample_rate=0.01) as profiler:
    run_production_workload()

# Extrapolated results
print(f"Estimated comparisons: {profiler.report.comparison_count:,}")
print(f"Estimated comparator time: {profiler.report.comparator_time_pct:.1f}%")
```

#### Programmatic Decision Making

```python
from concurrent_collections.instrumentation import ComparatorProfiler, OptimizationLevel

with ComparatorProfiler() as profiler:
    run_workload()

# Get actionable recommendation
level = profiler.report.optimization_level

if level == OptimizationLevel.NONE_NEEDED:
    print("Comparator overhead is negligible (<5%)")
elif level == OptimizationLevel.CONSIDER_KEY_FUNCTION:
    print("Consider using key= parameter instead of cmp=")
elif level == OptimizationLevel.CONSIDER_NATIVE:
    print("Consider implementing a native comparator")
elif level == OptimizationLevel.CRITICAL:
    print("Comparator is a critical bottleneck (>50%)")

# Or get detailed recommendation string
print(profiler.report.recommendation())
```

#### Logging Integration

```python
import logging
from concurrent_collections.instrumentation import ComparatorProfiler

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger("myapp.perf")

with ComparatorProfiler(logger=logger, log_interval=10.0) as profiler:
    # Logs stats every 10 seconds during long-running workloads
    run_long_workload()
```

**Log output:**
```
INFO:myapp.perf:ComparatorProfiler [10.0s]: 234,567 comparisons, 18.2% of time
INFO:myapp.perf:ComparatorProfiler [20.0s]: 512,345 comparisons, 17.8% of time
INFO:myapp.perf:ComparatorProfiler [final]: 892,123 comparisons, 17.9% of time
```

#### Latency Percentiles

Averages hide outliers. Use percentiles to catch GC pauses, lock contention, and other tail latency issues:

```python
from concurrent_collections.instrumentation import ComparatorProfiler

with ComparatorProfiler(track_percentiles=True) as profiler:
    run_workload()

report = profiler.report

print(f"Latency distribution:")
print(f"  P50 (median):  {report.p50_comparison_ns:,.0f} ns")
print(f"  P95:           {report.p95_comparison_ns:,.0f} ns")
print(f"  P99:           {report.p99_comparison_ns:,.0f} ns")
print(f"  P99.9:         {report.p999_comparison_ns:,.0f} ns")
print(f"  Max:           {report.max_comparison_ns:,.0f} ns")

# Detect GC or contention issues
if report.p99_comparison_ns > report.p50_comparison_ns * 100:
    print("WARNING: High tail latency detected!")
    print("  This may indicate GC pauses or lock contention.")
```

**Example output:**
```
Latency distribution:
  P50 (median):  280 ns
  P95:           450 ns
  P99:           1,200 ns
  P99.9:         45,000 ns  <- GC pause!
  Max:           2,100,000 ns
```

#### Export Formats

Export profiling data for analysis in external tools:

```python
from concurrent_collections.instrumentation import ComparatorProfiler

with ComparatorProfiler() as profiler:
    run_workload()

report = profiler.report

# JSON export (for web dashboards, APIs)
json_str = report.to_json()
report.to_json("comparator_profile.json")

# CSV export (for spreadsheets)
report.to_csv("comparator_profile.csv")

# pandas DataFrame (for Jupyter notebooks)
df = report.to_dataframe()
print(df.describe())

# Plot in Jupyter
import matplotlib.pyplot as plt
df['comparison_time_ns'].hist(bins=50)
plt.xlabel('Comparison time (ns)')
plt.ylabel('Frequency')
plt.title('Comparison Latency Distribution')
plt.show()
```

**CSV output format:**
```csv
timestamp,container,thread_id,comparison_count,time_sec,avg_ns,p50_ns,p95_ns,p99_ns
2025-12-04T10:30:00,users,140234,50000,0.125,2500,280,450,1200
2025-12-04T10:30:00,orders,140234,1200000,0.892,743,280,420,980
2025-12-04T10:30:00,orders,140567,800000,0.612,765,290,440,1100
```

#### Thread-Level Breakdown

Critical for free-threaded Python (3.13+) to identify per-thread bottlenecks:

```python
from concurrent_collections.instrumentation import ComparatorProfiler
import threading

# Run multi-threaded workload
with ComparatorProfiler() as profiler:
    threads = [
        threading.Thread(target=worker, args=(shared_map,))
        for _ in range(8)
    ]
    for t in threads:
        t.start()
    for t in threads:
        t.join()

# Analyze per-thread breakdown
print(f"{'Thread ID':<12} {'Name':<15} {'Comparisons':>15} {'Time':>10} {'%':>8}")
print("-" * 65)

for thread_id, stats in profiler.report.threads.items():
    print(f"{thread_id:<12} {stats.thread_name or 'N/A':<15} "
          f"{stats.comparison_count:>15,} {stats.time_sec:>10.3f} "
          f"{stats.time_pct:>7.1f}%")

# Detect thread imbalance
times = [s.time_sec for s in profiler.report.threads.values()]
if max(times) > min(times) * 2:
    print("\nWARNING: Thread imbalance detected!")
    print("  Some threads spending much more time in comparisons.")
```

**Example output:**
```
Thread ID    Name            Comparisons       Time        %
-----------------------------------------------------------------
140234567890 Worker-0            312,456      0.125    12.5%
140234567891 Worker-1            298,234      0.119    11.9%
140234567892 Worker-2            315,678      0.126    12.6%
140234567893 Worker-3          1,245,678      0.498    49.8%  <- Imbalance!
```

#### Comparison Tracing

Capture actual comparison operands for debugging ordering issues:

```python
from concurrent_collections.instrumentation import ComparatorProfiler

# Capture 100 sample comparisons
with ComparatorProfiler(trace_samples=100) as profiler:
    run_workload_with_strange_ordering()

# Examine captured comparisons
print("Sampled comparisons:")
for i, trace in enumerate(profiler.report.traces[:10]):
    print(f"  [{i}] cmp({trace.a!r}, {trace.b!r}) = {trace.result}")
    print(f"      Container: {trace.container_name}, Thread: {trace.thread_id}")
    print(f"      Duration: {trace.duration_ns} ns")

# Find slow comparisons
slow = [t for t in profiler.report.traces if t.duration_ns > 10000]
if slow:
    print(f"\nFound {len(slow)} slow comparisons (>10μs):")
    for trace in slow[:5]:
        print(f"  cmp({trace.a!r}, {trace.b!r}) took {trace.duration_ns/1000:.1f}μs")
```

**Example output:**
```
Sampled comparisons:
  [0] cmp('apple', 'banana') = -1
      Container: fruits, Thread: 140234567890
      Duration: 285 ns
  [1] cmp('cherry', 'apple') = 1
      Container: fruits, Thread: 140234567890
      Duration: 290 ns
  [2] cmp(MyObject(id=42), MyObject(id=17)) = 1
      Container: objects, Thread: 140234567891
      Duration: 45230 ns  <- Slow!
```

#### HTML Report

Generate visual reports for sharing with teams:

```python
from concurrent_collections.instrumentation import ComparatorProfiler

with ComparatorProfiler(track_percentiles=True) as profiler:
    run_workload()

# Generate HTML report
profiler.report.to_html("comparator_report.html")
print("Report saved to comparator_report.html")
```

The HTML report includes:
- Summary statistics with color-coded recommendations
- Latency histogram chart
- Percentile breakdown chart
- Per-container table
- Per-thread table (if multi-threaded)
- Comparison trace table (if tracing enabled)
- Optimization recommendations

**Report sections:**
```
┌─────────────────────────────────────────────────────────────────┐
│  ComparatorProfiler Report - 2025-12-04 10:30:00               │
├─────────────────────────────────────────────────────────────────┤
│  SUMMARY                                                        │
│  Wall time: 2.345s | Comparator: 17.6% | Status: ⚠️ MODERATE    │
├─────────────────────────────────────────────────────────────────┤
│  [Latency Histogram Chart]                                      │
│  ████████████████████  P50: 280ns                               │
│  ██████████           P95: 450ns                                │
│  ███                  P99: 1,200ns                              │
├─────────────────────────────────────────────────────────────────┤
│  CONTAINERS                                                     │
│  users:  50,000 comparisons, 0.125s (5.3%)                     │
│  orders: 1,200,000 comparisons, 0.892s (37.8%)  ← Optimize!    │
├─────────────────────────────────────────────────────────────────┤
│  RECOMMENDATION                                                 │
│  Container 'orders' has high comparison overhead (37.8%).       │
│  Consider using key=str.lower instead of Python callable.       │
└─────────────────────────────────────────────────────────────────┘
```

#### Threshold Alerts

Get notified when comparator overhead exceeds acceptable limits:

```python
from concurrent_collections.instrumentation import ComparatorProfiler
import logging

logger = logging.getLogger("myapp.perf")

def handle_threshold_exceeded(report):
    """Called when comparator overhead exceeds threshold."""
    logger.warning(
        f"Comparator overhead alert: {report.comparator_time_pct:.1f}% "
        f"exceeds threshold"
    )
    # Send to monitoring system
    metrics.gauge("comparator.overhead_pct", report.comparator_time_pct)

    # Optionally dump detailed report
    report.to_json(f"/var/log/comparator_alert_{time.time()}.json")

# Alert when comparator exceeds 30% of execution time
with ComparatorProfiler(
    threshold_pct=30.0,
    on_threshold=handle_threshold_exceeded
) as profiler:
    run_production_workload()
```

**Alert modes:**

```python
# One-time alert (default)
ComparatorProfiler(
    threshold_pct=30.0,
    on_threshold=alert_callback
)

# Continuous monitoring with repeated alerts
ComparatorProfiler(
    threshold_pct=30.0,
    on_threshold=alert_callback,
    threshold_cooldown=60.0,  # Re-alert after 60 seconds
)

# Alert on specific conditions
def smart_alert(report):
    if report.comparator_time_pct > 50:
        send_critical_alert(report)
    elif report.p99_comparison_ns > 100_000:  # >100μs
        send_latency_alert(report)

ComparatorProfiler(
    threshold_pct=20.0,  # Check starts at 20%
    on_threshold=smart_alert
)
```

**Integration with monitoring systems:**

```python
# Prometheus/Grafana
from prometheus_client import Gauge, Histogram

comparator_overhead = Gauge('comparator_overhead_percent', 'Comparator time %')
comparator_latency = Histogram('comparator_latency_ns', 'Comparison latency')

def export_to_prometheus(report):
    comparator_overhead.set(report.comparator_time_pct)
    for trace in report.traces:
        comparator_latency.observe(trace.duration_ns)

# Datadog
from datadog import statsd

def export_to_datadog(report):
    statsd.gauge('comparator.overhead_pct', report.comparator_time_pct)
    statsd.gauge('comparator.p99_ns', report.p99_comparison_ns)
    statsd.increment('comparator.total_count', report.comparison_count)
```

### Decision Checklist

Before writing a native comparator, verify:

- [ ] **Measured in context**: Used `ComparatorProfiler` during actual workload
- [ ] **Identified bottleneck**: Comparator is >20% of wall time in your application
- [ ] **Quantified impact**: Know exact comparison count and time
- [ ] **Estimated improvement**: Native comparator would provide >2x speedup
- [ ] **Justified complexity**: Maintenance cost is worth the performance gain
- [ ] **Tested correctness**: Native comparator produces identical ordering

### C API

```c
// Create comparators
ComparatorObject* Comparator_Natural(void);
ComparatorObject* Comparator_Reverse(void);
ComparatorObject* Comparator_Numeric(void);
ComparatorObject* Comparator_String(void);
ComparatorObject* Comparator_FromCFunc(cc_cmp_func func, void *ctx, PyObject *ctx_ref);
ComparatorObject* Comparator_FromPython(PyObject *callable, bool is_key_func);

// Perform comparison
int Comparator_Compare(ComparatorObject *cmp, PyObject *a, PyObject *b);

// Check for pending exception after comparison
bool Comparator_HasError(void);
```

### Container Integration

```python
# Constructor accepts cmp= or key= parameter
m = SkipListMap()                           # Natural ordering
m = SkipListMap(cmp=Comparator.reverse())   # C comparator
m = SkipListMap(cmp=lambda a, b: ...)       # Python callable
m = SkipListMap(key=str.lower)              # Key function

# Report active comparator type
m.comparator_type  # 'natural', 'c_func', 'key_func', or 'python'
```

## Design Decisions

| Decision | Choice | Rationale | Alternatives Considered |
|----------|--------|-----------|------------------------|
| Three-way compare | Return -1/0/+1 | Compatible with C, efficient | Boolean less-than only (requires two calls) |
| Key extraction | At insertion time | Amortize cost, consistent ordering | At comparison time (repeated cost) |
| Context support | Void pointer + PyObject ref | Flexible, supports GC prevention | Closure capture (Python only) |
| Built-in comparators | Static methods | Clear factory pattern | Singleton instances (less flexible) |
| Error handling | Check PyErr_Occurred | Standard Python C API pattern | Return value sentinel (ambiguous) |

## Performance Characteristics

| Comparator Type | Cost per Comparison | Notes |
|-----------------|---------------------|-------|
| Natural | ~50ns | Two `PyObject_RichCompareBool` calls |
| C function | ~10ns | Direct C call, no Python overhead |
| Numeric (optimized) | ~15ns | Type check + direct comparison |
| String (optimized) | ~20ns | PyUnicode_Compare |
| Key function | ~50ns | Natural on extracted key |
| Python callable | ~500ns | Full Python call protocol |

## Integration Points

### With Ordered Containers

```c
// In SkipListMap
typedef struct {
    PyObject_HEAD
    ComparatorObject *comparator;  // Owned reference
    // ...
} SkipListMapObject;

// At construction
self->comparator = resolve_comparator(cmp_arg, key_arg);

// At comparison
int result = Comparator_Compare(self->comparator, a, b);
if (Comparator_HasError()) {
    return NULL;  // Propagate exception
}
```

### With Cython (C implementation path)

```cython
# User defines comparator function
cdef int my_cmp(PyObject* a, PyObject* b, void* ctx) noexcept nogil:
    # Custom comparison logic
    ...

# Register with library
def get_my_comparator():
    from concurrent_collections import Comparator
    return Comparator.from_cfunc(<Py_uintptr_t>my_cmp)
```

### With Rust (Rust implementation path)

If implementing in Rust with PyO3, custom comparators can be provided via Rust closures or trait implementations:

```rust
use pyo3::prelude::*;
use std::cmp::Ordering;

/// Trait for custom comparators
pub trait PyComparator: Send + Sync {
    /// Compare two Python objects
    /// Returns Ordering::Less, Equal, or Greater
    fn compare(&self, py: Python<'_>, a: &PyAny, b: &PyAny) -> PyResult<Ordering>;
}

/// Comparator type enumeration
pub enum ComparatorKind {
    Natural,
    Reverse,
    Numeric,
    String,
    RustFn(Box<dyn PyComparator>),
    PythonCallable(PyObject),
    KeyFunction(PyObject),
}

/// Main comparator struct
#[pyclass]
pub struct Comparator {
    kind: ComparatorKind,
}

#[pymethods]
impl Comparator {
    /// Create natural ordering comparator
    #[staticmethod]
    fn natural() -> Self {
        Comparator { kind: ComparatorKind::Natural }
    }

    /// Create reverse ordering comparator
    #[staticmethod]
    fn reverse() -> Self {
        Comparator { kind: ComparatorKind::Reverse }
    }

    /// Create from Rust closure (for Rust users extending the library)
    #[staticmethod]
    fn from_rust_fn(cmp_fn: Box<dyn PyComparator>) -> Self {
        Comparator { kind: ComparatorKind::RustFn(cmp_fn) }
    }

    /// Get comparator type as string
    #[getter]
    fn r#type(&self) -> &'static str {
        match &self.kind {
            ComparatorKind::Natural => "natural",
            ComparatorKind::Reverse | ComparatorKind::Numeric |
            ComparatorKind::String | ComparatorKind::RustFn(_) => "rust_fn",
            ComparatorKind::PythonCallable(_) => "python",
            ComparatorKind::KeyFunction(_) => "key_func",
        }
    }
}

impl Comparator {
    /// Internal comparison method
    pub fn compare(&self, py: Python<'_>, a: &PyAny, b: &PyAny) -> PyResult<Ordering> {
        match &self.kind {
            ComparatorKind::Natural => {
                if a.lt(b)? { Ok(Ordering::Less) }
                else if a.gt(b)? { Ok(Ordering::Greater) }
                else { Ok(Ordering::Equal) }
            }
            ComparatorKind::Reverse => {
                self.compare_natural(py, b, a)  // Swap arguments
            }
            ComparatorKind::RustFn(f) => f.compare(py, a, b),
            // ... other cases
        }
    }
}
```

#### Example: Custom Rust Comparator

```rust
use concurrent_collections::{Comparator, PyComparator};
use pyo3::prelude::*;
use std::cmp::Ordering;

/// Case-insensitive string comparator
struct CaseInsensitiveComparator;

impl PyComparator for CaseInsensitiveComparator {
    fn compare(&self, py: Python<'_>, a: &PyAny, b: &PyAny) -> PyResult<Ordering> {
        let a_str: String = a.extract()?;
        let b_str: String = b.extract()?;
        Ok(a_str.to_lowercase().cmp(&b_str.to_lowercase()))
    }
}

/// Numeric reverse comparator with fast path
struct NumericReverseComparator;

impl PyComparator for NumericReverseComparator {
    fn compare(&self, py: Python<'_>, a: &PyAny, b: &PyAny) -> PyResult<Ordering> {
        // Try fast path for i64
        if let (Ok(a_int), Ok(b_int)) = (a.extract::<i64>(), b.extract::<i64>()) {
            return Ok(b_int.cmp(&a_int));  // Reversed
        }
        // Fallback to float
        if let (Ok(a_f), Ok(b_f)) = (a.extract::<f64>(), b.extract::<f64>()) {
            return Ok(b_f.partial_cmp(&a_f).unwrap_or(Ordering::Equal));
        }
        // Fallback to Python comparison (reversed)
        if b.lt(a)? { Ok(Ordering::Less) }
        else if b.gt(a)? { Ok(Ordering::Greater) }
        else { Ok(Ordering::Equal) }
    }
}

// Register with Python module
#[pymodule]
fn my_comparators(_py: Python<'_>, m: &PyModule) -> PyResult<()> {
    #[pyfn(m)]
    fn case_insensitive() -> Comparator {
        Comparator::from_rust_fn(Box::new(CaseInsensitiveComparator))
    }

    #[pyfn(m)]
    fn numeric_reverse() -> Comparator {
        Comparator::from_rust_fn(Box::new(NumericReverseComparator))
    }

    Ok(())
}
```

#### Usage from Python

```python
from concurrent_collections import SkipListMap
from my_comparators import case_insensitive, numeric_reverse

# Case-insensitive string ordering
m = SkipListMap(cmp=case_insensitive())
m["Apple"] = 1
m["banana"] = 2
m["CHERRY"] = 3
list(m.keys())  # ['Apple', 'banana', 'CHERRY'] - case-insensitive order

# Numeric reverse ordering
m2 = SkipListMap(cmp=numeric_reverse())
m2[1] = "a"
m2[10] = "b"
m2[5] = "c"
list(m2.keys())  # [10, 5, 1]
```

## Open Questions

| Question | Options | Impact |
|----------|---------|--------|
| Thread safety | Comparator immutable vs allow mutation | Concurrent container usage |
| Comparison caching | Cache recent results vs always compute | Memory vs CPU tradeoff |
| Error propagation | Exception vs error code | API consistency |
