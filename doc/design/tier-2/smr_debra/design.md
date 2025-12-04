# smr_debra — Design

## Overview

The `smr_debra` module implements DEBRA+ (Distributed Epoch-Based Reclamation Algorithm with Neutralization), an advanced safe memory reclamation scheme. DEBRA+ extends basic epoch-based reclamation with signal-based thread neutralization to handle stalled threads.

## Dependencies

| Dependency | Purpose |
|------------|---------|
| atomics | Atomic operations for epoch tracking |
| config | Runtime configuration, thread detection |
| mimalloc_glue | Actual memory allocation/deallocation |
| smr_ibr | Shared epoch concepts (may share code) |

## Why DEBRA+ Over Basic IBR?

| Feature | IBR | DEBRA+ |
|---------|-----|--------|
| Stalled thread handling | Blocks reclamation | Signal-based neutralization |
| Memory bound guarantee | Weak (depends on cooperation) | Strong (O(T × R)) |
| Complexity | Simple | Moderate |
| Portability | High | Requires signals (POSIX) |

**Use Case**: DEBRA+ is preferred when:
- Applications may have threads that stall (blocking I/O, page faults)
- Stricter memory bounds are required
- Running on POSIX systems (Linux, macOS)

## Architecture

### Core Concept: Neutralization

When a thread stalls, other threads can "neutralize" it via a signal:

```
Thread A (stalled)         Thread B (wants to reclaim)
────────────────          ─────────────────────────────
enter(epoch=2)
  read(node)
  <page fault>             detect_stall(A)
                           send_signal(A, SIGURG)
  <signal handler>
  save_context()
  exit()                   # A no longer blocks reclamation
  <resume later>
  re-enter()
  re-read(node)            # May get different value!
```

### Key Insight: Helping vs Blocking

Traditional IBR: stalled thread blocks everyone.
DEBRA+: other threads "help" by neutralizing the stalled thread.

The neutralized thread must be prepared to:
1. Exit critical section (in signal handler)
2. Re-enter and re-read data (may have changed)
3. Handle operation restart

### Data Structures

```c
// Global state (extends smr_ibr)
typedef struct {
    // Epoch tracking (same as IBR)
    atomic_uint64_t global_epoch;
    atomic_uint64_t thread_epochs[MAX_THREADS];
    atomic_bool thread_active[MAX_THREADS];

    // DEBRA+ additions
    atomic_bool thread_neutralized[MAX_THREADS];  // Was thread neutralized?
    pthread_t thread_handles[MAX_THREADS];        // For sending signals
    atomic_uint32_t neutralize_count;             // Statistics
} debra_global_t;

// Per-thread state
typedef struct {
    // Same as IBR
    uint64_t local_epoch;
    retire_list_t* retire_lists[3];
    uint32_t retire_count;
    uint32_t thread_id;

    // DEBRA+ additions
    sigjmp_buf checkpoint;           // For longjmp after signal
    bool checkpoint_valid;           // Is checkpoint set?
    bool was_neutralized;            // Check after operations
    uint32_t operation_count;        // For poll scheduling
} debra_thread_t;
```

### Signal Handler

```c
// Installed for SIGURG (out-of-band signal)
static void debra_signal_handler(int sig, siginfo_t* info, void* ctx) {
    debra_thread_t* thr = get_thread_debra();
    if (!thr || !thr->checkpoint_valid) {
        return;  // Not in critical section, ignore
    }

    // Mark as neutralized
    atomic_store(&g_debra.thread_neutralized[thr->thread_id], true);
    thr->was_neutralized = true;

    // Exit critical section
    atomic_store(&g_debra.thread_active[thr->thread_id], false);

    // Jump back to checkpoint (abort current operation)
    siglongjmp(thr->checkpoint, 1);
}
```

### Enter Critical Section (DEBRA+)

```c
bool debra_enter(debra_thread_t* thr) {
    // Set checkpoint for neutralization
    if (sigsetjmp(thr->checkpoint, 1) != 0) {
        // Returned here from signal handler
        // Operation was aborted, must restart
        return false;  // Tell caller to retry
    }
    thr->checkpoint_valid = true;

    // Standard epoch entry
    uint64_t epoch = atomic_load(&g_debra.global_epoch);
    thr->local_epoch = epoch;
    atomic_store(&g_debra.thread_epochs[thr->thread_id], epoch);
    atomic_store(&g_debra.thread_active[thr->thread_id], true);

    atomic_thread_fence(memory_order_seq_cst);

    return true;  // Proceed with operation
}
```

### Exit Critical Section (DEBRA+)

```c
void debra_exit(debra_thread_t* thr) {
    thr->checkpoint_valid = false;  // Disable neutralization

    atomic_store(&g_debra.thread_active[thr->thread_id], false);

    // Opportunistic reclamation
    if (++thr->operation_count >= POLL_INTERVAL) {
        thr->operation_count = 0;
        debra_poll(thr);
    }
}
```

### Neutralization

```c
bool debra_try_neutralize(uint32_t thread_id) {
    // Check if thread is stalled
    if (!atomic_load(&g_debra.thread_active[thread_id])) {
        return false;  // Not active, nothing to do
    }

    uint64_t thread_epoch = atomic_load(&g_debra.thread_epochs[thread_id]);
    uint64_t global = atomic_load(&g_debra.global_epoch);

    if (global - thread_epoch < STALL_THRESHOLD) {
        return false;  // Not stalled yet
    }

    // Send neutralization signal
    pthread_t handle = g_debra.thread_handles[thread_id];
    int rc = pthread_kill(handle, SIGURG);

    if (rc == 0) {
        atomic_fetch_add(&g_debra.neutralize_count, 1);
        return true;
    }
    return false;
}
```

### Poll with Neutralization

```c
void debra_poll(debra_thread_t* thr) {
    uint64_t safe_epoch = debra_compute_safe_epoch();

    // Check for stalled threads blocking reclamation
    if (thr->retire_count > LIMBO_THRESHOLD) {
        for (int t = 0; t < MAX_THREADS; t++) {
            if (debra_is_stalled(t)) {
                debra_try_neutralize(t);
            }
        }
        // Recompute after neutralization
        safe_epoch = debra_compute_safe_epoch();
    }

    // Standard reclamation (same as IBR)
    for (int i = 0; i < 3; i++) {
        retire_list_t* list = thr->retire_lists[i];
        if (list->epoch < safe_epoch && list->count > 0) {
            for (uint32_t j = 0; j < list->count; j++) {
                retire_entry_t* e = &list->entries[j];
                e->free_fn(e->ptr, e->size);
            }
            list->count = 0;
        }
    }
}
```

## Operation Patterns

### Basic Operation with Restart

```c
PyObject* skiplist_get(SkipListMapObject* self, PyObject* key) {
    debra_thread_t* thr = get_thread_debra();

restart:
    if (!debra_enter(thr)) {
        goto restart;  // Was neutralized, retry
    }

    PyObject* result = find_internal(self, key);

    // Check for neutralization before using result
    if (thr->was_neutralized) {
        thr->was_neutralized = false;
        debra_exit(thr);
        goto restart;
    }

    // Safe to use result
    Py_XINCREF(result);
    debra_exit(thr);

    return result;
}
```

### Write Operation with Restart

```c
int skiplist_put(SkipListMapObject* self, PyObject* key, PyObject* value) {
    debra_thread_t* thr = get_thread_debra();

restart:
    if (!debra_enter(thr)) {
        goto restart;
    }

    int result = insert_internal(self, key, value);

    if (thr->was_neutralized) {
        thr->was_neutralized = false;
        // Note: insert may have partially succeeded
        // Need operation-specific rollback or idempotent retry
        debra_exit(thr);
        goto restart;
    }

    debra_exit(thr);
    return result;
}
```

## Memory Bound Guarantee

DEBRA+ provides a stronger memory bound than IBR:

**Theorem**: With T threads, retire threshold R, and neutralization:
- Maximum pending nodes: O(T × R)
- Not O(T² × R) like IBR worst case

**Proof Sketch**:
1. Each thread contributes at most R nodes before triggering reclamation
2. Stalled threads are neutralized, so they exit critical section
3. No thread blocks reclamation indefinitely
4. Therefore, at most T × R nodes can accumulate before safe_epoch advances

## Platform Considerations

### Signal Selection

| Signal | Pros | Cons |
|--------|------|------|
| SIGURG | Out-of-band, rarely used | May conflict with select() |
| SIGUSR1/2 | Standard user signals | Often used by apps |
| SIGRTMIN+n | Real-time, reserved | Less portable |

**Choice**: SIGURG as default, configurable.

### Windows Compatibility

DEBRA+ uses POSIX signals unavailable on Windows. Options:

1. **Fallback to IBR**: No neutralization on Windows
2. **Thread Suspension**: Use SuspendThread/ResumeThread (risky)
3. **Cooperative Polling**: Require threads to check flag periodically

**Implementation**: Fallback to IBR on Windows.

```c
#if defined(_WIN32)
    // Windows: no signal support, fall back to basic epoch
    #define DEBRA_NEUTRALIZATION_SUPPORTED 0
#else
    #define DEBRA_NEUTRALIZATION_SUPPORTED 1
#endif
```

## API Surface

### C API

```c
// Initialization
int debra_init(void);
void debra_shutdown(void);

// Thread registration
debra_thread_t* debra_thread_register(void);
void debra_thread_unregister(debra_thread_t* thr);

// Critical section (returns false if neutralized)
bool debra_enter(debra_thread_t* thr);
void debra_exit(debra_thread_t* thr);

// Check neutralization
bool debra_was_neutralized(debra_thread_t* thr);
void debra_clear_neutralized(debra_thread_t* thr);

// Retirement (same as IBR)
void debra_retire(debra_thread_t* thr, void* ptr, size_t size,
                  void (*free_fn)(void*, size_t));

// Reclamation
void debra_poll(debra_thread_t* thr);

// Diagnostics
uint64_t debra_get_epoch(void);
uint64_t debra_pending_count(debra_thread_t* thr);
uint32_t debra_neutralize_count(void);
```

### Python Integration

```python
from concurrent_collections import config

# Select SMR scheme (default: 'ibr')
config.smr_scheme = 'debra'  # Use DEBRA+ with neutralization

# DEBRA+ specific config
config.debra_stall_threshold = 100     # Epochs before stall detection
config.debra_neutralize_signal = 23    # SIGURG by default
```

## Design Decisions

| Decision | Choice | Rationale |
|----------|--------|-----------|
| Signal for neutralization | SIGURG | Least likely to conflict |
| Checkpoint mechanism | sigsetjmp/siglongjmp | Portable, async-signal-safe |
| Fallback on Windows | Basic IBR | No portable signal mechanism |
| Stall threshold | Configurable (default 100) | Balance responsiveness vs overhead |
| Neutralization trigger | On poll when limbo full | Demand-driven, not proactive |

## Configuration

| Parameter | Default | Description |
|-----------|---------|-------------|
| `retire_threshold` | 64 | Nodes before triggering reclamation |
| `stall_threshold` | 100 | Epochs before thread considered stalled |
| `poll_interval` | 32 | Operations between poll attempts |
| `limbo_threshold` | 256 | Pending nodes before neutralization attempt |
| `signal_number` | SIGURG | Signal for neutralization |

## Performance Characteristics

### Overhead

| Operation | Cost | Notes |
|-----------|------|-------|
| `debra_enter` | ~15-25ns | sigsetjmp overhead |
| `debra_exit` | ~5ns | Same as IBR |
| `debra_retire` | ~20ns | Same as IBR |
| `debra_poll` | ~50ns-5μs | Depends on nodes to free |
| Signal send | ~1-5μs | Infrequent |
| Signal receive | ~10-50μs | Includes longjmp |

### When Neutralization Occurs

Neutralization is rare in well-behaved applications:
- Only when threads actually stall (blocking I/O, page faults)
- Threshold prevents false positives
- One-time cost per stall event

## Comparison with Other Schemes

| Scheme | Stall Handling | Memory Bound | Complexity |
|--------|----------------|--------------|------------|
| IBR | None (blocks) | O(T²R) | Simple |
| DEBRA+ | Signal neutralization | O(TR) | Moderate |
| Hazard Pointers | N/A (per-object) | O(T×HP) | Simple |
| EBR | None (blocks) | O(T²R) | Simple |

## Instrumentation & Profiling

### DEBRAProfiler

The `DEBRAProfiler` extends `SMRProfiler` with DEBRA+-specific metrics for neutralization analysis, signal handling, and operation restart tracking.

#### DEBRA+ Specific Features

| Feature | Purpose | Overhead |
|---------|---------|----------|
| **Neutralization Events** | Track every neutralization signal | Low |
| **Signal Latency** | Time from send to handler execution | Medium |
| **Operation Restart Rate** | How often operations need retry | Low |
| **Neutralization Triggers** | What caused each neutralization | Low |
| **Thread Vulnerability** | Which threads get neutralized most | Low |
| **Recovery Time** | Time from neutralize to successful retry | Medium |
| **Memory Bound Comparison** | Compare O(TR) vs O(T²R) empirical | Low |
| **Signal Delivery Failures** | Track failed neutralization attempts | Low |

#### Data Structures

```python
@dataclass
class NeutralizationEvent:
    """Record of a neutralization event."""
    timestamp: float
    target_thread_id: int
    sender_thread_id: int
    target_epoch: int
    global_epoch: int
    epoch_lag: int
    trigger: str                    # "limbo_full", "explicit", "timeout"
    signal_latency_ns: int | None   # Time to handler execution
    recovery_time_ns: int | None    # Time until successful retry
    success: bool                   # Signal delivered successfully

@dataclass
class OperationRestartRecord:
    """Record of an operation restart due to neutralization."""
    timestamp: float
    thread_id: int
    operation_type: str             # "get", "put", "delete", etc.
    restart_count: int              # How many retries needed
    total_time_ns: int              # Total time including restarts
    neutralization_ids: list[int]   # Which neutralizations caused restarts

@dataclass
class ThreadVulnerabilityStats:
    """Per-thread neutralization vulnerability analysis."""
    thread_id: int
    times_neutralized: int
    times_sent_neutralization: int
    avg_time_to_neutralization_ns: float
    avg_recovery_time_ns: float
    restart_count: int
    restart_rate: float             # Restarts per operation

@dataclass
class DEBRAProfilerReport(SMRProfilerReport):
    """Extended report with DEBRA+-specific metrics."""
    # Inherits all SMRProfilerReport fields, plus:

    # Neutralization statistics
    neutralization_count: int
    neutralization_success_rate: float
    neutralization_events: list[NeutralizationEvent]

    # Signal metrics
    signal_latency_p50: float
    signal_latency_p95: float
    signal_latency_p99: float
    signal_delivery_failures: int

    # Operation restart metrics
    restart_count: int
    restart_rate: float             # Restarts per 1000 operations
    restart_records: list[OperationRestartRecord] | None
    max_restarts_per_operation: int

    # Recovery metrics
    recovery_time_p50: float
    recovery_time_p95: float
    recovery_time_p99: float

    # Thread vulnerability
    thread_vulnerability: list[ThreadVulnerabilityStats]
    most_vulnerable_thread: int | None
    most_aggressive_sender: int | None

    # Memory bound comparison
    empirical_memory_bound: int     # Actual peak pending
    theoretical_ibr_bound: int      # O(T²R) theoretical
    theoretical_debra_bound: int    # O(TR) theoretical
    bound_improvement_ratio: float  # IBR/DEBRA

    # Platform info
    neutralization_supported: bool  # False on Windows
    signal_number: int
```

#### Profiler API

```python
class DEBRAProfiler(SMRProfiler):
    def __init__(
        self,
        *,
        # Inherited from SMRProfiler
        track_timeline: bool = False,
        track_per_thread: bool = True,
        track_latency: bool = True,

        # DEBRA+ specific
        track_neutralizations: bool = True,
        track_restarts: bool = True,
        track_signal_latency: bool = False,  # Higher overhead
        compare_memory_bounds: bool = True,
    ):
        """Initialize DEBRA+ profiler."""
        ...

    def report(self) -> DEBRAProfilerReport:
        """Get DEBRA+-specific report."""
        ...

    # DEBRA+ specific analysis
    def analyze_neutralizations(self) -> list[dict]:
        """Detailed analysis of neutralization patterns."""
        ...

    def find_vulnerable_threads(self) -> list[int]:
        """Find threads frequently getting neutralized."""
        ...

    def find_aggressive_threads(self) -> list[int]:
        """Find threads frequently sending neutralizations."""
        ...

    def memory_bound_analysis(self) -> dict:
        """Compare empirical vs theoretical memory bounds."""
        ...

    def restart_analysis(self) -> dict:
        """Analyze operation restart patterns."""
        ...
```

#### Usage Examples

```python
from concurrent_collections import DEBRAProfiler, SkipListMap, config
import threading
import time

# Enable DEBRA+
config.smr_scheme = 'debra'

# Profile with DEBRA+-specific metrics
with DEBRAProfiler(track_signal_latency=True) as prof:
    m = SkipListMap()

    def worker_with_stalls(n, stall_every=100):
        for i in range(n):
            m[f"key_{i}"] = i
            if i % stall_every == 0:
                time.sleep(0.001)  # Simulate blocking I/O

    threads = [threading.Thread(target=worker_with_stalls, args=(10000,))
               for _ in range(8)]
    for t in threads:
        t.start()
    for t in threads:
        t.join()

report = prof.report()

# Neutralization analysis
print(f"Neutralizations: {report.neutralization_count}")
print(f"Success rate: {report.neutralization_success_rate:.1%}")
print(f"Signal latency P99: {report.signal_latency_p99 / 1000:.1f} µs")

# Restart analysis
print(f"\nOperation restarts: {report.restart_count}")
print(f"Restart rate: {report.restart_rate:.2f} per 1000 ops")
print(f"Max restarts for single op: {report.max_restarts_per_operation}")

# Memory bound comparison
print(f"\nMemory Bound Analysis:")
print(f"  Empirical peak: {report.empirical_memory_bound} nodes")
print(f"  IBR theoretical: {report.theoretical_ibr_bound} nodes")
print(f"  DEBRA+ theoretical: {report.theoretical_debra_bound} nodes")
print(f"  Improvement: {report.bound_improvement_ratio:.1f}x better than IBR")

# Thread vulnerability
print(f"\nMost vulnerable thread: {report.most_vulnerable_thread}")
print(f"Most aggressive sender: {report.most_aggressive_sender}")

for tv in sorted(report.thread_vulnerability, key=lambda x: -x.times_neutralized)[:3]:
    print(f"  Thread {tv.thread_id}: {tv.times_neutralized} neutralizations, "
          f"{tv.restart_rate:.2f} restarts/op")

# Detailed neutralization analysis
analysis = prof.analyze_neutralizations()
for pattern in analysis:
    print(f"\nNeutralization pattern: {pattern['description']}")
    print(f"  Frequency: {pattern['frequency']}")
    print(f"  Typical trigger: {pattern['trigger']}")
    print(f"  Recommendation: {pattern['recommendation']}")
```

#### HTML Dashboard Extensions

The DEBRA+ HTML report adds these visualizations:

1. **Neutralization Timeline** - When and where neutralizations occur
2. **Signal Latency Distribution** - Histogram of signal delivery times
3. **Restart Heatmap** - Thread × time restart patterns
4. **Memory Bound Comparison** - IBR vs DEBRA+ empirical vs theoretical
5. **Thread Vulnerability Matrix** - Who neutralizes whom
6. **Recovery Time Distribution** - How long to recover from neutralization

#### Prometheus Metrics (DEBRA+ Extensions)

```prometheus
# Neutralization metrics
cc_debra_neutralization_total 42
cc_debra_neutralization_success_total 40
cc_debra_neutralization_failed_total 2

# Signal latency histogram (nanoseconds)
cc_debra_signal_latency_bucket{le="1000"} 10
cc_debra_signal_latency_bucket{le="10000"} 35
cc_debra_signal_latency_bucket{le="100000"} 40
cc_debra_signal_latency_bucket{le="+Inf"} 42

# Restart metrics
cc_debra_restart_total 156
cc_debra_restart_rate 0.0032

# Recovery time histogram
cc_debra_recovery_time_bucket{le="10000"} 100
cc_debra_recovery_time_bucket{le="100000"} 145
cc_debra_recovery_time_bucket{le="+Inf"} 156

# Memory bound comparison
cc_debra_empirical_peak_pending 512
cc_debra_theoretical_ibr_bound 12288
cc_debra_theoretical_debra_bound 1536
cc_debra_bound_improvement_ratio 8.0

# Platform status
cc_debra_neutralization_supported 1
```

### Comparative Analysis Tools

```python
from concurrent_collections.profiling import compare_smr_schemes

# Run same workload with IBR and DEBRA+
results = compare_smr_schemes(
    workload=my_workload_function,
    schemes=['ibr', 'debra'],
    duration=30,
    threads=8,
)

# Compare results
print("IBR vs DEBRA+ Comparison:")
print(f"  Peak memory: {results['ibr'].peak_pending_bytes / 1024:.1f} KB "
      f"vs {results['debra'].peak_pending_bytes / 1024:.1f} KB")
print(f"  Stall events: {results['ibr'].stall_count} vs {results['debra'].stall_count}")
print(f"  Throughput: {results['ibr'].ops_per_sec:.0f} vs {results['debra'].ops_per_sec:.0f}")

# Generate comparison report
results.to_html("smr_comparison.html")
```

### Jupyter Notebook Integration

See `examples/debra_analysis.ipynb` for DEBRA+-specific analysis including:
- Neutralization pattern visualization
- Signal latency profiling
- Operation restart analysis
- Memory bound verification
- Thread vulnerability heatmaps

See `examples/memory_subsystem_comparison.ipynb` for comparing:
- IBR vs DEBRA+ performance
- Memory bound empirical vs theoretical
- Stall handling effectiveness
- Platform-specific behavior

## Open Questions

| Question | Options | Impact |
|----------|---------|--------|
| Signal choice | SIGURG vs SIGUSR1 | App compatibility |
| Nested critical sections | Disallow vs track depth | API complexity |
| Windows implementation | IBR fallback vs suspension | Platform parity |

## References

- Brown, T. "Reclaiming Memory for Lock-Free Data Structures: There has to be a Better Way" (2015)
- DEBRA original paper: epoch-based with quiescent state detection
- DEBRA+: adds signal-based neutralization for non-quiescent threads
