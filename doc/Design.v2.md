# concurrent_collections

## High-Level Design Document

**Version**: 1.0 Draft  
**Target**: Python 3.13+ (free-threaded)  
**License**: BSD-3-Clause (CPython compatible)

---

## 1. Vision & Goals

### 1.1 Problem Statement

Free-threaded Python (PEP 703) removes the GIL but exposes a critical gap: Python lacks high-performance concurrent data structures. Developers must choose between:

- **Lock-wrapped stdlib containers**: Simple but contention kills scaling
- **multiprocessing-based sharing**: High overhead, serialization costs
- **Pure Python attempts**: Can't achieve native performance

Meanwhile, Java has `java.util.concurrent`, C++ has Intel TBB and folly, and Rust has crossbeam. Python has nothing comparable.

### 1.2 Solution

`concurrent_collections` provides production-ready, lock-free data structures:

| Category | Structures | Fills Gap |
|----------|------------|-----------|
| **Ordered Maps/Sets** | SkipListMap, SkipListSet, TreeMap, TreeSet | No concurrent ordered containers exist in Python |
| **Queues** | LockFreeQueue, FastQueue, WaitFreeQueue | `queue.Queue` uses locks, poor scaling |
| **Stacks** | LockFreeStack | No concurrent stack in stdlib |

### 1.3 Design Principles

1. **Correctness first**: Linearizable, formally verified algorithms from peer-reviewed literature
2. **Pythonic API**: Familiar interfaces (dict-like, set-like) with Pythonic iteration
3. **Zero-copy where possible**: Minimize PyObject overhead in hot paths
4. **Graceful degradation**: Works on GIL-enabled Python (with reduced benefit)
5. **No dependencies**: Self-contained, vendored SMR implementation
6. **Production-ready**: Comprehensive testing, benchmarks, documentation

---

## 2. Package Contents

### 2.1 Module Structure

```
concurrent_collections
├── SkipListMap          # Ordered key-value, O(log n)
├── SkipListSet          # Ordered set, O(log n)
├── TreeMap              # BST-based ordered key-value
├── TreeSet              # BST-based ordered set
├── LockFreeQueue        # MPMC queue, portable
├── FastQueue            # MPMC queue, architecture-optimized
├── WaitFreeQueue        # MPMC queue, wait-free guarantee
├── LockFreeStack        # MPMC stack with elimination
└── config               # Runtime configuration
```

### 2.2 Ordered Containers

#### SkipListMap / SkipListSet

**Algorithm**: Fraser's lock-free skip list (2004), proven in Java's `ConcurrentSkipListMap`

**Why skip list first**:
- Simpler than balanced trees (no rotations)
- Probabilistic balance—no worst-case degradation in practice
- Well-understood, multiple production implementations exist
- Better concurrency than BSTs under heavy writes

**Complexity**:
| Operation | Average | Worst |
|-----------|---------|-------|
| get | O(log n) | O(n)* |
| put | O(log n) | O(n)* |
| delete | O(log n) | O(n)* |
| range | O(log n + k) | O(n + k)* |

*Worst case is probabilistically negligible (1/2^32 for 32 levels)

#### TreeMap / TreeSet

**Algorithm**: Natarajan-Mittal external BST (PPoPP 2014)

**Why offer both skip list and BST**:
- BST has better cache locality for read-heavy workloads
- Skip list has better write concurrency
- Different workloads favor each—let users benchmark
- External BST has cleaner deletion semantics

**Key differentiator from skip list**: Deterministic O(log n) with proper balancing (though unbalanced in base form; balanced variant possible via Brown's (a,b)-tree)

### 2.3 Queue Family

#### LockFreeQueue (Default)

**Algorithm**: SCQ—Scalable Circular Queue (Nikolaev & Ravindran, 2019)

**Why SCQ**:
- Portable: only requires single-width CAS
- Works on ARM, RISC-V, PowerPC—not just x86
- Livelock-free (unlike CRQ)
- Bounded memory footprint

#### FastQueue (Architecture-Optimized)

**Algorithm**: LCRQ on x86-64, SCQ fallback elsewhere

**Why offer both**:
- LCRQ achieves highest known throughput on x86-64
- Requires double-width CAS (CMPXCHG16B)—not portable
- Runtime architecture detection selects optimal implementation

#### WaitFreeQueue

**Algorithm**: wCQ—Wait-Free Circular Queue (SPAA 2022)

**Why offer wait-free variant**:
- Hard real-time systems need bounded worst-case latency
- Lock-free only guarantees system-wide progress
- Wait-free guarantees per-thread progress

**Tradeoff**: ~15-20% throughput overhead vs lock-free in typical workloads

### 2.4 Stack

#### LockFreeStack

**Algorithm**: Treiber stack with elimination backoff

**Elimination optimization**: Under high contention, concurrent push/pop pairs "eliminate" each other without touching the shared stack—dramatic throughput improvement.

---

## 3. API Design

### 3.1 Ordered Map API

```python
from concurrent_collections import SkipListMap

m = SkipListMap()  # Keys must be comparable

# Basic operations (dict-like)
m[key] = value              # put(key, value)
value = m[key]              # get(key), raises KeyError if missing
value = m.get(key, default) # get with default
del m[key]                  # delete(key)
key in m                    # contains(key)
len(m)                      # size (approximate under concurrency)

# Atomic operations
old = m.put_if_absent(key, value)      # Returns existing or None
old = m.replace(key, new_value)        # Returns old or None
ok = m.replace_if(key, expected, new)  # CAS semantics
old = m.pop(key, default)              # Atomic remove and return

# Ordered operations (the differentiator)
m.first_key()               # Minimum key, raises KeyError if empty
m.last_key()                # Maximum key
m.floor_key(key)            # Greatest key ≤ key, or None
m.ceiling_key(key)          # Least key ≥ key, or None
m.lower_key(key)            # Greatest key < key
m.higher_key(key)           # Least key > key

# Range operations
m.keys(start, stop)         # Iterator over keys in [start, stop)
m.items(start, stop)        # Iterator over (key, value) pairs
m.values(start, stop)       # Iterator over values

# Iteration (snapshot semantics—sees consistent point-in-time view)
for key in m:               # Iterate keys in order
    ...
for key, value in m.items():
    ...

# Bulk operations
m.clear()                   # Remove all entries
m.update(other_map)         # Merge from dict or mapping
```

### 3.2 Ordered Set API

```python
from concurrent_collections import SkipListSet

s = SkipListSet()

# Basic operations (set-like)
s.add(item)
s.discard(item)             # Remove if present, no error if missing
s.remove(item)              # Remove, raises KeyError if missing
item in s
len(s)

# Ordered operations
s.first()                   # Minimum element
s.last()                    # Maximum element
s.floor(item)               # Greatest element ≤ item
s.ceiling(item)             # Least element ≥ item

# Range iteration
s.range(start, stop)        # Iterator over [start, stop)

# Set operations (return new SkipListSet)
s.union(other)
s.intersection(other)
s.difference(other)
```

### 3.3 Queue API

```python
from concurrent_collections import LockFreeQueue, FastQueue, WaitFreeQueue

q = LockFreeQueue(maxsize=0)  # 0 = unbounded

# Core operations
q.put(item)                 # Enqueue, blocks if bounded and full
q.put_nowait(item)          # Enqueue, raises Full if bounded and full
item = q.get()              # Dequeue, blocks if empty
item = q.get_nowait()       # Dequeue, raises Empty if empty

# Non-blocking try variants
ok = q.try_put(item)        # Returns True/False
item = q.try_get()          # Returns item or None

# Inspection (approximate under concurrency)
len(q)
q.empty()
q.full()                    # Only meaningful if bounded

# Bulk operations
items = q.drain(max_items)  # Dequeue up to max_items, returns list

# Compatibility with queue.Queue
q.qsize()                   # Alias for len(q)
q.task_done()               # No-op for compatibility
q.join()                    # No-op for compatibility
```

### 3.4 Stack API

```python
from concurrent_collections import LockFreeStack

s = LockFreeStack()

s.push(item)
item = s.pop()              # Raises Empty if empty
item = s.try_pop()          # Returns None if empty
item = s.peek()             # View top without removing

len(s)
s.empty()
```

### 3.5 Configuration

```python
from concurrent_collections import config

# === Platform & Architecture (read-only) ===
config.detected_arch            # 'x86_64', 'aarch64', etc.
config.detected_features        # {'cmpxchg16b': True, 'lse': False, ...}
config.available_queue_backends # ['scq', 'lcrq'] or ['scq']

# === Backend Selection ===
config.queue_backend = 'auto'   # 'auto', 'scq', 'lcrq'
                                # 'auto' selects best for platform
                                # 'lcrq' raises if unavailable

# === SMR Tuning ===
config.smr_scheme = 'ibr'       # 'ibr' or 'debra'
config.retire_threshold = 64    # Trigger reclamation after N retires
config.max_reclaim_per_poll = 32 # Bound reclamation work per poll

# === Debugging & Diagnostics ===
config.enable_statistics = False # Track operation counts (slight overhead)
config.enable_contention_stats = False  # Track CAS failures

# === Build Information ===
import concurrent_collections
concurrent_collections.print_config()  # Print full configuration
info = concurrent_collections.get_build_info()  # Programmatic access
```

**Configuration Precedence**: Environment variables override defaults, code overrides environment:

```bash
# Environment variable override (useful for benchmarking)
export CONCURRENT_COLLECTIONS_QUEUE_BACKEND=scq
export CONCURRENT_COLLECTIONS_SMR_SCHEME=debra
```

---

## 4. Architecture

### 4.1 Component Diagram

```
┌─────────────────────────────────────────────────────────────────┐
│                        Python Layer                              │
│  ┌─────────────┐ ┌─────────────┐ ┌─────────────┐ ┌────────────┐ │
│  │ SkipListMap │ │   TreeMap   │ │    Queue    │ │   Stack    │ │
│  │ SkipListSet │ │   TreeSet   │ │   Family    │ │            │ │
│  └──────┬──────┘ └──────┬──────┘ └──────┬──────┘ └─────┬──────┘ │
└─────────┼───────────────┼───────────────┼──────────────┼────────┘
          │               │               │              │
          ▼               ▼               ▼              ▼
┌─────────────────────────────────────────────────────────────────┐
│                      C Extension Layer                           │
│  ┌─────────────────────────────────────────────────────────────┐│
│  │                   Python C API Bindings                      ││
│  │         (Reference counting, GC integration, typing)         ││
│  └─────────────────────────────────────────────────────────────┘│
│                              │                                   │
│  ┌───────────────────────────┼───────────────────────────────┐  │
│  │                  Core Data Structures                      │  │
│  │  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────┐   │  │
│  │  │ skiplist │  │   bst    │  │ scq/lcrq │  │ treiber  │   │  │
│  │  └────┬─────┘  └────┬─────┘  └────┬─────┘  └────┬─────┘   │  │
│  └───────┼─────────────┼─────────────┼─────────────┼─────────┘  │
│          │             │             │             │             │
│          ▼             ▼             ▼             ▼             │
│  ┌─────────────────────────────────────────────────────────────┐│
│  │                Safe Memory Reclamation (SMR)                 ││
│  │              IBR (primary) / DEBRA+ (alternative)            ││
│  └─────────────────────────────────────────────────────────────┘│
│                              │                                   │
│  ┌─────────────────────────────────────────────────────────────┐│
│  │                     Utility Layer                            ││
│  │    atomics  │  backoff  │  arch detection  │  mimalloc glue ││
│  └─────────────────────────────────────────────────────────────┘│
└─────────────────────────────────────────────────────────────────┘
                               │
                               ▼
                    ┌─────────────────────┐
                    │      mimalloc       │
                    │ (CPython allocator) │
                    └─────────────────────┘
```

### 4.2 Memory Reclamation Strategy

All lock-free structures face the reclamation problem: when a thread removes a node, other threads may still hold references. Premature freeing causes use-after-free; never freeing causes unbounded memory growth.

**Primary scheme: Interval-Based Reclamation (IBR)**

| Property | IBR | CPython's GUS | Hazard Pointers |
|----------|-----|---------------|-----------------|
| Overhead per access | Low | Low | High (fence) |
| Memory bound | O(T²R) | Unbounded | O(TR) |
| Stalled thread handling | Yes | No | Yes |
| Complexity | Medium | Simple | Medium |

IBR chosen because it provides bounded memory (unlike GUS) without the per-access fence overhead of hazard pointers.

**Alternative: DEBRA+**

Available via configuration for specific workloads:
- Better throughput than IBR under low contention
- Signal-based neutralization for stalled threads
- Preferred for single-socket, low thread count scenarios

### 4.3 mimalloc Integration

```
┌──────────────────────────────────────────────────────┐
│                   Our Extension                       │
│                                                       │
│   SkipListNode allocation:  mi_malloc(sizeof(...))   │
│   Node retirement:          smr_retire(node)         │
│   Deferred free callback:   mi_free(node)            │
│                                                       │
│   No conflict with CPython's page-level QSBR—        │
│   we manage our own nodes independently              │
└──────────────────────────────────────────────────────┘
                          │
                          ▼
              ┌───────────────────────┐
              │       mimalloc        │
              │  • Thread-local heaps │
              │  • Handles cross-     │
              │    thread frees       │
              └───────────────────────┘
```

Our SMR retires nodes to a deferred list. When safe, the SMR reclamation callback invokes `mi_free()`. This is fully compatible with mimalloc's design—it handles cross-thread frees internally.

### 4.4 Thread Safety Model

**Linearizability**: All operations appear to take effect atomically at some point between invocation and response.

**Progress guarantees**:

| Structure | Guarantee |
|-----------|-----------|
| SkipListMap/Set | Lock-free |
| TreeMap/Set | Lock-free |
| LockFreeQueue | Lock-free |
| FastQueue | Lock-free |
| WaitFreeQueue | Wait-free |
| LockFreeStack | Lock-free |

**Lock-free**: At least one thread makes progress in finite steps (system-wide progress)

**Wait-free**: Every thread makes progress in bounded steps (per-thread progress)

---

## 5. Platform Support & Architecture Strategy

### 5.1 Design Philosophy

`concurrent_collections` follows a **portable-first with architecture-specific optimizations** approach. Every structure works on every supported platform. Performance-critical paths use optimized implementations where available, with automatic fallback to portable alternatives.

This matches community expectations set by NumPy, PyTorch, and other serious packages: users should never encounter "not supported on your platform" errors, but should benefit from hardware-specific optimizations transparently.

### 5.2 Platform Support Matrix

| Structure | x86-64 | ARM64 | Other* |
|-----------|--------|-------|--------|
| SkipListMap/Set | Full | Full | Full |
| TreeMap/Set | Full | Full | Full |
| LockFreeQueue (SCQ) | Full | Full | Full |
| FastQueue | LCRQ | SCQ | SCQ |
| WaitFreeQueue | Full | Full | Full |
| LockFreeStack | Full | Full | Full |

*Other includes RISC-V, PowerPC, SPARC, etc.—any platform with C11 atomics support.

**Key insight**: All core data structures are fully portable. Only `FastQueue` has architecture-specific variants, and it always falls back to the portable SCQ implementation.

### 5.3 Architecture Detection & Selection

```
┌─────────────────────────────────────────────────────────────┐
│                      FastQueue                               │
├─────────────────────────────────────────────────────────────┤
│  Compile-time:                                               │
│    #if defined(__x86_64__) && defined(__CMPXCHG16B__)       │
│        → Build includes LCRQ code path                       │
│    #endif                                                    │
│    → Always build SCQ code path                              │
│                                                              │
│  Runtime:                                                    │
│    x86-64 with CMPXCHG16B?  ──yes──►  LCRQ (best throughput)│
│           │                                                  │
│           no                                                 │
│           ▼                                                  │
│        SCQ (portable, still excellent)                       │
└─────────────────────────────────────────────────────────────┘
```

Runtime detection uses CPUID on x86-64 to verify CMPXCHG16B support (present on all Intel Core/AMD K10 and later, but worth checking for virtualized environments).

### 5.4 Wheel Distribution

We provide pre-built wheels for all major platforms:

| Platform Tag | Architecture | Notes |
|--------------|--------------|-------|
| `manylinux_2_28_x86_64` | Linux x86-64 | Primary, includes LCRQ |
| `manylinux_2_28_aarch64` | Linux ARM64 | Graviton, Ampere, etc. |
| `musllinux_1_2_x86_64` | Alpine x86-64 | Container-friendly |
| `musllinux_1_2_aarch64` | Alpine ARM64 | Container-friendly |
| `macosx_11_0_arm64` | macOS Apple Silicon | M1/M2/M3 |
| `macosx_10_15_x86_64` | macOS Intel | Legacy support |
| `win_amd64` | Windows x86-64 | Includes LCRQ |

**Build infrastructure**: cibuildwheel on GitHub Actions, testing on native ARM64 runners.

**Source fallback**: If no wheel matches, pip builds from source. Build requirements are minimal (C11 compiler, Python headers).

### 5.5 Configuration API for Architecture Control

```python
from concurrent_collections import config

# Query detected configuration (read-only)
print(config.detected_arch)        # 'x86_64', 'aarch64', 'riscv64', etc.
print(config.detected_features)    # {'cmpxchg16b': True, 'lse': False, ...}
print(config.queue_backend)        # 'lcrq' or 'scq' (auto-selected)

# Override backend selection (for testing/benchmarking)
config.queue_backend = 'scq'       # Force portable implementation
config.queue_backend = 'lcrq'      # Force LCRQ (raises if unavailable)
config.queue_backend = 'auto'      # Restore automatic selection

# Check what's available
print(config.available_queue_backends)  # ['scq', 'lcrq'] or ['scq']
```

### 5.6 Architecture-Specific Optimizations

Beyond queue selection, we apply architecture-aware optimizations throughout:

| Optimization | x86-64 | ARM64 | Portable |
|--------------|--------|-------|----------|
| Cache line padding | 64 bytes | 64/128 bytes* | 64 bytes |
| Memory barriers | `mfence`, `sfence` | `dmb`, `dsb` | C11 atomics |
| Atomic operations | Native CAS, FAA | LSE when available | C11 atomics |
| Backoff strategy | `pause` instruction | `yield` | Spin loop |

*ARM64 uses 128-byte padding when targeting Apple Silicon (128-byte cache lines).

### 5.7 Future: Wheel Variants

The Python packaging ecosystem is developing "wheel variants" (WheelNext initiative) that will allow:

```
concurrent_collections-1.0-cp313-manylinux_2_28_x86_64.whl
concurrent_collections-1.0-cp313-manylinux_2_28_x86_64+avx512.whl
```

With pip automatically selecting the best match. Our architecture-aware design positions us well for this future. When available, we may offer:

- AVX-512 optimized memory operations on supporting CPUs
- ARM SVE optimizations for server ARM
- CUDA-accelerated batch operations (longer term)

### 5.8 Transparency Principle

Users should always know what they're getting:

```python
import concurrent_collections

# Startup banner (optional, disabled by default)
concurrent_collections.print_config()
# Output:
# concurrent_collections 1.0.0
# Platform: linux-x86_64 (glibc 2.28)
# Queue backend: lcrq (CMPXCHG16B detected)
# SMR scheme: ibr
# Compiler: gcc 12.2.0

# Programmatic access
info = concurrent_collections.get_build_info()
# {'version': '1.0.0', 'platform': 'linux-x86_64', 'queue_backend': 'lcrq', ...}
```

Benchmarks should always report the active backend to ensure reproducibility across different hardware.

---

## 6. Performance Targets

### 6.1 Competitive Baselines

| Operation | Baseline | Target Speedup |
|-----------|----------|----------------|
| Ordered map (8 threads) | `sortedcontainers` + Lock | 5-10x |
| Queue throughput (8 threads) | `queue.Queue` | 3-5x |
| Stack throughput (8 threads) | `list` + Lock | 3-5x |

### 6.2 Scaling Characteristics

```
Expected throughput scaling (operations/sec, normalized to 1 thread):

Threads │ Locked Container │ concurrent_collections
────────┼──────────────────┼────────────────────────
   1    │       1.0x       │         1.0x
   2    │       0.6x       │         1.8x
   4    │       0.4x       │         3.2x
   8    │       0.3x       │         5.5x
  16    │       0.2x       │         7.0x*
  
* NUMA effects limit scaling beyond ~8 threads on dual-socket
```

### 6.3 Memory Overhead

| Structure | Per-entry overhead |
|-----------|-------------------|
| SkipListMap | ~64 bytes (node + avg 2 levels) |
| TreeMap | ~48 bytes (node + child pointers) |
| Queue slot | ~16 bytes (pointer + metadata) |

SMR adds ~16 bytes per retired-but-not-yet-reclaimed node.

---

## 7. Testing Strategy

### 7.1 Correctness Testing

| Test Type | Purpose |
|-----------|---------|
| Unit tests | Basic functionality, edge cases |
| Stress tests | Random operations from many threads |
| Linearizability tests | Verify operations are linearizable |
| Sanitizer runs | TSAN, ASAN, MSAN for memory/race bugs |

**Linearizability checking**: Use tools like Lincheck or custom history recorder to verify operation histories are linearizable.

### 7.2 Stress Test Patterns

```
Pattern 1: Uniform random
  - Random mix of operations
  - Random keys from large space
  - Tests general correctness

Pattern 2: Hot spot
  - 80% of operations on 20% of keys
  - Tests contention handling

Pattern 3: Producer-consumer
  - Dedicated producer/consumer threads
  - Tests queue/stack under asymmetric load

Pattern 4: Range scan + mutation
  - Concurrent range iterations and modifications
  - Tests snapshot isolation of iterators
```

### 7.3 Platform Testing

**Primary CI Matrix** (GitHub Actions):

| Platform | Runner | Tests | Notes |
|----------|--------|-------|-------|
| Linux x86-64 | ubuntu-latest | Full suite | Primary development target |
| Linux ARM64 | ubuntu-24.04-arm | Full suite | Native ARM runner |
| macOS x86-64 | macos-13 | Full suite | Intel Mac |
| macOS ARM64 | macos-14 | Full suite | Apple Silicon |
| Windows x86-64 | windows-latest | Full suite | MSVC build |

**Architecture-Specific Validation**:

| Test | Purpose |
|------|---------|
| LCRQ activation test | Verify LCRQ selected on x86-64 with CMPXCHG16B |
| SCQ fallback test | Verify SCQ used on ARM64 and non-DCAS x86 |
| Backend override test | Verify `config.queue_backend = 'scq'` works on x86-64 |
| Feature detection test | Verify `config.detected_features` accuracy |

**Cross-Platform Correctness**:

All platforms must pass identical correctness tests. The test suite includes:

```python
# Example: Backend-agnostic queue test
def test_queue_correctness():
    """Must pass regardless of LCRQ vs SCQ backend."""
    q = FastQueue()
    
    # Record which backend is active
    backend = config.queue_backend
    
    # Run standard correctness tests
    run_mpmc_stress_test(q, threads=8, ops=100_000)
    run_linearizability_check(q)
    
    # Log for reproducibility
    print(f"Tested with backend: {backend}")
```

**Performance Regression Detection**:

We track performance across platforms to catch architecture-specific regressions:

- Benchmark results stored per-platform, per-backend
- Alert if performance drops >10% between releases
- Separate tracking for LCRQ vs SCQ paths

---

## 8. Documentation Plan

### 8.1 User Documentation

- **Getting Started**: Installation, basic usage
- **API Reference**: Complete method documentation
- **Choosing the Right Structure**: Decision guide for different use cases
- **Performance Tuning**: Configuration options, NUMA awareness
- **Migration Guide**: From `queue.Queue`, `sortedcontainers`, etc.

### 8.2 Developer Documentation

- **Architecture Overview**: Component design, data flow
- **SMR Deep Dive**: Memory reclamation explained
- **Contributing Guide**: Code style, testing requirements
- **Benchmarking Guide**: How to run and interpret benchmarks

---

## 9. Rollout Plan

### Phase 1: Alpha (Weeks 1-6)

**Deliverables**:
- Core SMR implementation (IBR)
- SkipListMap/SkipListSet complete
- Basic test suite
- Initial benchmarks

**Exit criteria**:
- Passes stress tests (1M ops, 16 threads)
- TSAN clean
- 3x faster than locked baseline at 8 threads

### Phase 2: Beta (Weeks 7-10)

**Deliverables**:
- TreeMap/TreeSet
- Queue family (SCQ, LCRQ, wCQ)
- LockFreeStack
- Comprehensive benchmarks
- Documentation draft

**Exit criteria**:
- Linearizability tests pass
- API frozen
- Performance targets met

### Phase 3: Release Candidate (Weeks 11-12)

**Deliverables**:
- PyPI package with wheels (manylinux, macOS, Windows)
- Complete documentation
- Benchmark comparison suite

**Exit criteria**:
- External review (python-dev, concurrency experts)
- No critical bugs in 1 week of community testing

### Phase 4: Stable Release

- 1.0 release to PyPI
- Announcement on Python forums, blogs
- Begin gathering feedback for future improvements

---

## 10. Future Directions

### 10.1 Potential Additions (Post-1.0)

| Structure | Algorithm | Notes |
|-----------|-----------|-------|
| ConcurrentHashMap | Split-ordered list | Lock-free unordered map |
| PriorityQueue | Lock-free skip list heap | Different interface than ordered map |
| Deque | Lock-free doubly-linked | More complex than queue |
| NUMA-aware variants | Node Replication | For large NUMA systems |

### 10.2 Stdlib Consideration

If `concurrent_collections` gains adoption and proves stable, propose PEP for stdlib inclusion as `concurrent.collections`. The external package serves as proving ground.

### 10.3 C API Exposure

Consider exposing C API for other extension authors to build on:
- SMR primitives
- Atomic utilities
- Backoff helpers

---

## 11. References

### Algorithms

1. Fraser, K. (2004). "Practical Lock-Freedom" (PhD Thesis) — Skip list
2. Natarajan, A. & Mittal, N. (2014). "Fast Concurrent Lock-Free Binary Search Trees" — BST
3. Nikolaev, R. & Ravindran, B. (2019). "A Scalable, Portable Lock-Free FIFO Queue" — SCQ
4. Morrison, A. & Afek, Y. (2013). "Fast Concurrent Queues for x86 Processors" — LCRQ
5. Nikolaev, R. et al. (2022). "wCQ: A Fast Wait-Free Queue" — wCQ
6. Wen, H. et al. (2018). "Interval-Based Memory Reclamation" — IBR
7. Brown, T. (2015). "Reclaiming Memory for Lock-Free Data Structures" — DEBRA+

### Prior Art

- Java: `java.util.concurrent.ConcurrentSkipListMap`
- C++: folly::ConcurrentSkipList, Intel TBB
- Rust: crossbeam, flurry

---

## Appendix A: Algorithm Selection Rationale

### Why Fraser Skip List over alternatives?

| Alternative | Reason Not Chosen |
|-------------|-------------------|
| Herlihy-Shavit skip list | More complex, marginal benefit |
| Lock-based skip list | Doesn't meet lock-free goal |
| Pure Python | Can't achieve native performance |

### Why Natarajan-Mittal BST?

| Alternative | Reason Not Chosen |
|-------------|-------------------|
| Internal BST (Chatterjee) | Requires more complex SMR |
| Brown's (a,b)-tree | More complex, balanced variant possible later |
| Red-black tree | Lock-free versions very complex |

### Why SCQ as portable queue?

| Alternative | Reason Not Chosen |
|-------------|-------------------|
| Michael-Scott queue | Lower throughput |
| CRQ | Requires closing mechanism, livelock possible |
| Basket queue | More complex, marginal benefit |

---

## Appendix B: Risk Assessment

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Subtle concurrency bug | Medium | High | Extensive testing, TSAN, linearizability checking |
| Performance below targets | Low | Medium | Benchmark early and often |
| Python C API complexity | Medium | Medium | Study existing extensions, test on multiple Python versions |
| Platform compatibility issues | Medium | Low | CI on all target platforms |
| mimalloc integration issues | Low | Medium | Test with mimalloc debug mode |

---

## Appendix C: Open Questions

1. **Iterator semantics**: Should iterators be strictly snapshot (copy-on-create) or weakly consistent (may see concurrent modifications)?
   - *Recommendation*: Weakly consistent for performance, document clearly

2. **Comparator customization**: Support custom key comparators, or require naturally comparable keys?
   - *Recommendation*: Start with natural ordering, add comparator support post-1.0

3. **Bounded vs unbounded default**: Should SkipListMap have a size limit?
   - *Recommendation*: Unbounded by default, optional limit

4. **GIL-enabled Python behavior**: How much to optimize for GIL-enabled Python?
   - *Recommendation*: Ensure correctness, accept reduced performance benefit