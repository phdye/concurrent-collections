# SkipListMap — Design Document

## Overview

`SkipListMap` is the primary ordered map container, providing a dict-like Python API with concurrent access safety. It wraps `skiplist_lockfree` or `skiplist_locked` depending on GIL state.

**Implementation:** Rust (via PyO3)

## Public API (Python)

```python
class SkipListMap(MutableMapping[K, V]):
    def __init__(
        self,
        items: Iterable[Tuple[K, V]] = None,
        *,
        cmp: Callable[[K, K], int] = None,
        key: Callable[[K], Any] = None,
        backend: Literal['auto', 'lockfree', 'locked'] = 'auto'
    ): ...

    # Dict-like operations
    def __getitem__(self, key: K) -> V: ...
    def __setitem__(self, key: K, value: V) -> None: ...
    def __delitem__(self, key: K) -> None: ...
    def __contains__(self, key: K) -> bool: ...
    def __len__(self) -> int: ...
    def __iter__(self) -> Iterator[K]: ...

    def get(self, key: K, default: V = None) -> V: ...
    def pop(self, key: K, default: V = None) -> V: ...
    def setdefault(self, key: K, default: V = None) -> V: ...
    def update(self, other: Mapping[K, V]) -> None: ...

    # Atomic operations
    def put_if_absent(self, key: K, value: V) -> Optional[V]: ...
    def replace(self, key: K, value: V) -> Optional[V]: ...
    def replace_if(self, key: K, old_value: V, new_value: V) -> bool: ...
    def compute_if_absent(self, key: K, func: Callable[[K], V]) -> V: ...

    # Ordered operations
    def first_key(self) -> K: ...
    def last_key(self) -> K: ...
    def floor_key(self, key: K) -> Optional[K]: ...
    def ceiling_key(self, key: K) -> Optional[K]: ...
    def lower_key(self, key: K) -> Optional[K]: ...
    def higher_key(self, key: K) -> Optional[K]: ...

    # Range operations
    def keys(self, start: K = None, stop: K = None) -> Iterator[K]: ...
    def values(self, start: K = None, stop: K = None) -> Iterator[V]: ...
    def items(self, start: K = None, stop: K = None) -> Iterator[Tuple[K, V]]: ...
    def submap(self, start: K, stop: K, inclusive: bool = False) -> 'SkipListMap[K, V]': ...

    # Snapshot
    def snapshot(self) -> 'FrozenSkipListMap[K, V]': ...

    # Introspection
    @property
    def comparator_type(self) -> str: ...

    @property
    def backend_type(self) -> str: ...
```

## Rust Implementation

```rust
use pyo3::prelude::*;
use pyo3::types::{PyDict, PyTuple};
use std::sync::Arc;

/// Internal skip list storage (generic over backend)
enum SkipListBackend<K, V> {
    LockFree(Arc<LockFreeSkipList<K, V>>),
    Locked(Arc<LockedSkipList<K, V>>),
}

#[pyclass(name = "SkipListMap")]
pub struct PySkipListMap {
    inner: SkipListBackend<PyObject, PyObject>,
    comparator: Option<PyObject>,
}

#[pymethods]
impl PySkipListMap {
    #[new]
    #[pyo3(signature = (items=None, *, cmp=None, key=None, backend="auto"))]
    fn new(
        py: Python<'_>,
        items: Option<&PyAny>,
        cmp: Option<PyObject>,
        key: Option<PyObject>,
        backend: &str,
    ) -> PyResult<Self> {
        let backend = match backend {
            "lockfree" => Self::create_lockfree(cmp.clone()),
            "locked" => Self::create_locked(cmp.clone()),
            "auto" | _ => {
                if Self::is_gil_disabled(py)? {
                    Self::create_lockfree(cmp.clone())
                } else {
                    Self::create_locked(cmp.clone())
                }
            }
        };

        let mut map = Self { inner: backend, comparator: cmp };

        if let Some(items) = items {
            map.update(py, items)?;
        }

        Ok(map)
    }

    fn __getitem__(&self, py: Python<'_>, key: PyObject) -> PyResult<PyObject> {
        // Release GIL during Rust operation
        py.allow_threads(|| {
            self.inner.get(&key)
        }).ok_or_else(|| PyKeyError::new_err(key))
    }

    fn __setitem__(&self, py: Python<'_>, key: PyObject, value: PyObject) -> PyResult<()> {
        py.allow_threads(|| {
            self.inner.insert(key, value);
        });
        Ok(())
    }

    fn put_if_absent(
        &self,
        py: Python<'_>,
        key: PyObject,
        value: PyObject,
    ) -> PyResult<Option<PyObject>> {
        py.allow_threads(|| {
            self.inner.put_if_absent(key, value)
        })
    }

    // ... additional methods
}
```

## Usage Examples

```python
from concurrent_collections import SkipListMap

# Basic usage
m = SkipListMap()
m['alice'] = 100
m['bob'] = 200
print(m['alice'])  # 100

# Range query
for name in m.keys('a', 'c'):
    print(name)  # alice, bob

# Atomic operations
old = m.put_if_absent('carol', 300)  # Returns None (inserted)
old = m.put_if_absent('carol', 400)  # Returns 300 (not inserted)

# Custom ordering
m = SkipListMap(cmp=lambda a, b: b - a)  # Reverse order
m = SkipListMap(key=lambda x: x.lower())  # Case-insensitive

# Concurrent access
def worker(m, base):
    for i in range(1000):
        m[base + i] = i

threads = [Thread(target=worker, args=(m, i*1000)) for i in range(4)]
[t.start() for t in threads]
[t.join() for t in threads]
```

## Backend Selection

```python
# Automatic (recommended)
m = SkipListMap()  # Chooses based on GIL state

# Force lock-free (requires no-GIL Python)
m = SkipListMap(backend='lockfree')

# Force locked (always works)
m = SkipListMap(backend='locked')
```

## SkipListMapProfiler API

```python
class SkipListMapProfiler:
    """High-level profiler for SkipListMap."""

    def __init__(self, map_instance: SkipListMap):
        self._map = map_instance
        self._profiler = SkipListProfiler()
        self._map._attach_profiler(self._profiler)

    def get_operation_stats(self) -> Dict[str, Any]:
        """Get operation counts and latencies."""
        stats = self._profiler.get_stats()
        return {
            'gets': stats.total_searches,
            'puts': stats.total_inserts,
            'deletes': stats.total_deletes,
            'get_latency_p99_us': stats.search_latency_p99,
            'put_latency_p99_us': stats.insert_latency_p99,
        }

    def get_contention_report(self) -> Dict[str, Any]:
        """Analyze contention and provide recommendations."""
        return self._profiler.detect_contention()

    def export_metrics(self, format: str = 'prometheus') -> str:
        """Export metrics in specified format."""
        return self._profiler.export_prometheus()
```

## Thread Safety

| Operation | Safety | Notes |
|-----------|--------|-------|
| Read operations | Wait-free | Multiple readers OK |
| Write operations | Lock-free/Blocking | Depends on backend |
| Iteration | Weakly consistent | May see concurrent changes |

## PyO3 Integration Details

| Aspect | Implementation |
|--------|----------------|
| GIL handling | `py.allow_threads()` for Rust operations |
| Object storage | `PyObject` with proper reference counting |
| Error handling | `PyResult<T>` maps to Python exceptions |
| Type stubs | Generated `.pyi` files for IDE support |

## Memory Management

- Python object references managed via PyO3's `PyObject`
- Rust's ownership system prevents use-after-free
- Epoch-based SMR ensures safe memory reclamation (lock-free backend)
- `RwLock` with immediate deallocation (locked backend)

## Performance Targets

| Operation | P99 Latency | Throughput (8 threads, free-threaded) |
|-----------|-------------|------------------------|
| get | <2 μs | >5M ops/s |
| put | <5 μs | >2M ops/s |
| delete | <5 μs | >2M ops/s |
| range(100) | <20 μs | >500K ops/s |

*Note: Rust implementation provides significantly better performance than pure Python or C extension approaches.*
