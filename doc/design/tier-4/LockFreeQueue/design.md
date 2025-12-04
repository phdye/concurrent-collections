# LockFreeQueue — Design Document

## Overview

`LockFreeQueue` is a bounded MPMC (Multi-Producer Multi-Consumer) queue using the SCQ algorithm. Provides a `queue.Queue`-compatible API with lock-free guarantees.

## Public API

```python
class LockFreeQueue(Generic[T]):
    def __init__(self, maxsize: int = 0): ...

    # queue.Queue compatible
    def put(self, item: T, block: bool = True, timeout: float = None) -> None: ...
    def get(self, block: bool = True, timeout: float = None) -> T: ...
    def put_nowait(self, item: T) -> None: ...
    def get_nowait(self) -> T: ...

    # Non-blocking variants
    def try_put(self, item: T) -> bool: ...
    def try_get(self) -> Optional[T]: ...

    # Bulk operations
    def drain(self, max_items: int = -1) -> List[T]: ...

    # State
    def qsize(self) -> int: ...
    def empty(self) -> bool: ...
    def full(self) -> bool: ...

    @property
    def maxsize(self) -> int: ...
```

## Usage

```python
from concurrent_collections import LockFreeQueue

q = LockFreeQueue(maxsize=1000)

# Producer
q.put(item)           # Blocks if full
q.put_nowait(item)    # Raises Full
q.try_put(item)       # Returns False

# Consumer
item = q.get()           # Blocks if empty
item = q.get_nowait()    # Raises Empty
item = q.try_get()       # Returns None

# Bulk drain
items = q.drain(100)  # Get up to 100 items
```

## QueueProfiler Integration

```python
from concurrent_collections.profilers import QueueProfiler

q = LockFreeQueue(1000)
profiler = QueueProfiler()
profiler.attach(q)

# ... use queue ...

stats = profiler.get_stats()
print(f"Throughput: {stats.enqueue_throughput:.0f} ops/s")
print(f"P99 latency: {stats.enqueue_latency_p99:.1f} μs")
```

## Thread Safety

- All operations are lock-free
- FIFO ordering guaranteed
- Safe for multiple producers and consumers
