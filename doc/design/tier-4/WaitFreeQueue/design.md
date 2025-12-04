# WaitFreeQueue — Design Document

## Overview

`WaitFreeQueue` provides the strongest progress guarantee: every operation completes in bounded steps. Use when worst-case latency matters more than average throughput.

## Public API

```python
class WaitFreeQueue(Generic[T]):
    def __init__(self, maxsize: int = 0, max_threads: int = 64): ...

    # Same interface as LockFreeQueue
    def put(self, item: T, block: bool = True, timeout: float = None) -> None: ...
    def get(self, block: bool = True, timeout: float = None) -> T: ...
    def try_put(self, item: T) -> bool: ...
    def try_get(self) -> Optional[T]: ...

    # Wait-free verification
    def get_max_steps(self) -> int:
        """Returns maximum steps observed per operation."""
        ...
```

## Usage

```python
from concurrent_collections import WaitFreeQueue

# Specify max threads for optimal performance
q = WaitFreeQueue(maxsize=1000, max_threads=8)

# Use identically to other queues
q.put(item)
item = q.get()

# Verify wait-freedom
print(f"Max steps: {q.get_max_steps()}")  # Should be O(max_threads)
```

## When to Use

- Real-time systems with hard latency requirements
- Safety-critical applications
- When fairness is important (no thread starvation)

## Trade-offs

| Aspect | WaitFreeQueue | LockFreeQueue |
|--------|---------------|---------------|
| Progress | Wait-free | Lock-free |
| Throughput | ~50% of LockFreeQueue | Baseline |
| Worst-case latency | Bounded O(n) | Unbounded |
| Memory | Higher (announcement array) | Lower |
