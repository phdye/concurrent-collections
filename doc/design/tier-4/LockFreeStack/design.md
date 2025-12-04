# LockFreeStack — Design Document

## Overview

`LockFreeStack` is a lock-free LIFO stack using the Treiber algorithm with elimination backoff for high-contention scenarios.

## Public API

```python
class LockFreeStack(Generic[T]):
    def __init__(self, *, enable_elimination: bool = True): ...

    # Core operations
    def push(self, item: T) -> None: ...
    def pop(self) -> T: ...  # Raises Empty if empty
    def try_pop(self) -> Optional[T]: ...
    def peek(self) -> Optional[T]: ...

    # State
    def __len__(self) -> int: ...
    def empty(self) -> bool: ...

    # Configuration
    @property
    def elimination_enabled(self) -> bool: ...
```

## Usage

```python
from concurrent_collections import LockFreeStack

stack = LockFreeStack()

# Push/pop
stack.push(1)
stack.push(2)
stack.push(3)

print(stack.pop())  # 3
print(stack.pop())  # 2
print(stack.peek())  # 1 (doesn't remove)

# Try_pop for non-blocking
item = stack.try_pop()  # Returns None if empty
```

## Elimination Backoff

Under high contention, push and pop operations can exchange directly through an elimination array, bypassing the main stack:

```python
# High contention scenario
stack = LockFreeStack(enable_elimination=True)

def producer():
    for i in range(10000):
        stack.push(i)

def consumer():
    for _ in range(10000):
        stack.try_pop()

# With elimination, matching push/pop pairs rendezvous
# without touching the main stack, reducing contention
```

## StackProfiler Integration

```python
from concurrent_collections.profilers import StackProfiler

stack = LockFreeStack()
profiler = StackProfiler()
profiler.attach(stack)

# ... use stack ...

stats = profiler.get_stats()
print(f"Eliminations: {stats.elimination_successes}")
print(f"Elimination rate: {stats.elimination_rate:.1%}")

analysis = profiler.analyze_elimination_effectiveness()
print(analysis['reason'])
```

## Thread Safety

- All operations are lock-free
- LIFO ordering guaranteed
- Safe for multiple pushers and poppers
