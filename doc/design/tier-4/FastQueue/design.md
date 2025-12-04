# FastQueue — Design Document

## Overview

`FastQueue` automatically selects the fastest queue implementation for the current platform:
- **x86-64**: Uses LCRQ (double-width CAS)
- **Other**: Falls back to SCQ

## Public API

Same as `LockFreeQueue`.

```python
class FastQueue(Generic[T]):
    def __init__(self, maxsize: int = 0): ...

    # Same methods as LockFreeQueue
    def put(self, item: T, block: bool = True, timeout: float = None) -> None: ...
    def get(self, block: bool = True, timeout: float = None) -> T: ...
    # ...

    @property
    def backend(self) -> str:
        """Returns 'lcrq' or 'scq'."""
        ...
```

## Usage

```python
from concurrent_collections import FastQueue

q = FastQueue(maxsize=10000)
print(q.backend)  # 'lcrq' on x86-64, 'scq' otherwise

# Use like any queue
q.put(item)
item = q.get()
```

## When to Use

- **Always use FastQueue** unless you need specific guarantees
- Provides best throughput automatically
- Falls back gracefully on unsupported platforms
