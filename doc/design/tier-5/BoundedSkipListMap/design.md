# BoundedSkipListMap — Design Document

## Overview

`BoundedSkipListMap` is a size-limited wrapper around `SkipListMap` with configurable eviction policies. Useful for caches and bounded buffers where memory usage must be controlled.

## Public API

```python
class BoundedSkipListMap(SkipListMap[K, V]):
    def __init__(
        self,
        maxsize: int,
        *,
        eviction: Literal['error', 'oldest', 'newest'] = 'error',
        cmp: Callable[[K, K], int] = None,
        key: Callable[[K], Any] = None,
    ): ...

    # Inherited from SkipListMap
    def __getitem__(self, key: K) -> V: ...
    def __setitem__(self, key: K, value: V) -> None: ...  # May evict
    def __delitem__(self, key: K) -> None: ...

    # Bounded-specific
    def is_full(self) -> bool: ...
    def remaining_capacity(self) -> int: ...

    @property
    def maxsize(self) -> int: ...

    @property
    def eviction_policy(self) -> str: ...
```

## Eviction Policies

### `eviction='error'` (Default)

Raises `BoundedMapFullError` when inserting into a full map:

```python
from concurrent_collections import BoundedSkipListMap
from concurrent_collections.exceptions import BoundedMapFullError

m = BoundedSkipListMap(maxsize=3, eviction='error')
m['a'] = 1
m['b'] = 2
m['c'] = 3
m['d'] = 4  # Raises BoundedMapFullError
```

### `eviction='oldest'`

Evicts the smallest key (first_key) to make room:

```python
m = BoundedSkipListMap(maxsize=3, eviction='oldest')
m['b'] = 2
m['c'] = 3
m['d'] = 4
m['e'] = 5  # Evicts 'b' (smallest key)

print(list(m.keys()))  # ['c', 'd', 'e']
```

### `eviction='newest'`

Evicts the largest key (last_key) to make room:

```python
m = BoundedSkipListMap(maxsize=3, eviction='newest')
m['a'] = 1
m['b'] = 2
m['c'] = 3
m['d'] = 4  # Evicts 'c' (largest key before 'd')

print(list(m.keys()))  # ['a', 'b', 'd']
```

## Usage Examples

### Cache with Bounded Size

```python
from concurrent_collections import BoundedSkipListMap

# LRU-like cache (evicts oldest)
cache = BoundedSkipListMap(maxsize=1000, eviction='oldest')

def get_or_compute(key):
    if key in cache:
        return cache[key]
    value = expensive_computation(key)
    cache[key] = value  # May evict oldest entry
    return value
```

### Sliding Window

```python
# Keep newest entries only
window = BoundedSkipListMap(maxsize=100, eviction='oldest')

for timestamp, value in stream:
    window[timestamp] = value  # Old timestamps evicted

# Window always contains most recent 100 entries
```

### Strict Capacity

```python
# Fail if full (explicit backpressure)
buffer = BoundedSkipListMap(maxsize=1000, eviction='error')

def process(key, value):
    if buffer.is_full():
        apply_backpressure()
    try:
        buffer[key] = value
    except BoundedMapFullError:
        handle_overflow(key, value)
```

## BoundedMapProfiler API

```python
class BoundedMapProfiler:
    """Profiler for BoundedSkipListMap."""

    def __init__(self, map_instance: BoundedSkipListMap):
        self._map = map_instance
        self._eviction_count = 0
        self._overflow_count = 0
        self._hit_rate_window = []

    def get_stats(self) -> Dict[str, Any]:
        return {
            'current_size': len(self._map),
            'maxsize': self._map.maxsize,
            'utilization': len(self._map) / self._map.maxsize,
            'evictions': self._eviction_count,
            'overflows': self._overflow_count,
        }

    def analyze_capacity(self) -> Dict[str, Any]:
        stats = self.get_stats()
        issues = []
        recommendations = []

        if stats['utilization'] > 0.95:
            issues.append("Near capacity")
            if self._eviction_count > 0:
                recommendations.append("Increase maxsize or improve eviction")
            else:
                recommendations.append("Consider eviction='oldest' policy")

        if self._overflow_count > 0:
            issues.append(f"{self._overflow_count} overflow events")
            recommendations.append("Increase capacity or add backpressure")

        return {
            'has_issues': len(issues) > 0,
            'issues': issues,
            'recommendations': recommendations,
        }
```

## Concurrency Considerations

**Important**: Eviction under concurrency may exhibit race conditions:

```python
# Thread A checks
if not m.is_full():
    # Thread B inserts, triggering eviction
    m['key_a'] = value_a  # May still evict!
```

The map remains consistent, but:
- With `eviction='error'`: May raise even after `is_full()` returns False
- With `eviction='oldest'`: Multiple threads may evict concurrently

### Safe Pattern

```python
def safe_insert(m, key, value):
    """Insert with retry on overflow."""
    for _ in range(3):
        try:
            m[key] = value
            return True
        except BoundedMapFullError:
            time.sleep(0.001)  # Brief backoff
    return False
```

## Thread Safety

| Operation | Safety | Notes |
|-----------|--------|-------|
| Read | Lock-free | Same as SkipListMap |
| Insert (no eviction) | Lock-free | Same as SkipListMap |
| Insert (with eviction) | Serialized | Eviction may block |
| is_full | Wait-free | Approximate |

## Performance

| Operation | Complexity | Notes |
|-----------|------------|-------|
| Insert (no eviction) | O(log n) | Same as SkipListMap |
| Insert (with eviction) | O(log n) | Plus eviction cost |
| Eviction | O(log n) | Removes first/last key |

## Configuration

```python
# Maximum entries
maxsize: int  # Required, must be > 0

# Eviction policy
eviction: str  # 'error', 'oldest', 'newest'

# Inherited from SkipListMap
cmp: Callable  # Custom comparator
key: Callable  # Key extraction function
```
