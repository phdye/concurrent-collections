# Tier 5: Extensions

## Overview

Extensions provide additional utilities built on top of the core containers. These are useful but represent minority use cases, so they're separated from the main API.

## Dependencies

- Tier 4 (Public API)

## Modules

| Module | Description | Complexity |
|--------|-------------|------------|
| `BoundedSkipListMap` | Size-limited wrapper with eviction policy | Low |

## Completion Criteria

### BoundedSkipListMap
- [ ] `maxsize` parameter limits entries
- [ ] `eviction='error'` raises `BoundedMapFullError` when full
- [ ] `eviction='oldest'` evicts `first_key()` to make room
- [ ] `is_full()` check available
- [ ] Inherits all `SkipListMap` functionality
- [ ] Documented race conditions under concurrency
- [ ] design.md, spec.md, tests.md complete

## Why in Extensions?

Bounded concurrent containers add complexity:
- Size tracking under concurrency has inherent races
- Eviction policies interact with concurrent access
- Minority use case—most users want unbounded

If demand warrants, may promote to core in future versions.

## API

```python
from concurrent_collections.recipes import BoundedSkipListMap, BoundedMapFullError

# Raise when full
m = BoundedSkipListMap(maxsize=1000)
m[key] = value  # Raises BoundedMapFullError if full

# Evict oldest when full
m = BoundedSkipListMap(maxsize=1000, eviction='oldest')
m[key] = value  # Evicts first_key() if full

# Check capacity
m.maxsize       # Maximum entries
m.is_full()     # True if at capacity
```

## Concurrency Considerations

### Size Tracking Race

```python
# This pattern has inherent races:
if not m.is_full():
    m[key] = value  # May still fail - another thread may have filled it
```

### Eviction Atomicity

With `eviction='oldest'`:
- Evict-then-insert is **not** atomic
- Window where map may be temporarily below maxsize
- Concurrent inserts may both evict, overshooting target

Document these behaviors clearly in user documentation.

## Future Extensions

Potential additions for post-1.0:
- `BoundedSkipListSet`
- `BoundedTreeMap` / `BoundedTreeSet`
- LRU-ordered variants
- TTL-based expiration
