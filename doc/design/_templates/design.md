# [Module Name] — Design

## Overview

[2-3 sentence description of what this module does and why it exists]

## Dependencies

| Dependency | Purpose |
|------------|---------|
| [Module/Library] | [What we use it for] |

## Architecture

[High-level structure description]

### Data Structures

```c
// Key data structures with field descriptions
typedef struct {
    // ...
} ExampleStruct;
```

### Algorithms

[Key algorithms with complexity analysis]

| Algorithm | Complexity | Reference |
|-----------|------------|-----------|
| [Name] | O(?) | [Paper/source] |

### Concurrency Model

[Thread safety approach, synchronization primitives used]

## API Surface

### Public Functions

```c
// Function signatures with brief descriptions
ReturnType function_name(ParamType param);
```

### Internal Functions

[Key internal functions, if relevant]

## Design Decisions

| Decision | Choice | Rationale | Alternatives Considered |
|----------|--------|-----------|------------------------|
| [Topic] | [What we chose] | [Why] | [What we didn't choose] |

## Integration Points

[How this module connects to other modules]

## Open Questions

[Module-specific unresolved issues]
