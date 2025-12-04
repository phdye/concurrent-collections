# [Module Name] — Specification

## Overview

[What behavior this module guarantees]

## Invariants

[Properties that must always hold]

1. **[Invariant Name]**: [Description]
2. **[Invariant Name]**: [Description]

## Preconditions

[Global preconditions for using this module]

- [Precondition 1]
- [Precondition 2]

## Contracts by Operation

### [Operation Name]

**Signature:**
```c
ReturnType operation_name(ParamType param);
```

**Description:** [What this operation does]

**Preconditions:**
- [Condition 1]
- [Condition 2]

**Postconditions:**
- [Condition 1]
- [Condition 2]

**Errors:**
- [Error condition] → [Response/return value]

**Complexity:** O(?)

**Thread Safety:** [Lock-free / Blocking / Thread-unsafe]

---

### [Next Operation]

...

## Error Handling

| Error Condition | Detection | Response |
|-----------------|-----------|----------|
| [Condition] | [How detected] | [What happens] |

## Thread Safety

[Concurrency guarantees for the module as a whole]

| Guarantee | Scope | Notes |
|-----------|-------|-------|
| [Guarantee] | [What it applies to] | [Caveats] |

## Memory Model

[Memory ordering requirements, barrier semantics]

## Performance Bounds

| Operation | Average | Worst Case | Notes |
|-----------|---------|------------|-------|
| [Op] | O(?) | O(?) | [Conditions for worst case] |

## Formal Properties

[Reference to TLA+ spec if applicable]

See `spec.tla` for formal verification of:
- [Property 1]
- [Property 2]
