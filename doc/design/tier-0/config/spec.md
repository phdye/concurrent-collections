# config — Specification

## Overview

The `config` module guarantees consistent runtime configuration detection and provides stable configuration values throughout program execution. Configuration is detected once at module import and remains stable unless explicitly changed.

## Invariants

1. **Detection Stability**: `gil_disabled` never changes after module initialization
2. **Backend Consistency**: `active_backend` reflects current `force_backend` and GIL state
3. **Feature Accuracy**: `detected_features` accurately reflects hardware capabilities
4. **Environment Precedence**: Environment variables override programmatic defaults

## Preconditions

- Python interpreter initialized
- `sys` module available
- For LCRQ: x86-64 with CMPXCHG16B support

## Contracts by Operation

### cc_config_init

**Signature:**
```c
int cc_config_init(void);
```

**Description:** Initialize global configuration state. Called automatically at module import.

**Preconditions:**
- Python interpreter initialized
- Not previously initialized (idempotent)

**Postconditions:**
- `cc_config.gil_disabled` reflects actual GIL state
- `cc_config.active_backend` set based on GIL state and `force_backend`
- `cc_config.detected_arch` set to current architecture
- `cc_config.detected_features` populated
- Environment variable overrides applied

**Errors:**
- Returns -1 on Python API error (exception set)
- Returns 0 on success

**Complexity:** O(1)

**Thread Safety:** Thread-safe (called once at import under GIL)

---

### cc_config_gil_disabled

**Signature:**
```c
bool cc_config_gil_disabled(void);
```

**Description:** Query whether GIL is disabled in current runtime.

**Preconditions:**
- `cc_config_init()` completed

**Postconditions:**
- Returns true if free-threaded Python runtime
- Returns false if GIL-enabled Python runtime

**Errors:** None

**Complexity:** O(1)

**Thread Safety:** Thread-safe (reads immutable value)

---

### cc_config_active_backend

**Signature:**
```c
int cc_config_active_backend(void);
```

**Description:** Query which backend is active (lock-free or locked).

**Preconditions:**
- `cc_config_init()` completed

**Postconditions:**
- Returns `BACKEND_LOCK_FREE` or `BACKEND_LOCKED`
- Reflects current `force_backend` setting and GIL state

**Errors:** None

**Complexity:** O(1)

**Thread Safety:** Thread-safe

---

### config.force_backend (Python setter)

**Description:** Set backend selection mode.

**Preconditions:**
- Value is one of: `'auto'`, `'lock_free'`, `'locked'`

**Postconditions:**
- `force_backend` updated to new value
- `active_backend` recalculated
- Existing containers continue using their original backend

**Errors:**
- `ValueError` if invalid value

**Thread Safety:** Thread-safe (atomic update)

**Note:** Changing after containers created does not affect existing containers.

---

### config.queue_backend (Python setter)

**Description:** Set queue backend selection mode.

**Preconditions:**
- Value is one of: `'auto'`, `'scq'`, `'lcrq'`
- If `'lcrq'`: must be on x86-64 with CMPXCHG16B

**Postconditions:**
- `queue_backend` updated to new value
- `active_queue_backend` recalculated

**Errors:**
- `ValueError` if invalid value
- `RuntimeError` if `'lcrq'` requested but unavailable

**Thread Safety:** Thread-safe (atomic update)

## Error Handling

| Error Condition | Detection | Response |
|-----------------|-----------|----------|
| Invalid backend string | String comparison | `ValueError` |
| LCRQ unavailable | Feature detection | `RuntimeError` |
| Python API failure | NULL return | Exception propagation |

## Thread Safety

| Guarantee | Scope | Notes |
|-----------|-------|-------|
| Read safety | All getters | Always safe to read |
| Write atomicity | All setters | Atomic updates |
| Initialization | Single-threaded | Under GIL at import |

## Memory Model

Configuration reads require no memory barriers (immutable after init or atomically updated).

Configuration writes use release semantics to ensure visibility.

## Performance Bounds

| Operation | Average | Worst Case | Notes |
|-----------|---------|------------|-------|
| Any getter | O(1) | O(1) | Direct memory read |
| Any setter | O(1) | O(1) | Atomic write |
| Init | O(1) | O(1) | Fixed operations |

## Python API Constraints

```python
# These are read-only after init
config.gil_disabled          # Cannot be set
config.active_backend        # Derived from force_backend
config.detected_arch         # Immutable
config.detected_features     # Immutable
config.available_queue_backends  # Immutable

# These can be set at runtime
config.force_backend         # Affects new containers only
config.queue_backend         # Affects new queues only
config.smr_scheme            # Affects new containers only
config.retire_threshold      # Can affect running SMR
config.enable_statistics     # Immediate effect
```
