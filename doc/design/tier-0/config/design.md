# config — Design

## Overview

The `config` module provides runtime configuration, GIL state detection, and backend selection for `concurrent_collections`. It determines whether to use lock-free or locked backends based on the Python runtime environment.

## Dependencies

| Dependency | Purpose |
|------------|---------|
| Python C API | `sys._is_gil_enabled()`, `sys.abiflags` access |
| arch_detect | Platform feature detection for queue backend selection |

## Architecture

### Configuration State

```c
typedef struct {
    // GIL state (detected at init)
    bool gil_disabled;

    // Backend selection
    enum { BACKEND_AUTO, BACKEND_LOCK_FREE, BACKEND_LOCKED } force_backend;
    enum { BACKEND_LOCK_FREE, BACKEND_LOCKED } active_backend;

    // Queue backend selection
    enum { QUEUE_AUTO, QUEUE_SCQ, QUEUE_LCRQ } queue_backend;
    enum { QUEUE_SCQ, QUEUE_LCRQ } active_queue_backend;

    // SMR configuration
    enum { SMR_IBR, SMR_DEBRA } smr_scheme;
    uint32_t retire_threshold;
    uint32_t max_reclaim_per_poll;

    // Debugging
    bool enable_statistics;
    bool enable_contention_stats;
} cc_config_t;

// Global configuration (initialized at module import)
extern cc_config_t cc_config;
```

### GIL Detection

```c
static bool detect_gil_disabled(void) {
    // Try sys._is_gil_enabled() first (Python 3.13+)
    PyObject *sys = PyImport_ImportModule("sys");
    if (sys) {
        if (PyObject_HasAttrString(sys, "_is_gil_enabled")) {
            PyObject *result = PyObject_CallMethod(sys, "_is_gil_enabled", NULL);
            if (result) {
                bool enabled = PyObject_IsTrue(result);
                Py_DECREF(result);
                Py_DECREF(sys);
                return !enabled;
            }
        }
        Py_DECREF(sys);
    }
    PyErr_Clear();

    // Fallback: check abiflags for 't' suffix
    PyObject *abiflags = PySys_GetObject("abiflags");
    if (abiflags && PyUnicode_Check(abiflags)) {
        const char *flags = PyUnicode_AsUTF8(abiflags);
        if (flags && strchr(flags, 't')) {
            return true;
        }
    }

    return false;
}
```

### Backend Selection Logic

```
┌─────────────────────────────────────────┐
│          force_backend setting          │
├─────────────────────────────────────────┤
│  'auto'      → Use GIL detection        │
│  'lock_free' → Force lock-free          │
│  'locked'    → Force locked             │
└─────────────────────────────────────────┘
                    │
                    ▼
┌─────────────────────────────────────────┐
│         GIL detection (if auto)         │
├─────────────────────────────────────────┤
│  GIL disabled → BACKEND_LOCK_FREE       │
│  GIL enabled  → BACKEND_LOCKED          │
└─────────────────────────────────────────┘
```

### Environment Variable Overrides

| Variable | Values | Effect |
|----------|--------|--------|
| `CONCURRENT_COLLECTIONS_FORCE_BACKEND` | `auto`, `lock_free`, `locked` | Override backend selection |
| `CONCURRENT_COLLECTIONS_QUEUE_BACKEND` | `auto`, `scq`, `lcrq` | Override queue backend |
| `CONCURRENT_COLLECTIONS_SMR_SCHEME` | `ibr`, `debra` | Override SMR scheme |
| `CONCURRENT_COLLECTIONS_RETIRE_THRESHOLD` | Integer | SMR retire threshold |
| `CONCURRENT_COLLECTIONS_ENABLE_STATS` | `0`, `1` | Enable statistics |

## API Surface

### Python API

```python
from concurrent_collections import config

# Read-only properties (detected at import)
config.gil_disabled          # bool: True if running free-threaded
config.active_backend        # str: 'lock_free' or 'locked'
config.detected_arch         # str: 'x86_64', 'aarch64', etc.
config.detected_features     # dict: {'cmpxchg16b': True, ...}
config.available_queue_backends  # list: ['scq', 'lcrq'] or ['scq']

# Configurable settings
config.force_backend = 'auto'      # 'auto', 'lock_free', 'locked'
config.queue_backend = 'auto'      # 'auto', 'scq', 'lcrq'
config.smr_scheme = 'ibr'          # 'ibr', 'debra'
config.retire_threshold = 64       # int
config.max_reclaim_per_poll = 32   # int
config.enable_statistics = False   # bool
config.enable_contention_stats = False  # bool
```

### C API

```c
// Initialize configuration (called at module import)
int cc_config_init(void);

// Query configuration
bool cc_config_gil_disabled(void);
int cc_config_active_backend(void);
int cc_config_active_queue_backend(void);

// Runtime reconfiguration (limited)
int cc_config_set_smr_scheme(int scheme);
int cc_config_set_retire_threshold(uint32_t threshold);
```

## Design Decisions

| Decision | Choice | Rationale | Alternatives Considered |
|----------|--------|-----------|------------------------|
| Detection timing | At module import | One-time cost, consistent behavior | Per-operation (overhead) |
| Default backend | Auto-detect | Optimal for runtime | Always lock-free (suboptimal under GIL) |
| Config mutability | Mostly read-only | Prevents mid-operation changes | Full mutability (race conditions) |
| Env var prefix | `CONCURRENT_COLLECTIONS_` | Clear namespace | Short prefix (collision risk) |

## Integration Points

- **All containers**: Query `active_backend` to select implementation
- **Queue classes**: Query `active_queue_backend` for SCQ vs LCRQ
- **SMR modules**: Query `smr_scheme`, `retire_threshold`
- **Statistics**: Check `enable_statistics` before recording

## Open Questions

| Question | Options | Impact |
|----------|---------|--------|
| Config change notification | Callback vs polling | How containers detect config changes |
| Thread-local overrides | Support vs reject | Per-thread backend selection |
