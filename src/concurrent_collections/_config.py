"""
config - Runtime configuration and GIL detection

This module provides runtime configuration, GIL state detection, and backend
selection for concurrent_collections. It determines whether to use lock-free
or locked backends based on the Python runtime environment.
"""

import os
import sys
import threading
from enum import Enum
from typing import Optional, List, Dict, Any
from dataclasses import dataclass, field

from concurrent_collections._arch_detect import (
    get_arch_name,
    get_cpu_features,
    has_cmpxchg16b,
    Arch,
    get_arch,
)


class Backend(Enum):
    """Backend selection mode."""
    AUTO = "auto"
    LOCK_FREE = "lock_free"
    LOCKED = "locked"


class QueueBackend(Enum):
    """Queue backend selection mode."""
    AUTO = "auto"
    SCQ = "scq"
    LCRQ = "lcrq"


class SMRScheme(Enum):
    """Safe Memory Reclamation scheme."""
    IBR = "ibr"
    DEBRA = "debra"


def _detect_gil_disabled() -> bool:
    """Detect whether GIL is disabled in current runtime.

    Returns:
        True if running free-threaded Python (GIL disabled)
    """
    # Try sys._is_gil_enabled() first (Python 3.13+)
    if hasattr(sys, '_is_gil_enabled'):
        try:
            return not sys._is_gil_enabled()
        except Exception:
            pass

    # Fallback: check abiflags for 't' suffix (free-threaded build)
    abiflags = getattr(sys, 'abiflags', '')
    if 't' in abiflags:
        return True

    return False


def _get_env(name: str, default: Optional[str] = None) -> Optional[str]:
    """Get environment variable with prefix."""
    full_name = f"CONCURRENT_COLLECTIONS_{name}"
    return os.environ.get(full_name, default)


def _get_env_bool(name: str, default: bool = False) -> bool:
    """Get boolean environment variable."""
    value = _get_env(name)
    if value is None:
        return default
    return value.lower() in ('1', 'true', 'yes', 'on')


def _get_env_int(name: str, default: int) -> int:
    """Get integer environment variable."""
    value = _get_env(name)
    if value is None:
        return default
    try:
        return int(value)
    except ValueError:
        return default


class Config:
    """Global configuration for concurrent_collections.

    This class manages runtime configuration including GIL detection,
    backend selection, and various tuning parameters.

    Thread Safety:
        All reads are thread-safe. Writes use a lock and affect
        only containers created after the write.
    """

    __slots__ = (
        '_lock',
        '_gil_disabled',
        '_detected_arch',
        '_detected_features',
        '_force_backend',
        '_active_backend',
        '_queue_backend',
        '_active_queue_backend',
        '_smr_scheme',
        '_retire_threshold',
        '_max_reclaim_per_poll',
        '_enable_statistics',
        '_enable_contention_stats',
        '_initialized',
    )

    def __init__(self) -> None:
        """Initialize configuration (called once at module import)."""
        self._lock = threading.Lock()
        self._initialized = False
        self._init()

    def _init(self) -> None:
        """Perform initialization."""
        if self._initialized:
            return

        # Detect GIL state (immutable after init)
        self._gil_disabled = _detect_gil_disabled()

        # Detect architecture (immutable after init)
        self._detected_arch = get_arch_name()
        self._detected_features = get_cpu_features()

        # Initialize from environment or defaults
        force_backend_str = _get_env('FORCE_BACKEND', 'auto')
        try:
            self._force_backend = Backend(force_backend_str.lower())
        except ValueError:
            self._force_backend = Backend.AUTO

        queue_backend_str = _get_env('QUEUE_BACKEND', 'auto')
        try:
            self._queue_backend = QueueBackend(queue_backend_str.lower())
        except ValueError:
            self._queue_backend = QueueBackend.AUTO

        smr_scheme_str = _get_env('SMR_SCHEME', 'ibr')
        try:
            self._smr_scheme = SMRScheme(smr_scheme_str.lower())
        except ValueError:
            self._smr_scheme = SMRScheme.IBR

        self._retire_threshold = _get_env_int('RETIRE_THRESHOLD', 64)
        self._max_reclaim_per_poll = _get_env_int('MAX_RECLAIM_PER_POLL', 32)
        self._enable_statistics = _get_env_bool('ENABLE_STATS', False)
        self._enable_contention_stats = _get_env_bool('ENABLE_CONTENTION_STATS', False)

        # Calculate active backends
        self._update_active_backends()

        self._initialized = True

    def _update_active_backends(self) -> None:
        """Update active backend selections based on current settings."""
        # Determine active data structure backend
        if self._force_backend == Backend.AUTO:
            if self._gil_disabled:
                self._active_backend = Backend.LOCK_FREE
            else:
                self._active_backend = Backend.LOCKED
        else:
            self._active_backend = self._force_backend

        # Determine active queue backend
        if self._queue_backend == QueueBackend.AUTO:
            if get_arch() == Arch.X86_64 and has_cmpxchg16b():
                self._active_queue_backend = QueueBackend.LCRQ
            else:
                self._active_queue_backend = QueueBackend.SCQ
        elif self._queue_backend == QueueBackend.LCRQ:
            # Validate LCRQ is available
            if get_arch() != Arch.X86_64 or not has_cmpxchg16b():
                raise RuntimeError(
                    "LCRQ backend requires x86-64 with CMPXCHG16B support"
                )
            self._active_queue_backend = QueueBackend.LCRQ
        else:
            self._active_queue_backend = QueueBackend.SCQ

    # Read-only properties (immutable after init)

    @property
    def gil_disabled(self) -> bool:
        """True if running free-threaded Python (GIL disabled)."""
        return self._gil_disabled

    @property
    def detected_arch(self) -> str:
        """Detected CPU architecture ('x86_64', 'aarch64', etc.)."""
        return self._detected_arch

    @property
    def detected_features(self) -> Dict[str, Any]:
        """Detected CPU features as dictionary."""
        f = self._detected_features
        return {
            'cmpxchg16b': f.cmpxchg16b,
            'avx': f.avx,
            'avx2': f.avx2,
            'lse': f.lse,
            'lse2': f.lse2,
            'l1_cache_line_size': f.l1_cache_line_size,
            'l2_cache_line_size': f.l2_cache_line_size,
        }

    @property
    def available_queue_backends(self) -> List[str]:
        """List of available queue backends."""
        backends = ['scq']
        if get_arch() == Arch.X86_64 and has_cmpxchg16b():
            backends.append('lcrq')
        return backends

    @property
    def active_backend(self) -> str:
        """Currently active data structure backend ('lock_free' or 'locked')."""
        return self._active_backend.value

    @property
    def active_queue_backend(self) -> str:
        """Currently active queue backend ('scq' or 'lcrq')."""
        return self._active_queue_backend.value

    # Configurable properties

    @property
    def force_backend(self) -> str:
        """Backend selection mode ('auto', 'lock_free', 'locked')."""
        return self._force_backend.value

    @force_backend.setter
    def force_backend(self, value: str) -> None:
        """Set backend selection mode.

        Args:
            value: 'auto', 'lock_free', or 'locked'

        Raises:
            ValueError: If value is invalid

        Note:
            Changes only affect containers created after this call.
        """
        try:
            backend = Backend(value.lower())
        except ValueError:
            raise ValueError(
                f"Invalid backend: {value}. Must be 'auto', 'lock_free', or 'locked'"
            )
        with self._lock:
            self._force_backend = backend
            self._update_active_backends()

    @property
    def queue_backend(self) -> str:
        """Queue backend selection mode ('auto', 'scq', 'lcrq')."""
        return self._queue_backend.value

    @queue_backend.setter
    def queue_backend(self, value: str) -> None:
        """Set queue backend selection mode.

        Args:
            value: 'auto', 'scq', or 'lcrq'

        Raises:
            ValueError: If value is invalid
            RuntimeError: If 'lcrq' requested but unavailable
        """
        try:
            backend = QueueBackend(value.lower())
        except ValueError:
            raise ValueError(
                f"Invalid queue backend: {value}. Must be 'auto', 'scq', or 'lcrq'"
            )
        with self._lock:
            self._queue_backend = backend
            self._update_active_backends()

    @property
    def smr_scheme(self) -> str:
        """SMR scheme ('ibr' or 'debra')."""
        return self._smr_scheme.value

    @smr_scheme.setter
    def smr_scheme(self, value: str) -> None:
        """Set SMR scheme.

        Args:
            value: 'ibr' or 'debra'

        Raises:
            ValueError: If value is invalid
        """
        try:
            scheme = SMRScheme(value.lower())
        except ValueError:
            raise ValueError(
                f"Invalid SMR scheme: {value}. Must be 'ibr' or 'debra'"
            )
        with self._lock:
            self._smr_scheme = scheme

    @property
    def retire_threshold(self) -> int:
        """SMR retire threshold."""
        return self._retire_threshold

    @retire_threshold.setter
    def retire_threshold(self, value: int) -> None:
        """Set SMR retire threshold.

        Args:
            value: Positive integer threshold
        """
        if value < 1:
            raise ValueError("retire_threshold must be >= 1")
        with self._lock:
            self._retire_threshold = value

    @property
    def max_reclaim_per_poll(self) -> int:
        """Maximum nodes to reclaim per poll operation."""
        return self._max_reclaim_per_poll

    @max_reclaim_per_poll.setter
    def max_reclaim_per_poll(self, value: int) -> None:
        """Set maximum reclaim per poll.

        Args:
            value: Positive integer limit
        """
        if value < 1:
            raise ValueError("max_reclaim_per_poll must be >= 1")
        with self._lock:
            self._max_reclaim_per_poll = value

    @property
    def enable_statistics(self) -> bool:
        """Whether statistics collection is enabled."""
        return self._enable_statistics

    @enable_statistics.setter
    def enable_statistics(self, value: bool) -> None:
        """Enable or disable statistics collection."""
        with self._lock:
            self._enable_statistics = bool(value)

    @property
    def enable_contention_stats(self) -> bool:
        """Whether contention statistics are enabled."""
        return self._enable_contention_stats

    @enable_contention_stats.setter
    def enable_contention_stats(self, value: bool) -> None:
        """Enable or disable contention statistics."""
        with self._lock:
            self._enable_contention_stats = bool(value)

    def __repr__(self) -> str:
        """String representation of configuration."""
        return (
            f"Config("
            f"gil_disabled={self.gil_disabled}, "
            f"active_backend='{self.active_backend}', "
            f"detected_arch='{self.detected_arch}')"
        )


# Global configuration instance (initialized at module import)
config = Config()
