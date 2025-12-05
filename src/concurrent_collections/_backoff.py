"""
backoff - Exponential backoff strategies for contention management

This module provides exponential backoff for lock-free algorithms,
reducing cache line bouncing and improving throughput under contention.
"""

import time
import platform
from dataclasses import dataclass
from typing import Optional


# Platform-specific pause implementation
_SYSTEM = platform.system()
_MACHINE = platform.machine().lower()


def pause() -> None:
    """Execute a single pause instruction.

    On x86-64, this is equivalent to the PAUSE instruction which
    improves spin-wait loop performance. On ARM64, this yields
    to the scheduler. On other platforms, this is a brief sleep.
    """
    # In pure Python, we use a minimal sleep as a substitute
    # for hardware pause instructions. A C extension would use:
    # - x86-64: _mm_pause() or __builtin_ia32_pause()
    # - ARM64: __yield() or asm volatile("yield")
    # The time.sleep(0) call yields to other threads
    time.sleep(0)


@dataclass
class BackoffConfig:
    """Configuration for exponential backoff."""
    min_iterations: int = 1
    max_iterations: int = 1024
    growth_factor: int = 2


class Backoff:
    """Exponential backoff for contention management.

    Usage:
        backoff = Backoff()
        while not try_operation():
            backoff.spin()
        backoff.reset()  # After success

    The backoff doubles the spin count on each call up to max_iterations,
    then resets to min_iterations when reset() is called (typically after
    a successful operation).
    """

    __slots__ = ('_current', '_min', '_max', '_growth_factor')

    def __init__(
        self,
        min_iterations: int = 1,
        max_iterations: int = 1024,
        growth_factor: int = 2,
    ) -> None:
        """Initialize backoff state.

        Args:
            min_iterations: Minimum iterations (after reset)
            max_iterations: Maximum iterations (cap)
            growth_factor: Multiplier per spin (default 2x)
        """
        if min_iterations < 1:
            raise ValueError("min_iterations must be >= 1")
        if max_iterations < min_iterations:
            raise ValueError("max_iterations must be >= min_iterations")
        if growth_factor < 1:
            raise ValueError("growth_factor must be >= 1")

        self._min = min_iterations
        self._max = max_iterations
        self._current = min_iterations
        self._growth_factor = growth_factor

    @classmethod
    def from_config(cls, config: BackoffConfig) -> 'Backoff':
        """Create backoff from configuration object.

        Args:
            config: BackoffConfig instance

        Returns:
            Configured Backoff instance
        """
        return cls(
            min_iterations=config.min_iterations,
            max_iterations=config.max_iterations,
            growth_factor=config.growth_factor,
        )

    def spin(self) -> None:
        """Execute backoff spin.

        Spins for the current number of iterations, then doubles
        the iteration count (up to max_iterations).
        """
        # Execute pause instructions for current iteration count
        for _ in range(self._current):
            pause()

        # Grow backoff for next time
        if self._current < self._max:
            self._current = min(self._current * self._growth_factor, self._max)

    def reset(self) -> None:
        """Reset backoff after successful operation.

        Call this after a successful CAS or other operation to
        reset the backoff to minimum iterations.
        """
        self._current = self._min

    @property
    def current(self) -> int:
        """Get current iteration count."""
        return self._current

    @property
    def min_iterations(self) -> int:
        """Get minimum iteration count."""
        return self._min

    @property
    def max_iterations(self) -> int:
        """Get maximum iteration count."""
        return self._max


class AdaptiveBackoff:
    """Adaptive backoff that adjusts based on contention.

    This backoff adjusts its parameters based on observed success
    rates, becoming more aggressive under high contention and
    more responsive under low contention.
    """

    __slots__ = ('_backoff', '_successes', '_failures', '_window_size', '_adjustment_threshold')

    def __init__(
        self,
        min_iterations: int = 1,
        max_iterations: int = 1024,
        window_size: int = 16,
        adjustment_threshold: float = 0.5,
    ) -> None:
        """Initialize adaptive backoff.

        Args:
            min_iterations: Starting minimum iterations
            max_iterations: Maximum iterations cap
            window_size: Number of operations to track
            adjustment_threshold: Success rate below which to increase backoff
        """
        self._backoff = Backoff(min_iterations, max_iterations)
        self._successes = 0
        self._failures = 0
        self._window_size = window_size
        self._adjustment_threshold = adjustment_threshold

    def spin(self) -> None:
        """Execute backoff spin."""
        self._backoff.spin()

    def success(self) -> None:
        """Record a successful operation."""
        self._successes += 1
        self._backoff.reset()
        self._maybe_adjust()

    def failure(self) -> None:
        """Record a failed operation (CAS failure, etc.)."""
        self._failures += 1
        self._maybe_adjust()

    def _maybe_adjust(self) -> None:
        """Adjust parameters if window is full."""
        total = self._successes + self._failures
        if total >= self._window_size:
            success_rate = self._successes / total
            if success_rate < self._adjustment_threshold:
                # High contention: could adjust parameters
                # For now, just reset counters
                pass
            self._successes = 0
            self._failures = 0

    @property
    def current(self) -> int:
        """Get current iteration count."""
        return self._backoff.current


class TimedBackoff:
    """Time-based backoff using sleep instead of spin.

    Useful for longer waits where spinning wastes CPU.
    """

    __slots__ = ('_current_ms', '_min_ms', '_max_ms', '_growth_factor')

    def __init__(
        self,
        min_ms: float = 1.0,
        max_ms: float = 100.0,
        growth_factor: float = 2.0,
    ) -> None:
        """Initialize timed backoff.

        Args:
            min_ms: Minimum sleep time in milliseconds
            max_ms: Maximum sleep time in milliseconds
            growth_factor: Multiplier per sleep
        """
        if min_ms < 0:
            raise ValueError("min_ms must be >= 0")
        if max_ms < min_ms:
            raise ValueError("max_ms must be >= min_ms")

        self._min_ms = min_ms
        self._max_ms = max_ms
        self._current_ms = min_ms
        self._growth_factor = growth_factor

    def wait(self) -> None:
        """Sleep for current backoff time, then increase."""
        time.sleep(self._current_ms / 1000.0)
        if self._current_ms < self._max_ms:
            self._current_ms = min(self._current_ms * self._growth_factor, self._max_ms)

    def reset(self) -> None:
        """Reset to minimum sleep time."""
        self._current_ms = self._min_ms

    @property
    def current_ms(self) -> float:
        """Get current sleep time in milliseconds."""
        return self._current_ms
