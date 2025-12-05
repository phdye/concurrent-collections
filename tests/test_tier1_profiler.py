"""Tests for profiler module (Tier 1)."""

import time
import threading
import pytest

from concurrent_collections import (
    ComparatorProfiler,
    ProfilerReport,
    OptimizationLevel,
)


class TestProfilerReport:
    """Tests for ProfilerReport dataclass."""

    def test_default_values(self):
        """ProfilerReport has reasonable defaults."""
        report = ProfilerReport()
        assert report.wall_time_sec == 0.0
        assert report.comparison_count == 0
        assert report.comparator_time_pct == 0.0

    def test_optimization_level_none_needed(self):
        """Low overhead returns NONE_NEEDED."""
        report = ProfilerReport(comparator_time_pct=3.0)
        assert report.optimization_level == OptimizationLevel.NONE_NEEDED

    def test_optimization_level_consider_key(self):
        """Moderate overhead returns CONSIDER_KEY_FUNCTION."""
        report = ProfilerReport(comparator_time_pct=15.0)
        assert report.optimization_level == OptimizationLevel.CONSIDER_KEY_FUNCTION

    def test_optimization_level_consider_native(self):
        """High overhead returns CONSIDER_NATIVE."""
        report = ProfilerReport(comparator_time_pct=35.0)
        assert report.optimization_level == OptimizationLevel.CONSIDER_NATIVE

    def test_optimization_level_critical(self):
        """Critical overhead returns CRITICAL."""
        report = ProfilerReport(comparator_time_pct=60.0)
        assert report.optimization_level == OptimizationLevel.CRITICAL

    def test_recommendation_string(self):
        """recommendation() returns helpful string."""
        report = ProfilerReport(comparator_time_pct=25.0)
        rec = report.recommendation()
        assert isinstance(rec, str)
        assert len(rec) > 0

    def test_str_representation(self):
        """str() returns formatted report."""
        report = ProfilerReport(
            wall_time_sec=1.0,
            comparator_time_sec=0.2,
            comparator_time_pct=20.0,
            comparison_count=1000,
        )
        s = str(report)
        assert 'ComparatorProfiler Report' in s
        assert '1000' in s or '1,000' in s

    def test_to_dict(self):
        """to_dict() returns dictionary."""
        report = ProfilerReport(
            wall_time_sec=1.0,
            comparison_count=500,
        )
        d = report.to_dict()
        assert isinstance(d, dict)
        assert d['wall_time_sec'] == 1.0
        assert d['comparison_count'] == 500

    def test_to_json(self):
        """to_json() returns valid JSON."""
        import json
        report = ProfilerReport(wall_time_sec=1.5)
        json_str = report.to_json()
        parsed = json.loads(json_str)
        assert parsed['wall_time_sec'] == 1.5


class TestComparatorProfiler:
    """Tests for ComparatorProfiler class."""

    def test_init(self):
        """ComparatorProfiler initializes correctly."""
        profiler = ComparatorProfiler()
        assert profiler is not None

    def test_start_stop(self):
        """start() and stop() work correctly."""
        profiler = ComparatorProfiler()
        profiler.start()
        time.sleep(0.01)
        report = profiler.stop()

        assert isinstance(report, ProfilerReport)
        assert report.wall_time_sec >= 0.01

    def test_context_manager(self):
        """Context manager works correctly."""
        with ComparatorProfiler() as profiler:
            time.sleep(0.01)

        report = profiler.report
        assert report.wall_time_sec >= 0.01

    def test_record_comparison(self):
        """record_comparison() updates counts."""
        profiler = ComparatorProfiler()
        profiler.start()

        profiler.record_comparison(1000)  # 1μs
        profiler.record_comparison(2000)  # 2μs

        report = profiler.stop()
        assert report.comparison_count == 2
        assert report.comparator_time_sec > 0

    def test_record_with_container(self):
        """record_comparison() tracks container stats."""
        profiler = ComparatorProfiler()
        profiler.start()

        profiler.record_comparison(1000, container_name='test_map')
        profiler.record_comparison(2000, container_name='test_map')
        profiler.record_comparison(1500, container_name='other_map')

        report = profiler.stop()
        assert 'test_map' in report.containers
        assert report.containers['test_map'].comparison_count == 2
        assert 'other_map' in report.containers
        assert report.containers['other_map'].comparison_count == 1

    def test_thread_tracking(self):
        """Profiler tracks per-thread statistics."""
        profiler = ComparatorProfiler()
        profiler.start()

        def worker():
            profiler.record_comparison(1000)

        threads = [threading.Thread(target=worker) for _ in range(3)]
        for t in threads:
            t.start()
        for t in threads:
            t.join()

        report = profiler.stop()
        # Should have stats for multiple threads
        assert len(report.threads) >= 1

    def test_percentile_tracking(self):
        """Profiler tracks latency percentiles."""
        profiler = ComparatorProfiler(track_percentiles=True)
        profiler.start()

        # Record comparisons with varying latencies
        for i in range(100):
            profiler.record_comparison(i * 100)  # 0, 100, 200, ... ns

        report = profiler.stop()
        assert report.p50_comparison_ns > 0
        assert report.p95_comparison_ns >= report.p50_comparison_ns
        assert report.max_comparison_ns >= report.p95_comparison_ns

    def test_trace_samples(self):
        """Profiler captures trace samples."""
        profiler = ComparatorProfiler(trace_samples=5)
        profiler.start()

        for i in range(10):
            profiler.record_comparison(1000, a=i, b=i+1, result=-1)

        report = profiler.stop()
        # Should have at most 5 traces
        assert len(report.traces) == 5

    def test_reset(self):
        """reset() clears counters."""
        profiler = ComparatorProfiler()
        profiler.start()

        profiler.record_comparison(1000)
        profiler.record_comparison(2000)
        profiler.reset()

        report = profiler.stop()
        assert report.comparison_count == 0

    def test_report_property(self):
        """report property returns current state."""
        profiler = ComparatorProfiler()
        profiler.start()

        profiler.record_comparison(1000)
        intermediate = profiler.report
        assert intermediate.comparison_count == 1

        profiler.record_comparison(2000)
        final = profiler.stop()
        assert final.comparison_count == 2


class TestOptimizationLevel:
    """Tests for OptimizationLevel enum."""

    def test_values(self):
        """OptimizationLevel has expected values."""
        assert OptimizationLevel.NONE_NEEDED.value == 'none_needed'
        assert OptimizationLevel.CONSIDER_KEY_FUNCTION.value == 'consider_key_function'
        assert OptimizationLevel.CONSIDER_NATIVE.value == 'consider_native'
        assert OptimizationLevel.CRITICAL.value == 'critical'


class TestProfilerEdgeCases:
    """Tests for profiler edge cases."""

    def test_no_comparisons(self):
        """Report handles zero comparisons."""
        profiler = ComparatorProfiler()
        profiler.start()
        time.sleep(0.001)
        report = profiler.stop()

        assert report.comparison_count == 0
        assert report.avg_comparison_ns == 0

    def test_immediate_stop(self):
        """Stopping immediately after start works."""
        profiler = ComparatorProfiler()
        profiler.start()
        report = profiler.stop()
        assert report.wall_time_sec >= 0

    def test_multiple_start_stop(self):
        """Multiple start/stop cycles work."""
        profiler = ComparatorProfiler()

        for _ in range(3):
            profiler.start()
            profiler.record_comparison(1000)
            report = profiler.stop()
            assert report.comparison_count == 1
