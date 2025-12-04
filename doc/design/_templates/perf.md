# [Module Name] — Performance

## Overview

[Performance characteristics and optimization strategy]

## Targets

| Operation | Target (single-thread) | Target (8 threads) | Measurement |
|-----------|----------------------|-------------------|-------------|
| [Op] | [X ops/sec or latency] | [X ops/sec] | [Benchmark name] |

## Complexity Analysis

| Operation | Time (avg) | Time (worst) | Space | Notes |
|-----------|------------|--------------|-------|-------|
| [Op] | O(?) | O(?) | O(?) | [Conditions] |

## Benchmarks

### Microbenchmarks

| Benchmark | Description | Threads | Workload |
|-----------|-------------|---------|----------|
| `bench_[name]` | [What it measures] | 1,2,4,8 | [Pattern] |

### Contention Benchmarks

| Benchmark | Contention Level | Expected Scaling |
|-----------|------------------|------------------|
| `bench_[name]` | Low/Medium/High | [Linear/Sublinear/etc] |

## Baseline Comparisons

| Competitor | Our Performance | Notes |
|------------|-----------------|-------|
| [Library/approach] | [X% faster/slower] | [Conditions] |

## Optimization Notes

### Applied Optimizations

| Optimization | Effect | Tradeoff |
|--------------|--------|----------|
| [Technique] | [Improvement] | [Cost] |

### Considered but Rejected

| Optimization | Why Rejected |
|--------------|--------------|
| [Technique] | [Reason] |

## Cache Behavior

[Cache line utilization, false sharing prevention]

| Structure | Size | Cache Lines | Padding |
|-----------|------|-------------|---------|
| [Struct] | [bytes] | [N] | [bytes] |

## Memory Allocation Patterns

[Allocation frequency, sizes, cross-thread behavior]

## Profiling Data

[Summary of profiling results, hot spots identified]

### CPU Profile

| Function | % Time | Notes |
|----------|--------|-------|
| [func] | [%] | [Observation] |

### Contention Profile

| Lock/CAS | Contention Rate | Mitigation |
|----------|-----------------|------------|
| [Location] | [%] | [Approach] |

## Platform Variations

| Platform | Relative Performance | Notes |
|----------|---------------------|-------|
| Linux x86-64 | Baseline | [Optimizations active] |
| macOS ARM64 | [X%] | [Differences] |
| Windows x86-64 | [X%] | [Differences] |

## Regression Tracking

[How performance regressions are detected]

- Benchmark frequency: [When run]
- Threshold for alert: [X% regression]
- Historical data: [Location]
