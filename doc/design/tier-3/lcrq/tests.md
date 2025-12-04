# lcrq — Test Specification

## Availability Tests

| Test ID | Description |
|---------|-------------|
| `test_support_detection` | Correctly detect CMPXCHG16B |
| `test_fallback_to_scq` | Use SCQ on unsupported platforms |

## Unit Tests

| Test ID | Description |
|---------|-------------|
| `test_create_destroy` | Create/destroy queue |
| `test_enqueue_dequeue` | Basic operations |
| `test_fifo_order` | FIFO preserved |
| `test_ring_growth` | Allocate new rings on demand |
| `test_ring_retirement` | Old rings properly retired |

## Concurrency Tests

| Test ID | Threads | Description |
|---------|---------|-------------|
| `test_mpmc_stress` | 8+8 | High contention |
| `test_ring_contention` | 16+16 | Ring allocation races |
| `test_vs_scq` | 8+8 | Compare with SCQ |

## Memory Tests

| Test ID | Description |
|---------|-------------|
| `test_16byte_alignment` | Slots properly aligned |
| `test_no_leaks` | Rings freed correctly |
| `test_asan` | No memory errors |

## Performance Tests

| Test ID | Target |
|---------|--------|
| `bench_mpmc` | >8M ops/s |
| `bench_latency` | P99 < 500ns |

## Coverage

- Line: ≥90%
- Ring lifecycle: 100%
