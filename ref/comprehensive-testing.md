# Comprehensive Testing Methodology

**Purpose**: Universal testing methodology that adapts to project characteristics through feature detection
**Version**: 2.0
**Status**: Active

---

## Table of Contents

1. [Universal Testing Principles](#1-universal-testing-principles)
2. [Feature Detection & Applicable Requirements](#2-feature-detection--applicable-requirements)
3. [Test Dimension Analysis Methodology](#3-test-dimension-analysis-methodology)
4. [Coverage Requirements](#4-coverage-requirements)
5. [Testing Levels](#5-testing-levels)
6. [Domain-Specific Requirements](#6-domain-specific-requirements)
7. [Port Projects: Reference Analysis](#7-port-projects-reference-analysis)
8. [Test Organization](#8-test-organization)
9. [Test Quality Standards](#9-test-quality-standards)
10. [Acceptance Criteria](#10-acceptance-criteria)

---

## 1. Universal Testing Principles

### 1.1 Core Philosophy

**Goal**: Uncompromising Enterprise-Grade Reliability

**Fundamental Principle**: During development, **every step along the way**, for **all implemented functionality**, **every aspect is fully tested** including **all conceivable nuances**.

**No Excuses Policy**:
- ❌ "Hard to test" → Make it easier to test
- ❌ "Rarely executed" → Still must be tested
- ❌ "Error path" → Especially must be tested
- ❌ "Platform-specific" → Test on that platform
- ❌ "Performance overhead" → Test performance separately
- ❌ "Edge case" → Edge cases are critical
- ❌ "Unlikely scenario" → Test it anyway

### 1.2 Bottom-Up Testing Approach

**CRITICAL PRINCIPLE**: Always test bottom-up, as a faulty low-level item will cause a dependent item to break.

**Testing Order**:
1. Test the lowest level items that have **no** internal dependencies
2. Progressively work upward from least internally dependent to most internally dependent
3. **Never** test a component before its dependencies are verified

**Example Dependency-Ordered Testing**:
```
Level 1: No Dependencies
├── Core primitives (atomic operations, compiler hints)

Level 2: Depends on Level 1 Only
├── Basic synchronization (simple locks, backoff)

Level 3: Depends on Levels 1-2
├── Advanced synchronization (MCS, CLH locks)

Level 4: Depends on Levels 1-3
├── Memory reclamation (epoch-based, hazard pointers)

Level 5: Depends on Levels 1-4
├── Lock-free data structures (stacks, queues)

Level 6: Depends on Levels 1-5
├── Complex data structures (hash tables, trees)
```

### 1.3 Comprehensive Testing Scope

Test **everything** as soon as feasible:
- **Integrations** - Cross-module interactions and data flow
- **Algorithms** - Correctness of concurrent and lock-free algorithms
- **Use Cases** - Real-world application scenarios
- **Behavior** - State transitions and expected responses
- **Strategies** - Memory reclamation, backoff, optimization approaches
- **Internal Interfaces** - Module-to-module contracts
- **External Interfaces** - Public API surface
- **User Interfaces** - Documentation, examples, error messages
- **Error Paths** - All failure scenarios
- **Edge Cases** - All boundary conditions
- **Performance** - Efficiency under all conditions

### 1.4 Coverage Philosophy

**Line coverage is just the most fundamental testing requirement.**

Beyond line coverage, test:
- **100% of logical branches**
- **100% of decision paths**
- **100% of algorithm states**
- **100% of state transitions**
- **100% of invariants**
- **100% of preconditions and postconditions**
- **100% of error paths**

---

## 2. Feature Detection & Applicable Requirements

This section defines what requirements apply to your project based on automatically detectable features.

### 2.1 Feature Detection Rules

For each project, detect applicable features and apply corresponding requirements:

#### Feature: Multiple Variants/Implementations

**Detection**: Project has multiple implementations of the same interface

**Examples**:
- Multiple spinlock types (TAS, Ticket, MCS, CLH)
- Multiple hash table implementations
- Multiple sorting algorithms

**Applicable Requirements**:
- [Exhaustive Variant Testing](#331-exhaustive-variant-testing) ✓ REQUIRED
- [Variant Coverage Matrix](#424-variant-coverage-matrix) ✓ REQUIRED
- [Variant Test Templates](#8-test-organization) ✓ REQUIRED

#### Feature: Parametric Operations

**Detection**: Operations that work across multiple data types or sizes

**Examples**:
- Atomic operations on u8, u16, u32, u64, usize, pointers
- Generic collections with different element types
- Operations with multiple memory orderings

**Applicable Requirements**:
- [Parametric Testing Matrix](#425-parametric-operations-matrix) ✓ REQUIRED
- [Data Width Testing](#611-concurrency-primitives) ✓ REQUIRED
- Minimum test count: Operations × Data Types

#### Feature: Concurrency Primitives

**Detection**: Project includes synchronization primitives or concurrent data structures

**Keywords**: lock, mutex, atomic, concurrent, thread-safe, lock-free, wait-free

**Applicable Requirements**:
- [Concurrency-Specific Testing](#611-concurrency-primitives) ✓ REQUIRED
- [Model Checking](#52-concurrency-model-checking) ✓ REQUIRED
- [Race Detection](#910-continuous-integration-requirements) ✓ REQUIRED
- [Memory Ordering Tests](#611-concurrency-primitives) ✓ REQUIRED

#### Feature: Memory Reclamation

**Detection**: Project includes epoch-based reclamation, hazard pointers, or reference counting

**Applicable Requirements**:
- [Memory Reclamation Testing](#612-memory-reclamation-systems) ✓ REQUIRED
- [Leak Detection](#910-continuous-integration-requirements) ✓ REQUIRED
- [Stress Testing](#55-stress-testing) ✓ REQUIRED

#### Feature: Lock-Free Data Structures

**Detection**: Project includes lock-free or wait-free data structures

**Applicable Requirements**:
- [Linearizability Testing](#613-lock-free-data-structures) ✓ REQUIRED
- [Progress Guarantee Verification](#613-lock-free-data-structures) ✓ REQUIRED
- [ABA Problem Prevention](#613-lock-free-data-structures) ✓ REQUIRED

#### Feature: Port of Existing Library

**Detection**: Project description mentions "port", "implementation of", or references another library

**Applicable Requirements**:
- [Reference Test Analysis](#7-port-projects-reference-analysis) ✓ REQUIRED
- [Conformance Matrix](#72-test-conformance-analysis) ✓ REQUIRED
- [Gap Analysis](#73-gap-identification-and-closure) ✓ REQUIRED

#### Feature: Unsafe Code

**Detection**: Project contains `unsafe` blocks

**Applicable Requirements**:
- [Unsafe Code Testing](#614-unsafe-code) ✓ REQUIRED
- [Miri Verification](#910-continuous-integration-requirements) ✓ REQUIRED
- [Safety Invariant Documentation](#93-algorithmic-correctness-documentation) ✓ REQUIRED

#### Feature: Parser/Compiler

**Detection**: Project involves parsing, lexing, or compilation

**Applicable Requirements**:
- [Parser-Specific Testing](#615-parsers-and-compilers) ✓ REQUIRED
- [Grammar Coverage](#615-parsers-and-compilers) ✓ REQUIRED
- [Error Recovery Testing](#615-parsers-and-compilers) ✓ REQUIRED

#### Feature: Cryptographic Operations

**Detection**: Project involves encryption, hashing, signatures, or key derivation

**Applicable Requirements**:
- [Cryptography-Specific Testing](#616-cryptographic-code) ✓ REQUIRED
- [Test Vector Validation](#616-cryptographic-code) ✓ REQUIRED
- [Side-Channel Testing](#616-cryptographic-code) ✓ REQUIRED
- [Constant-Time Verification](#616-cryptographic-code) ✓ REQUIRED

### 2.2 Requirement Activation Checklist

For your project, check which features apply:

```markdown
## Project: [PROJECT_NAME]

### Feature Detection Results

- [ ] Multiple Variants/Implementations
  - If YES: Which? _________________________
  - Applicable Requirements: §3.3.1, §4.2.4, §8

- [ ] Parametric Operations
  - If YES: Operations? _____________ Types? _____________
  - Applicable Requirements: §4.2.5, §6.1.1
  - Minimum tests: _____ operations × _____ types = _____ tests

- [ ] Concurrency Primitives
  - If YES: Which? _________________________
  - Applicable Requirements: §6.1.1, §5.2, §9.10

- [ ] Memory Reclamation
  - If YES: Which mechanism? _________________________
  - Applicable Requirements: §6.1.2, §5.5, §9.10

- [ ] Lock-Free Data Structures
  - If YES: Which structures? _________________________
  - Applicable Requirements: §6.1.3

- [ ] Port of Existing Library
  - If YES: Original library? _________________________
  - Applicable Requirements: §7 (ALL SUBSECTIONS)

- [ ] Unsafe Code
  - If YES: Percentage of codebase? __________%
  - Applicable Requirements: §6.1.4, §9.10, §9.3

- [ ] Parser/Compiler
  - If YES: Grammar type? _________________________
  - Applicable Requirements: §6.1.5

- [ ] Cryptographic Operations
  - If YES: Which operations? _________________________
  - Applicable Requirements: §6.1.6
```

---

## 3. Test Dimension Analysis Methodology

### 3.1 Purpose

**Problem**: "Test everything" is vague without a methodology to identify what "everything" means.

**Solution**: Systematic analysis to discover ALL dimensions that require testing.

### 3.2 Dimension Discovery Process

#### Step 1: Enumerate API Surface

**For every module, document**:

```markdown
### Module: [MODULE_NAME]

#### Public Functions
- Function 1: `name(params) -> return`
- Function 2: `name(params) -> return`
- ... (list ALL public functions)
- **Total**: _____ functions

#### Public Types
- Type 1: `Name`
- Type 2: `Name`
- ... (list ALL public types)
- **Total**: _____ types

#### Implementations/Variants (if applicable)
- Variant 1: `Name`
- Variant 2: `Name`
- ... (list ALL variants)
- **Total**: _____ variants
```

#### Step 2: Enumerate Data Dimensions

**For parametric operations, document**:

```markdown
#### Data Types Supported
- [ ] u8
- [ ] u16
- [ ] u32
- [ ] u64
- [ ] u128
- [ ] usize
- [ ] i8, i16, i32, i64, i128, isize
- [ ] f32, f64
- [ ] bool
- [ ] pointers (*const T, *mut T)
- [ ] Custom types: _______________

#### Memory Orderings (if atomic operations)
- [ ] Relaxed
- [ ] Acquire
- [ ] Release
- [ ] AcqRel
- [ ] SeqCst

#### Operation Modes
- [ ] Blocking
- [ ] Non-blocking (try_*)
- [ ] Timed (timeout)
- [ ] Other: _______________
```

#### Step 3: Enumerate State Dimensions

**For stateful components, document**:

```markdown
#### Valid States
- State 1: [Description]
- State 2: [Description]
- ... (list ALL valid states)
- **Total**: _____ states

#### Invalid/Error States
- Error State 1: [Description]
- Error State 2: [Description]
- ... (list ALL error states)
- **Total**: _____ error states

#### State Transitions
Create state transition diagram showing:
- All valid transitions
- All invalid transitions (that must be prevented)
- All error transitions
```

#### Step 4: Enumerate Execution Dimensions

**For concurrent code, document**:

```markdown
#### Thread Configurations
- [ ] Single-threaded
- [ ] 2 threads (low contention)
- [ ] 4 threads
- [ ] 8 threads
- [ ] 16 threads (high contention)
- [ ] 32+ threads (extreme contention)
- [ ] Pathological: all threads synchronized

#### Contention Patterns
- [ ] No contention (independent operations)
- [ ] Low contention (occasional overlap)
- [ ] High contention (frequent conflicts)
- [ ] Pathological contention (all threads hitting same operation)

#### Load Patterns
- [ ] Empty collection
- [ ] Partially filled
- [ ] Nearly full
- [ ] Full
- [ ] Alternating full/empty
```

#### Step 5: Calculate Minimum Test Count

**Formula**:
```
Minimum Tests = (Functions) × (Variants) × (Data Types) × (States) × (Thread Configs)
```

**Example - Atomic Operations**:
```
Operations: 15 (load, store, add, sub, cas, swap, and, or, xor, etc.)
Data Types: 6 (u8, u16, u32, u64, usize, ptr)
Minimum Tests: 15 × 6 = 90 tests minimum
```

**Example - Spinlocks**:
```
Variants: 5 (TAS, Ticket, MCS, CLH, Anderson)
Operations per variant: 3 (lock, unlock, trylock)
Thread configs: 5 (1, 2, 4, 8, 16)
Minimum Tests: 5 × 3 × 5 = 75 tests minimum
```

### 3.3 Test Dimension Documentation

#### 3.3.1 Exhaustive Variant Testing

**Principle**: If you provide N variants of something, ALL N variants must be tested equivalently.

**Requirements**:

1. **Identify Template Test**: Choose the canonical test for one variant
2. **Apply to All Variants**: Every variant gets the same test suite
3. **Document Coverage**: Use coverage matrix (see §4.2.4)
4. **CI Enforcement**: CI fails if any variant lacks corresponding test

**Example - Spinlock Testing**:
```rust
// Template test (applies to ALL spinlock variants)
fn test_lock_unlock_maintains_count<L: Spinlock>(lock: L) {
    let counter = AtomicUsize::new(0);
    let threads = 16;
    let iterations = 1000;
    
    // Test logic...
}

// Apply to ALL variants
#[test]
fn test_tas_lock_unlock_maintains_count() {
    test_lock_unlock_maintains_count(TasLock::new());
}

#[test]
fn test_ticket_lock_unlock_maintains_count() {
    test_lock_unlock_maintains_count(TicketLock::new());
}

// ... repeat for MCS, CLH, Anderson, etc.
```

**Red Flags** (indicators of incomplete variant testing):
- ⚠️ Tests exist for Variant A but not Variant B
- ⚠️ Some variants have more tests than others
- ⚠️ Coverage matrix shows gaps for specific variants
- ⚠️ Test count doesn't match: variants × template_tests

#### 3.3.2 Parametric Operation Testing

**Principle**: If an operation works on N data types, test ALL N data types.

**Requirements**:

1. **Enumerate All Types**: List every supported data type
2. **Test Each Type**: Every type gets the same test logic
3. **Document Coverage**: Use parametric operations matrix (see §4.2.5)
4. **No Assumptions**: Don't assume "if u32 works, u64 works"

**Example - Atomic Operations**:
```rust
// Template test for one data type
fn test_atomic_add_correctness<T: AtomicInteger>() {
    // Test logic for add operation
}

// Apply to ALL types
#[test] fn test_atomic_add_u8() { test_atomic_add_correctness::<u8>(); }
#[test] fn test_atomic_add_u16() { test_atomic_add_correctness::<u16>(); }
#[test] fn test_atomic_add_u32() { test_atomic_add_correctness::<u32>(); }
#[test] fn test_atomic_add_u64() { test_atomic_add_correctness::<u64>(); }
#[test] fn test_atomic_add_usize() { test_atomic_add_correctness::<usize>(); }
```

---

## 4. Coverage Requirements

### 4.1 Universal Coverage Targets

**Core Principle**: 100% coverage is the minimum requirement, with documented exceptions only for tooling limitations.

| Metric | Target | Exceptions Allowed | Documentation Required |
|--------|--------|-------------------|------------------------|
| **Line Coverage** | 100% | Uninstrumentable lines only | Coverage-Exceptions.md |
| **Branch Coverage** | 100% | Uninstrumentable branches only | Coverage-Exceptions.md |
| **Logic Path Coverage** | 100% | None | Test traceability matrix |
| **Algorithm Coverage** | 100% | None | Algorithm documentation |
| **State Coverage** | 100% | None | State machine documentation |
| **Transition Coverage** | 100% | None | Transition testing docs |
| **Variant Coverage** | 100% | None | Variant coverage matrix |
| **Parametric Coverage** | 100% | None | Parametric operations matrix |

### 4.2 Coverage Documentation Requirements

#### 4.2.1 Uninstrumentable Lines Documentation

**File**: `Coverage-Exceptions.md` (project root)

**Required Information for Each Exception**:

```markdown
### Exception #N: [Brief Description]

**Location**: `file.rs:123-127`

**Reason**: Cannot be instrumented by [tool name] because [specific limitation]

**Code Context**:
```rust
fn example() {
    let x = compute();        // Line 122 - COVERED ✓
    unsafe {                  // Line 123 - UNINSTRUMENTABLE
        critical_op(x);       // Line 124 - UNINSTRUMENTABLE
    }                         // Line 125 - UNINSTRUMENTABLE
    use_result();            // Line 126 - COVERED ✓
}
```

**Proof of Execution**:
- Line 122 is covered (before uninstrumentable block)
- Line 126 is covered (after uninstrumentable block)
- No conditional branches between 122 and 126
- Execution is deterministic
- Therefore, lines 123-125 MUST execute

**Test Case**: `test_critical_operation` in `tests/mod.rs:45`

**Date Documented**: 2025-11-30
**Reviewed By**: [Reviewer 1], [Reviewer 2]
**Approved**: [Yes/No]
```

**Acceptance Criteria**:
- Each exception fully documented with ALL required information
- Proof of execution is sound (no gaps in logic)
- Test case actually exercises the code path
- Two reviewers have approved
- Exceptions represent <1% of total codebase

#### 4.2.2 Untestable Logic Documentation

**File**: `Untestable-Logic.md` (project root)

**When Required**: If ANY aspect of logic/algorithm cannot be tested (rare)

**Required Information**:

```markdown
### Untestable Aspect #N: [Brief Description]

**Component**: [Module::Function or Algorithm Name]

**Aspect**: [What specifically cannot be tested]

**Reason**: [Why it cannot be tested - must be fundamental limitation]

**Acceptable Reasons ONLY**:
1. Non-deterministic timing (exact timing of concurrent events)
2. Hardware-specific behavior (on unavailable hardware)
3. Quantum effects (extremely rare race conditions - must verify mathematically)
4. External dependencies (OS/hardware behavior beyond control)

**What IS Tested**: [Related aspects that ARE testable]

**Mitigation Strategies**:
- [How you minimize risk despite inability to test]
- [Alternative verification approaches]

**Risk Assessment**: [LOW / MEDIUM / HIGH]
- Justification: [Why this risk level]

**Alternative Verification**:
- [Manual inspection approach]
- [Formal methods used, if any]
- [Mathematical proof, if applicable]

**Date Documented**: 2025-11-30
**Reviewed By**: [Reviewer 1], [Reviewer 2]
```

**UNACCEPTABLE Reasons**:
- ❌ "Too complex to test"
- ❌ "Not enough time"
- ❌ "Performance overhead"
- ❌ "Edge case"
- ❌ "Unlikely scenario"

#### 4.2.3 Test-to-Requirement Traceability

**File**: `Test-Traceability.md` (project root)

**Purpose**: Map every requirement/feature to test cases that verify it

```markdown
## Module: [MODULE_NAME]

### Requirement 1: [Description]
- Tested by: `test_case_1`, `test_case_2`
- Coverage: 100%
- Status: ✓ Complete

### Requirement 2: [Description]
- Tested by: `test_case_3`
- Coverage: 100%
- Status: ✓ Complete

### Algorithm Invariant: [Description]
- Tested by: `property_test_invariant`
- Coverage: 100% (property-based, 10,000+ cases)
- Status: ✓ Complete
```

#### 4.2.4 Variant Coverage Matrix

**When Required**: Project has Feature "Multiple Variants/Implementations" (§2.1)

**File**: `Variant-Coverage-Matrix.md` (project root)

**Purpose**: Ensure ALL variants tested equivalently

**Format**:

```markdown
## Module: [MODULE_NAME]

### Variants Identified
1. Variant A (e.g., TAS Lock)
2. Variant B (e.g., Ticket Lock)
3. Variant C (e.g., MCS Lock)
4. Variant D (e.g., CLH Lock)
5. Variant E (e.g., Anderson Lock)

### Test Coverage Matrix

| Test Case | Variant A | Variant B | Variant C | Variant D | Variant E | Status |
|-----------|-----------|-----------|-----------|-----------|-----------|--------|
| Basic lock/unlock | ✓ | ✓ | ✓ | ✓ | ✓ | Complete |
| Try-lock success | ✓ | ✓ | ✓ | ✓ | ✓ | Complete |
| Try-lock failure | ✓ | ✓ | ✓ | ✓ | ✓ | Complete |
| Multi-threaded (2) | ✓ | ✓ | ✓ | ✓ | ✓ | Complete |
| Multi-threaded (4) | ✓ | ✓ | ✓ | ✓ | ✓ | Complete |
| Multi-threaded (8) | ✓ | ✓ | ✓ | ✓ | ✓ | Complete |
| Multi-threaded (16) | ✓ | ✓ | ✓ | ✓ | ✓ | Complete |
| High contention | ✓ | ✓ | ✓ | ✓ | ✓ | Complete |
| Stress test | ✓ | ✓ | ✓ | ✓ | ✓ | Complete |
| Performance bench | ✓ | ✓ | ✓ | ✓ | ✓ | Complete |

### Test Count Summary
- Total test categories: 10
- Variants: 5
- Expected tests: 10 × 5 = 50
- Actual tests: 50
- Coverage: 100% ✓

### Gaps Identified
None - all variants have complete test coverage.
```

**Acceptance Criteria**:
- Every cell in matrix is ✓
- Test count matches: (test categories) × (variants)
- No gaps or exceptions
- CI enforces this (fails if matrix incomplete)

#### 4.2.5 Parametric Operations Matrix

**When Required**: Project has Feature "Parametric Operations" (§2.1)

**File**: `Parametric-Coverage-Matrix.md` (project root)

**Purpose**: Ensure ALL data types/orderings tested for each operation

**Format**:

```markdown
## Module: Atomic Operations

### Data Types Supported
1. u8
2. u16
3. u32
4. u64
5. usize
6. *const T (pointer)

### Operations Implemented
1. load
2. store
3. swap
4. compare_exchange (cas)
5. fetch_add
6. fetch_sub
7. fetch_and
8. fetch_or
9. fetch_xor
10. fetch_max
11. fetch_min
... (list ALL operations)

### Operation × Data Type Coverage Matrix

| Operation | u8 | u16 | u32 | u64 | usize | ptr | Test Count | Status |
|-----------|----|----|-----|-----|-------|-----|------------|--------|
| load | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | 6 | Complete |
| store | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | 6 | Complete |
| swap | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | 6 | Complete |
| cas | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | 6 | Complete |
| fetch_add | ✓ | ✓ | ✓ | ✓ | ✓ | N/A | 5 | Complete |
| fetch_sub | ✓ | ✓ | ✓ | ✓ | ✓ | N/A | 5 | Complete |
| fetch_and | ✓ | ✓ | ✓ | ✓ | ✓ | N/A | 5 | Complete |
| fetch_or | ✓ | ✓ | ✓ | ✓ | ✓ | N/A | 5 | Complete |
| fetch_xor | ✓ | ✓ | ✓ | ✓ | ✓ | N/A | 5 | Complete |

### Memory Ordering Coverage

For each operation above, test with ALL orderings:

| Operation | Relaxed | Acquire | Release | AcqRel | SeqCst | Status |
|-----------|---------|---------|---------|--------|--------|--------|
| load | ✓ | ✓ | N/A | N/A | ✓ | Complete |
| store | ✓ | N/A | ✓ | N/A | ✓ | Complete |
| swap | ✓ | ✓ | ✓ | ✓ | ✓ | Complete |
| cas | ✓ | ✓ | ✓ | ✓ | ✓ | Complete |
| fetch_add | ✓ | ✓ | ✓ | ✓ | ✓ | Complete |
... (continue for all operations)

### Total Test Count
- Operations: 15
- Data types (average): 5.5
- Memory orderings (average): 4
- **Minimum expected tests**: 15 × 5.5 × 4 = 330 tests
- **Actual tests**: 330+
- **Coverage**: 100% ✓
```

**Acceptance Criteria**:
- Every (operation × data type) cell is ✓ or N/A (with justification)
- Every (operation × ordering) cell is ✓ or N/A (with justification)
- Actual test count ≥ minimum expected
- CI enforces completeness

---

## 5. Testing Levels

This section defines the different levels of testing required.

### 5.1 Unit Testing

**Scope**: Individual functions, methods, and small components in isolation

**Coverage Requirements**:
- 100% of public API functions
- 100% of unsafe code blocks
- 100% of error paths
- 100% of conditional branches
- All state transitions
- All boundary conditions

**Test Categories**:

#### 5.1.1 Basic Functionality Tests
Verify correct behavior under normal conditions.

**Template**:
```
TEST basic_functionality_[operation_name]
    GIVEN: [Initial conditions]
    WHEN: [Operation performed]
    THEN: [Expected outcome]
    
    Example assertions:
    - Return values match specifications
    - State transitions work correctly
    - Invariants maintained
    - Expected side effects occur
END TEST
```

#### 5.1.2 Edge Case Tests
Test boundary and extreme conditions.

**Required Edge Cases**:
- Empty inputs
- Single element
- Maximum values
- Minimum values
- Null/invalid pointers (if applicable)
- Overflow/underflow conditions
- Wraparound behavior

**Template**:
```
TEST edge_case_[scenario_name]
    GIVEN: [Boundary condition]
    WHEN: [Operation performed]
    THEN: [Expected boundary behavior]
END TEST
```

#### 5.1.3 Error Condition Tests
Test error handling and recovery.

**Required Tests**:
- Invalid inputs rejected gracefully
- Error codes correct
- State remains consistent after errors
- Resources properly cleaned up on error
- Error messages clear and actionable

**Template**:
```
TEST error_handling_[error_type]
    GIVEN: [Conditions that trigger error]
    WHEN: [Operation attempted]
    THEN: 
        - Error detected
        - Correct error code returned
        - State unchanged or safely modified
        - Resources cleaned up
END TEST
```

#### 5.1.4 Algorithmic Correctness Tests
Verify algorithm-specific properties.

For concurrent algorithms:
- Lock-free progress guarantees
- FIFO/LIFO ordering maintained
- Memory ordering constraints satisfied
- ABA problem prevented
- Linearizability preserved

**Template**:
```
TEST algorithm_property_[property_name]
    GIVEN: [Test setup]
    WHEN: [Algorithm executed]
    THEN: [Property verified]
    
    Examples:
    - Stack maintains LIFO order
    - Queue maintains FIFO order
    - Lock provides mutual exclusion
    - Memory is eventually reclaimed
END TEST
```

### 5.2 Concurrency Model Checking

**When Required**: Feature "Concurrency Primitives" detected (§2.1)

**Tool**: Loom (Rust) or similar model checker

**Purpose**: Exhaustively explore thread interleavings to find race conditions

**Scope**:
- 100% of concurrent primitives
- 100% of lock-free data structures
- 100% of synchronization mechanisms
- All memory orderings
- All possible CAS outcomes

**Test Structure**:
```
MODEL_CHECK [operation_name]
    CONFIGURE:
        max_threads = [2-4 typical]
        max_iterations = [1-3 typical]
        max_preemptions = [2-5 typical]
    
    SETUP:
        [Initialize shared state]
    
    THREADS:
        [Define concurrent thread behavior]
    
    VERIFY:
        [Check invariants hold under ALL interleavings]
END MODEL_CHECK
```

**Example**:
```rust
#[test]
fn loom_spinlock_mutual_exclusion() {
    loom::model(|| {
        let lock = Arc::new(TicketLock::new());
        let counter = Arc::new(AtomicUsize::new(0));
        
        let threads: Vec<_> = (0..2).map(|_| {
            let lock = lock.clone();
            let counter = counter.clone();
            
            loom::thread::spawn(move || {
                for _ in 0..2 {
                    lock.lock();
                    let val = counter.load(Ordering::SeqCst);
                    counter.store(val + 1, Ordering::SeqCst);
                    lock.unlock();
                }
            })
        }).collect();
        
        for thread in threads {
            thread.join().unwrap();
        }
        
        assert_eq!(counter.load(Ordering::SeqCst), 4);
    });
}
```

**Coverage**:
- All possible thread interleavings
- All memory ordering combinations
- All CAS success/failure paths
- All race condition scenarios
- All deadlock possibilities (for locks)

### 5.3 Integration Testing

**Scope**: Interactions between modules and components

**Focus Areas**:
- Module integration
- Data flow between components
- API contracts
- End-to-end workflows
- Error propagation
- Resource sharing
- State consistency

**Test Scenarios**:

#### 5.3.1 Cross-Module Integration
Test how modules work together.

**Template**:
```
TEST cross_module_[modules_involved]
    GIVEN: [Multiple modules initialized]
    WHEN: [Modules interact]
    THEN: [Correct integration behavior]
    
    Verify:
    - Data flows correctly between modules
    - Shared resources managed properly
    - State remains consistent
    - No resource leaks
END TEST
```

#### 5.3.2 Multi-Component Workflow
Test complete operation sequences.

**Template**:
```
TEST workflow_[workflow_name]
    GIVEN: [System setup]
    WHEN: [Complete workflow executed]
    THEN: [End-to-end correctness]
    
    Example: Producer-consumer workflow
    - Producers push to queue
    - Consumers pop from queue
    - Verify all items processed
    - Verify correct ordering
    - Verify no data loss
END TEST
```

#### 5.3.3 Strategy Integration
Test how optimization strategies integrate with core functionality.

**Example**: Backoff strategy with locks
```
TEST backoff_integration_with_locks
    GIVEN: Lock with backoff strategy
    WHEN: High contention scenario
    THEN: 
        - Lock still provides mutual exclusion
        - Backoff reduces contention overhead
        - No deadlocks
        - Correct operation under load
END TEST
```

### 5.4 Property-Based Testing

**Purpose**: Verify algorithmic properties hold for wide range of inputs

**Coverage**:
- Data structure invariants
- Synchronization properties
- Memory reclamation properties
- Linearizability properties

**Property Definition Template**:
```
PROPERTY [property_name]
    INPUT: [Description of input space]
    STRATEGY: [How inputs generated]
    
    SETUP: [Test setup]
    EXECUTE: [Operations to perform]
    VERIFY: [Property that must hold]
    
    PARAMETERS:
        - Input range: [min, max]
        - Number of test cases: [typically 1000-10000]
        - Shrinking enabled: [yes/no]
END PROPERTY
```

**Example - LIFO Property**:
```rust
#[test]
fn property_stack_lifo_order() {
    proptest!(|(values: Vec<u32>)| {
        let stack = Stack::new();
        let handle = collector.register();
        
        // Push all values
        for &value in &values {
            stack.push(value);
        }
        
        // Pop must be in exact reverse order
        for &value in values.iter().rev() {
            let popped = stack.pop(&handle);
            prop_assert_eq!(popped, Some(value));
        }
        
        // Stack must be empty
        prop_assert_eq!(stack.pop(&handle), None);
    });
}
```

### 5.5 Stress Testing

**Purpose**: Validate behavior under sustained high load and extreme conditions

**Duration**: Extended periods (minutes to hours)

**Scenarios**:
- High contention
- Sustained load
- Pathological workloads
- Memory pressure

**Test Template**:
```
STRESS_TEST [scenario_name]
    DURATION: [time]
    THREADS: [count]
    
    SETUP: [Initialize system]
    
    WORKLOAD: [Description of load pattern]
    
    MONITORING:
        - Throughput
        - Latency
        - Memory usage
        - Error rate
    
    ACCEPTANCE:
        - No crashes
        - No deadlocks
        - No livelocks
        - No memory leaks
        - Performance within bounds
END STRESS_TEST
```

**Example**:
```rust
#[test]
#[ignore] // Long-running
fn stress_lock_extreme_contention() {
    const DURATION: Duration = Duration::from_secs(60);
    const THREADS: usize = 64;
    
    let lock = Arc::new(TicketLock::new());
    let counter = Arc::new(AtomicUsize::new(0));
    let done = Arc::new(AtomicBool::new(false));
    
    let handles: Vec<_> = (0..THREADS)
        .map(|_| {
            let lock = lock.clone();
            let counter = counter.clone();
            let done = done.clone();
            
            thread::spawn(move || {
                let mut local_count = 0;
                while !done.load(Ordering::Relaxed) {
                    lock.lock();
                    counter.fetch_add(1, Ordering::Relaxed);
                    lock.unlock();
                    local_count += 1;
                }
                local_count
            })
        })
        .collect();
    
    thread::sleep(DURATION);
    done.store(true, Ordering::Relaxed);
    
    let total: usize = handles.into_iter()
        .map(|h| h.join().unwrap())
        .sum();
    
    assert_eq!(counter.load(Ordering::SeqCst), total);
    // Additional checks: throughput, no crashes, etc.
}
```

### 5.6 Performance Testing

**Purpose**: Validate performance requirements and detect regressions

**Benchmark Categories**:
- Throughput
- Latency percentiles
- Scalability
- Memory overhead

**Benchmark Template**:
```
BENCHMARK [benchmark_name]
    CONFIGURATIONS:
        [List all configuration dimensions]
    
    FOR EACH configuration:
        WARMUP: [warmup iterations]
        MEASURE: [measurement iterations]
        
        RECORD:
            - Throughput (ops/sec)
            - Latency (p50, p95, p99, p999)
            - Memory usage
            - CPU usage
        
        COMPARE:
            - Against baseline
            - Flag regressions >5%
END BENCHMARK
```

**Example**:
```rust
fn criterion_spinlock_throughput(c: &mut Criterion) {
    let mut group = c.benchmark_group("spinlock_throughput");
    
    for lock_type in &["TAS", "Ticket", "MCS", "CLH"] {
        for threads in &[1, 2, 4, 8, 16] {
            group.bench_function(
                &format!("{}_{}threads", lock_type, threads),
                |b| {
                    let lock = create_lock(lock_type);
                    let counter = Arc::new(AtomicUsize::new(0));
                    
                    b.iter(|| {
                        // Benchmark logic
                    });
                }
            );
        }
    }
    
    group.finish();
}
```

### 5.7 Regression Testing

**Purpose**: Ensure fixed bugs don't reappear

**Policy**:
- Every bug gets a permanent test
- Run regression suite on **every** commit
- Never remove regression tests

**Regression Test Template**:
```
TEST regression_issue_[number]_[brief_description]
    // Bug: [Description of bug]
    // Discovered: [Date]
    // Fixed: [Date]
    // Symptom: [What went wrong]
    
    GIVEN: [Conditions that triggered bug]
    WHEN: [Operations that exposed bug]
    THEN: [Verify bug is fixed]
    
    // Specific verification that bug doesn't reoccur
END TEST
```

**Example**:
```rust
#[test]
fn regression_issue_42_mcs_unlock_race() {
    // Bug: MCS unlock could race with new lock acquisition
    // Discovered: 2025-11-15
    // Fixed: 2025-11-16
    // Symptom: Occasionally hung threads under high contention
    
    let lock = Arc::new(McsLock::new());
    let success = Arc::new(AtomicUsize::new(0));
    
    let handles: Vec<_> = (0..100)
        .map(|_| {
            let lock = lock.clone();
            let success = success.clone();
            
            thread::spawn(move || {
                let mut node = McsNode::new();
                for _ in 0..1000 {
                    lock.lock(&mut node);
                    success.fetch_add(1, Ordering::Relaxed);
                    lock.unlock(&mut node);
                }
            })
        })
        .collect();
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    assert_eq!(success.load(Ordering::SeqCst), 100_000);
}
```

---

## 6. Domain-Specific Requirements

Based on feature detection (§2), apply domain-specific requirements.

### 6.1 Domain-Specific Test Requirements

#### 6.1.1 Concurrency Primitives

**Applies When**: Feature "Concurrency Primitives" detected

**Requirements**:

**1. Data Width Coverage**
- [ ] Test every atomic operation across ALL supported widths
- [ ] Test every operation with ALL memory orderings
- [ ] Use parametric operations matrix (§4.2.5)

**2. Thread Configuration Coverage**
- [ ] Single thread (baseline)
- [ ] 2 threads (low contention)
- [ ] 4 threads (moderate contention)
- [ ] 8 threads (high contention)
- [ ] 16+ threads (extreme contention)
- [ ] Pathological: all threads synchronized

**3. Contention Pattern Coverage**
- [ ] No contention (independent operations)
- [ ] Low contention (occasional overlap)
- [ ] High contention (frequent conflicts)
- [ ] Pathological contention (worst case)

**4. Memory Ordering Verification**
- [ ] Verify sequential consistency when required
- [ ] Verify acquire/release semantics
- [ ] Verify relaxed ordering allows reordering
- [ ] Use model checking to verify orderings

**5. Lock-Specific Tests**
- [ ] Mutual exclusion (critical section protection)
- [ ] Fairness (if applicable)
- [ ] No deadlock
- [ ] No livelock
- [ ] No priority inversion (if priority-aware)

#### 6.1.2 Memory Reclamation Systems

**Applies When**: Feature "Memory Reclamation" detected

**Requirements**:

**1. Operation Coverage**
- [ ] begin/end (pin/unpin)
- [ ] defer (add to reclamation queue)
- [ ] synchronize (wait for safe epoch)
- [ ] barrier (ensure point-in-time consistency)
- [ ] call (defer with callback)
- [ ] poll (check for reclaimable objects)

**2. Scenario Coverage**
- [ ] Normal operation (begin → defer → end → reclaim)
- [ ] Nested pins (multiple begin/end pairs)
- [ ] Synchronization timing (early, late, concurrent)
- [ ] Barrier semantics
- [ ] Callback execution (for `call` operation)
- [ ] Poll behavior (when objects are/aren't reclaimable)

**3. Edge Cases**
- [ ] Zero pins
- [ ] Single pin
- [ ] Many nested pins (100+)
- [ ] Deferred items never reclaimed (leaked pins)
- [ ] Massive garbage list (1M+ items)
- [ ] Epoch counter overflow/wraparound

**4. Stress Scenarios**
- [ ] Sustained high load (minutes to hours)
- [ ] Burst patterns (alternating full/empty)
- [ ] Memory pressure (low available memory)
- [ ] Pathological: all threads deferring, no reclamation

**5. Verification**
- [ ] No memory leaks (all deferred items eventually reclaimed)
- [ ] No use-after-free
- [ ] No double-free
- [ ] Memory usage bounded
- [ ] Reclamation eventually happens

#### 6.1.3 Lock-Free Data Structures

**Applies When**: Feature "Lock-Free Data Structures" detected

**Requirements**:

**1. Linearizability**
- [ ] All operations linearizable
- [ ] History recording of operations
- [ ] Verification of linearization points
- [ ] Use model checking when possible

**2. Progress Guarantees**
- [ ] Lock-free: At least one thread makes progress
- [ ] Wait-free: All threads make progress (if claimed)
- [ ] Obstruction-free: Progress when alone (if claimed)
- [ ] Test under contention to verify

**3. ABA Problem Prevention**
- [ ] If using CAS, verify ABA protection
- [ ] Test with value recycling
- [ ] Test with pointer recycling
- [ ] Use generation counters or hazard pointers

**4. Ordering Properties**
- [ ] FIFO: dequeue order matches enqueue order
- [ ] LIFO: pop order matches push order (reversed)
- [ ] Priority: higher priority items first
- [ ] Test with property-based testing

**5. Consistency**
- [ ] Size remains consistent
- [ ] Empty/full state correct
- [ ] Iterator consistency (if applicable)
- [ ] No lost items
- [ ] No duplicated items

#### 6.1.4 Unsafe Code

**Applies When**: Project contains `unsafe` blocks

**Requirements**:

**1. Coverage**
- [ ] 100% of unsafe blocks tested
- [ ] All unsafe operations verified safe
- [ ] All safety invariants documented
- [ ] All safety invariants tested

**2. Miri Verification**
- [ ] All unsafe code passes Miri
- [ ] No undefined behavior
- [ ] No invalid pointer dereferences
- [ ] No data races
- [ ] No memory leaks in unsafe sections

**3. Safety Documentation**
- [ ] Every unsafe block has safety comment
- [ ] Safety comment explains why it's safe
- [ ] Preconditions documented
- [ ] Invariants maintained documented

**4. Alternative Safe Implementation**
- [ ] Consider if safe alternative exists
- [ ] Document why unsafe is necessary
- [ ] Minimize unsafe scope

**Example Safety Documentation**:
```rust
unsafe {
    // SAFETY: Pointer is valid because:
    // 1. Allocated by Box::into_raw()
    // 2. Has not been freed (protected by epoch)
    // 3. Type T is properly initialized
    // 4. We own exclusive access (no concurrent modifications)
    let value = ptr::read(data_ptr);
    value
}
```

#### 6.1.5 Parsers and Compilers

**Applies When**: Feature "Parser/Compiler" detected

**Requirements**:

**1. Grammar Coverage**
- [ ] Every production rule tested
- [ ] Every token type tested
- [ ] Every syntax construct tested
- [ ] Valid and invalid syntax

**2. Input Coverage**
- [ ] Empty input
- [ ] Single token
- [ ] Minimal valid program
- [ ] Complex nested structures
- [ ] Maximum nesting depth
- [ ] Boundary cases (max identifiers, max literals, etc.)

**3. Error Recovery**
- [ ] Error detection for invalid syntax
- [ ] Error messages are clear
- [ ] Parser recovers and continues
- [ ] Multiple errors detected in one pass

**4. Edge Cases**
- [ ] Very long identifiers
- [ ] Deeply nested expressions
- [ ] Large number literals
- [ ] Unicode edge cases
- [ ] Whitespace edge cases

#### 6.1.6 Cryptographic Code

**Applies When**: Feature "Cryptographic Operations" detected

**Requirements**:

**1. Test Vector Validation**
- [ ] All standard test vectors pass
- [ ] Test vectors from specifications
- [ ] Test vectors from reference implementations
- [ ] Known-answer tests (KAT)

**2. Property Testing**
- [ ] Encryption/decryption round-trip
- [ ] Hash collision resistance (to extent testable)
- [ ] Signature verification
- [ ] Key derivation consistency

**3. Side-Channel Resistance**
- [ ] Constant-time operation verification
- [ ] No data-dependent branches in critical paths
- [ ] No data-dependent memory access patterns
- [ ] Timing attack resistance tests

**4. Constant-Time Verification**
- [ ] Use timing-testing tools
- [ ] Verify operations take same time regardless of input
- [ ] Test with different input patterns

**5. Failure Cases**
- [ ] Invalid keys rejected
- [ ] Tampering detected
- [ ] Wrong keys fail verification
- [ ] Malformed input handled

---

## 7. Port Projects: Reference Analysis

**Applies When**: Feature "Port of Existing Library" detected (§2.1)

**Purpose**: When porting an existing library, systematically analyze and conform to original test suite.

### 7.1 Reference Test Inventory

**Required Documentation**: `Port-Analysis.md` (project root)

#### Step 1: Catalog Original Tests

```markdown
## Reference Library: [NAME]
**Version**: [version being ported]
**URL**: [repository URL]

### Test File Inventory

#### Directory Structure
```
original-repo/
├── tests/
│   ├── unit/
│   ├── integration/
│   └── regression/
├── benchmarks/
└── validation/
```

#### Test Counts by Category

| Category | Directory | File Count | Test Count | Purpose |
|----------|-----------|------------|------------|---------|
| Unit Tests | tests/unit/ | 45 | 523 | Basic functionality |
| Integration | tests/integration/ | 23 | 184 | Cross-module |
| Regression | tests/regression/ | 15 | 227 | Bug prevention |
| Validation | validation/ | 30 | 412 | Conformance |
| Benchmarks | benchmarks/ | 12 | 43 | Performance |
| **TOTAL** | | **125** | **1,389** | |
```

#### Step 2: Categorize Test Types

```markdown
### Test Type Analysis

#### By Functionality
- Atomic operations: 115 tests
- Synchronization primitives: 87 tests
- Memory reclamation: 34 tests
- Data structures: 98 tests
- Performance: 43 tests
- Other: 1,012 tests

#### By Methodology
- Unit tests: 523
- Multi-threaded: 184
- Stress tests: 43
- Property-based: 0 (not in original)
- Model checking: 0 (not in original)
```

### 7.2 Test Conformance Analysis

#### Step 1: Identify Test Dimensions in Original

```markdown
### Test Dimensions Identified in Original

#### Atomic Operations
**Dimensions Found**:
- Operations: 15 types (load, store, add, sub, cas, swap, etc.)
- Data widths: 6 types (u8, u16, u32, u64, usize, ptr)
- **Matrix**: 15 × 6 = 90 test files

**Test Files**:
- ck_pr/validate/ck_pr_load.c
- ck_pr/validate/ck_pr_store.c
- ck_pr/validate/ck_pr_add.c
- ... (list all 23 test files)

**Pattern**: Each operation has one test file that tests all data widths

#### Spinlocks
**Dimensions Found**:
- Variants: 10 types (TAS, Ticket, MCS, CLH, Anderson, etc.)
- Operations: 3 per variant (lock, unlock, trylock)
- **Pattern**: Each variant has separate validation and benchmark

**Test Files**:
- ck_spinlock/validate/ck_tas.c
- ck_spinlock/validate/ck_ticket.c
- ... (list all variants)

#### Memory Reclamation
**Scenarios Found**:
- synchronize: Wait for safe epoch
- call: Defer with callback
- poll: Check reclaimable
- section: Section-based protection
- section_2: Advanced sections
- torture: Extreme stress

**Test Files**:
- ck_epoch/validate/ck_epoch_synchronize.c
- ck_epoch/validate/ck_epoch_call.c
- ... (list all scenarios)
```

#### Step 2: Compare with Current Implementation

```markdown
### Conformance Matrix

#### Atomic Operations

| Original Test File | Purpose | Ported? | Location | Status |
|--------------------|---------|---------|----------|--------|
| ck_pr_load.c | Load operations | ✓ | src/pr.rs:tests | Complete |
| ck_pr_store.c | Store operations | ✓ | src/pr.rs:tests | Complete |
| ck_pr_add.c | Addition | ✗ | N/A | MISSING |
| ck_pr_sub.c | Subtraction | ✗ | N/A | MISSING |
| ck_pr_cas.c | Compare-and-swap | ✓ | src/pr.rs:tests | Complete |
| ck_pr_swap.c | Swap | ✓ | src/pr.rs:tests | Complete |
| ck_pr_and.c | Bitwise AND | ✗ | N/A | MISSING |
| ck_pr_or.c | Bitwise OR | ✗ | N/A | MISSING |
| ck_pr_xor.c | Bitwise XOR | ✗ | N/A | MISSING |
| ... | ... | ... | ... | ... |

**Summary**:
- Original tests: 23
- Ported: 8
- Missing: 15
- Coverage: 35% ⚠️

#### Spinlocks

| Variant | Original Validation | Original Benchmark | Ported Validation | Ported Benchmark | Status |
|---------|--------------------|--------------------|------------------|------------------|--------|
| TAS | ✓ | ✓ | ✓ | ✓ | Complete |
| Ticket | ✓ | ✓ | ✓ | ✓ | Complete |
| MCS | ✓ | ✓ | ✓ | ✓ | Complete |
| CLH | ✓ | ✓ | ✓ | ✓ | Complete |
| Anderson | ✓ | ✓ | ✗ | ✗ | MISSING |
| FAS | ✓ | ✓ | ✗ | ✗ | MISSING |
| ... | ... | ... | ... | ... | ... |

**Summary**:
- Original variants: 10
- Ported: 4
- Missing: 6
- Coverage: 40% ⚠️

#### Memory Reclamation

| Scenario | Original Test | Ported? | Location | Status |
|----------|---------------|---------|----------|--------|
| synchronize | ✓ | ✓ | tests/epoch_sync.rs | Complete |
| call | ✓ | ✗ | N/A | MISSING |
| poll | ✓ | ✗ | N/A | MISSING |
| section | ✓ | ✗ | N/A | MISSING |
| section_2 | ✓ | ✗ | N/A | MISSING |
| torture | ✓ | ✗ | N/A | MISSING |

**Summary**:
- Original scenarios: 7
- Ported: 3
- Missing: 4
- Coverage: 43% ⚠️
```

### 7.3 Gap Identification and Closure

#### Step 1: Document Gaps

```markdown
### Identified Gaps

#### Critical Gaps (Must Fix Before Release)

1. **Atomic Operations - Missing 15 operations**
   - Impact: Core functionality not fully tested
   - Affected operations: add, sub, and, or, xor, btc, btr, bts, faa, fas, inc, dec, etc.
   - Plan: Port all 15 operation test files
   - Timeline: Sprint 1

2. **Spinlocks - Missing 6 variants**
   - Impact: Incomplete variant coverage
   - Missing: Anderson, FAS, DEC, HCL, TicketPB, Linux
   - Plan: Implement missing variants first, then port tests
   - Timeline: Sprint 2-3

3. **Memory Reclamation - Missing 4 scenarios**
   - Impact: Edge cases not validated
   - Missing: call, poll, section, section_2, torture
   - Plan: Port all scenario tests
   - Timeline: Sprint 1

#### Medium Priority Gaps

4. **Benchmark Coverage**
   - Original has 43 benchmarks
   - Port has 12 benchmarks
   - Plan: Port remaining performance tests
   - Timeline: Sprint 4

#### Low Priority Gaps

5. **Platform-Specific Tests**
   - Original tests on 12 platforms
   - Port tests on 4 platforms
   - Plan: Add CI for missing platforms
   - Timeline: Sprint 5
```

#### Step 2: Create Closure Plan

```markdown
### Gap Closure Plan

#### Sprint 1: Critical Atomic Operations
**Week 1-2**: Port atomic operation tests
- [ ] ck_pr_add.c → tests/atomic_add.rs
- [ ] ck_pr_sub.c → tests/atomic_sub.rs
- [ ] ck_pr_and.c → tests/atomic_and.rs
- [ ] ck_pr_or.c → tests/atomic_or.rs
- [ ] ck_pr_xor.c → tests/atomic_xor.rs
- [ ] ... (list all 15)

**Acceptance**: All 15 atomic operation tests ported and passing

#### Sprint 1: Critical Memory Reclamation
**Week 3-4**: Port memory reclamation edge cases
- [ ] ck_epoch_call.c → tests/epoch_call.rs
- [ ] ck_epoch_poll.c → tests/epoch_poll.rs
- [ ] ck_epoch_section.c → tests/epoch_section.rs
- [ ] ck_epoch_section_2.c → tests/epoch_section_2.rs
- [ ] ck_epoch_torture.c → tests/epoch_torture.rs

**Acceptance**: All 5 epoch scenario tests ported and passing

#### Sprint 2-3: Spinlock Variants
**Implementation + Testing**
- [ ] Implement Anderson lock
- [ ] Port validation tests
- [ ] Port benchmark tests
- [ ] Repeat for FAS, DEC, HCLH, TicketPB, Linux

**Acceptance**: All 6 missing variants implemented and tested

#### Sprint 4: Performance Testing
**Benchmark Porting**
- [ ] Port throughput benchmarks
- [ ] Port latency benchmarks
- [ ] Port scalability benchmarks

**Acceptance**: Benchmark coverage matches original

#### Sprint 5: Platform Coverage
**CI Infrastructure**
- [ ] Add FreeBSD CI
- [ ] Add OpenBSD CI
- [ ] Add ARM32 CI
- [ ] Add MIPS CI
- [ ] ... (additional platforms)

**Acceptance**: Platform coverage matches original
```

#### Step 3: Track Progress

```markdown
### Conformance Tracking

#### Overall Statistics
- Original test count: 1,389
- Ported test count: 523 (37.6%)
- Missing test count: 866 (62.4%)
- Target completion: Sprint 5

#### Progress by Category

| Category | Original | Ported | Missing | % Complete |
|----------|----------|--------|---------|------------|
| Atomic Ops | 115 | 40 | 75 | 35% |
| Spinlocks | 87 | 35 | 52 | 40% |
| Epoch | 34 | 15 | 19 | 44% |
| Data Structures | 98 | 45 | 53 | 46% |
| Benchmarks | 43 | 12 | 31 | 28% |
| Other | 1,012 | 376 | 636 | 37% |

#### Sprint Progress
- Sprint 1 Target: 150 tests ported (critical gaps)
- Sprint 2-3 Target: 250 tests ported (variants)
- Sprint 4 Target: 31 benchmarks ported
- Sprint 5 Target: Complete (100% conformance)
```

### 7.4 Additional Value Beyond Reference

**Not Just Porting - Also Adding**:

Port projects should not just copy the original, but also add value where Rust enables better testing:

```markdown
### Testing Enhancements in Port

#### What Original Has
- Basic multi-threaded tests
- Manual timing measurements
- Platform-specific atomic implementations

#### What Port Adds (Rust-Specific)
- [x] Loom model checking (exhaustive interleaving exploration)
  - Not possible in C
  - Finds race conditions original can't detect
  
- [x] Miri undefined behavior detection
  - Catches UB that original accepts
  - Memory safety verification
  
- [x] Property-based testing with proptest
  - Tests with 10,000+ random inputs
  - Automatic shrinking to minimal failing case
  
- [x] Criterion benchmarks
  - Statistical analysis
  - Regression detection
  - Performance tracking over time
  
- [x] Type-safe testing
  - Generic tests work for all types
  - Compiler ensures correctness

#### Conformance Strategy
**Minimum Requirement**: Match or exceed original test coverage
**Target**: Original coverage + Rust-specific enhancements
```

---

## 8. Test Organization

### 8.1 Directory Structure

```
project-root/
├── src/
│   ├── module1.rs          # Unit tests in #[cfg(test)] modules
│   ├── module2.rs
│   └── lib.rs
├── tests/                  # Integration tests
│   ├── integration_*.rs
│   ├── loom_*.rs          # Concurrency model checking
│   ├── stress_*.rs        # Long-running stress tests
│   ├── property_*.rs      # Property-based tests
│   └── regression_*.rs    # Regression tests
├── benches/               # Performance benchmarks
│   ├── throughput.rs
│   ├── latency.rs
│   └── scalability.rs
├── regressions/           # Port-specific: CK conformance tests
│   ├── common/
│   │   └── mod.rs
│   ├── maps are deterministic (or documented otherwise)

**Test Approach**:
```rust
#[test]
fn deterministic_output() {
    let input = create_test_input();
    let result1 = process(&input);
    let result2 = process(&input);
    assert_eq!(result1, result2, "Same input must produce same output");
}
```

---

## 5.16 Mutation Testing

**Purpose**: Verify that tests actually detect bugs, not just execute code

**Problem Solved**: High line coverage doesn't guarantee tests catch bugs. Mutation testing injects faults and verifies tests fail.

**Tools**: cargo-mutants, mutagen

**Applies When**: Always. Every test suite benefits from mutation testing validation.

**N/A Justification**: Never N/A. If tests exist, they should catch mutations.

**How It Works**:
1. Tool mutates source code (e.g., `+` → `-`, `<` → `<=`, `true` → `false`)
2. Tests run against mutated code
3. If tests still pass, the "mutant survives" = test gap identified
4. Goal: Kill all mutants (tests catch all injected bugs)

**Execution**:
```bash
# Run mutation testing
cargo mutants

# Target specific module
cargo mutants --package ck-rust -- src/pr.rs
```

**Metrics**:
| Metric | Target | Meaning |
|--------|--------|---------|
| Mutation Score | >90% | Percentage of mutants killed |
| Survived Mutants | 0 ideal | Bugs tests would miss |
| Timeout Mutants | <5% | Infinite loops (often acceptable) |

**CI Requirements**:
- [ ] Mutation testing on critical modules (concurrency, safety-critical)
- [ ] Survived mutants require justification or new tests
- [ ] Track mutation score over time (should not decrease)

**Example Output Analysis**:
```
MISSED: src/pr.rs:142 - replaced `<` with `<=` in bounds check
ACTION: Add test for boundary condition
```

---

## 5.17 Static Analysis

**Purpose**: Catch bugs, anti-patterns, and security issues without running code

**Tools**: clippy, rust-analyzer, cargo-audit, cargo-deny, custom lints

**Applies When**: Always. All Rust code benefits from static analysis.

**N/A Justification**: Never N/A.

**Required Analysis Levels**:

**1. Clippy (Lint Analysis)**:
```bash
# Strict clippy - deny all warnings
cargo clippy -- -D warnings

# Pedantic mode for higher standards
cargo clippy -- -W clippy::pedantic

# Nursery lints for emerging best practices  
cargo clippy -- -W clippy::nursery
```

**2. Security Audit**:
```bash
# Check dependencies for known vulnerabilities
cargo audit

# Comprehensive dependency policy
cargo deny check
```

**3. Unsafe Code Analysis**:
```bash
# Count and track unsafe usage
cargo geiger

# Verify unsafe blocks are minimized
```

**CI Requirements**:
- [ ] `cargo clippy -- -D warnings` on every PR (zero warnings policy)
- [ ] `cargo audit` on every PR (no known vulnerabilities)
- [ ] `cargo deny` for license and dependency policy
- [ ] Unsafe code count tracked and justified

**Clippy Configuration** (`clippy.toml`):
```toml
# Project-wide clippy configuration
warn = [
    "clippy::all",
    "clippy::pedantic",
    "clippy::nursery",
]
allow = [
    # Explicit exceptions with justification
]
```

---

## 5.18 API Compatibility Testing

**Purpose**: Detect breaking changes and ensure semantic versioning compliance

**Tools**: cargo-semver-checks, cargo-public-api

**Applies When**: Library has public API consumed by external users

**N/A Justification**: Only for internal-only code with no external consumers

**Requirements**:

**1. Semver Compliance**:
```bash
# Check for breaking changes vs published version
cargo semver-checks check-release
```

**2. Public API Tracking**:
```bash
# Generate API surface
cargo public-api

# Diff against baseline
cargo public-api diff
```

**3. Deprecation Policy**:
- [ ] Deprecated items marked with `#[deprecated]`
- [ ] Deprecation includes migration path
- [ ] Minimum one release cycle before removal

**CI Requirements**:
- [ ] Semver check on every PR to main
- [ ] Breaking changes require major version bump
- [ ] API diff reviewed for unintended changes

**Breaking Change Categories**:
| Change Type | Semver Impact | Example |
|-------------|---------------|---------|
| Remove public item | MAJOR | Delete `pub fn foo()` |
| Change signature | MAJOR | Change return type |
| Add required parameter | MAJOR | New non-default param |
| Weaken bounds | Minor | `T: Clone` → `T` |
| Add with defaults | Minor | New method with default |
| Bug fix | Patch | Fix incorrect behavior |

---

## 5.19 Formal Verification

**Purpose**: Mathematically prove correctness of critical algorithms

**Tools**: TLA+, Kani, Creusot, Prusti

**Applies When**: 
- Lock-free algorithms
- Memory reclamation schemes
- Safety-critical code paths
- Any code where "probably correct" is insufficient

**N/A Justification**: Only for trivial code with no complex invariants

**Verification Levels**:

| Level | Tool | Effort | Guarantees |
|-------|------|--------|------------|
| Model Checking | TLA+ | Medium | Algorithm correctness |
| Bounded Verification | Kani | Medium | No panics/UB for bounded inputs |
| Full Verification | Creusot/Prusti | High | Mathematical proof |

**TLA+ for Algorithm Design**:
```tla
---- MODULE EpochReclamation ----
VARIABLES epoch, pinned, deferred

TypeInvariant ==
    /\ epoch \in Nat
    /\ pinned \subseteq THREADS
    /\ deferred \in [Nat -> SUBSET POINTERS]

Safety ==
    \A ptr \in POINTERS:
        ptr \in Reclaimable => NoThreadReferences(ptr)

Liveness ==
    \A ptr \in deferred[e]: <>(ptr \in Reclaimed)
====
```

**Kani for Rust Verification**:
```rust
#[kani::proof]
fn verify_cas_linearizable() {
    let initial: u32 = kani::any();
    let expected: u32 = kani::any();
    let new: u32 = kani::any();
    
    let atom = AtomicU32::new(initial);
    let result = atom.compare_exchange(expected, new, SeqCst, SeqCst);
    
    // Verify CAS semantics
    if initial == expected {
        assert!(result.is_ok());
        assert_eq!(atom.load(SeqCst), new);
    } else {
        assert!(result.is_err());
        assert_eq!(atom.load(SeqCst), initial);
    }
}
```

**CI Requirements**:
- [ ] TLA+ specs for all lock-free algorithms
- [ ] Kani proofs for critical unsafe code
- [ ] Specs updated when algorithm changes
- [ ] Proof failures block merge

---

## 5.20 Fault Injection Testing

**Purpose**: Verify correct behavior when dependencies/resources fail

**Applies When**: Code depends on fallible operations (I/O, allocation, system calls)

**N/A Justification**: Only for pure computation with no external dependencies

**Fault Categories**:

| Fault Type | Injection Method | Tests |
|------------|------------------|-------|
| Allocation failure | Custom allocator | OOM handling |
| I/O failure | Mock/stub | Error propagation |
| Thread spawn failure | Limit enforcement | Graceful degradation |
| Timeout | Artificial delay | Timeout handling |
| Partial failure | Probabilistic injection | Recovery logic |

**Allocation Fault Injection**:
```rust
use std::alloc::{GlobalAlloc, Layout, System};

struct FailingAllocator {
    fail_after: AtomicUsize,
}

unsafe impl GlobalAlloc for FailingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        if self.fail_after.fetch_sub(1, SeqCst) == 0 {
            return std::ptr::null_mut(); // Simulate OOM
        }
        System.alloc(layout)
    }
    // ...
}

#[test]
fn handles_allocation_failure() {
    ALLOCATOR.fail_after.store(10, SeqCst);
    let result = operation_that_allocates();
    assert!(result.is_err()); // Should handle gracefully
}
```

**CI Requirements**:
- [ ] Fault injection tests for all fallible operations
- [ ] No panics on resource exhaustion
- [ ] Error messages are actionable

---

## 5.21 Security Testing

**Purpose**: Identify vulnerabilities beyond what fuzzing catches

**Applies When**: Code handles untrusted input, manages memory, or has safety implications

**N/A Justification**: Rarely N/A for systems code. Even internal libraries can have security implications.

**Security Testing Layers**:

| Layer | Method | Catches |
|-------|--------|---------|
| Fuzzing | Automated | Crashes, panics |
| Sanitizers | Automated | Memory errors, races |
| Static Analysis | cargo-audit | Known CVEs |
| Code Review | Manual | Logic errors, design flaws |
| Security Audit | Expert review | Subtle vulnerabilities |

**Security Checklist for Unsafe Code**:
- [ ] All unsafe blocks have safety comments
- [ ] Pointer validity verified before dereference
- [ ] No unbounded pointer arithmetic
- [ ] Lifetimes correctly enforced
- [ ] No data races possible
- [ ] Integer overflow handled
- [ ] No uninitialized memory exposure

**Security Checklist for Concurrency**:
- [ ] No TOCTOU (time-of-check-time-of-use) races
- [ ] Atomic operations use correct ordering
- [ ] Lock ordering prevents deadlock
- [ ] No ABA vulnerabilities
- [ ] Memory reclamation is safe

**Third-Party Audit Requirements** (for releases):
- [ ] Security-focused code review
- [ ] Documented threat model
- [ ] Known limitations documented
- [ ] Security contact/policy published

---

## 5.22 Dependency Version Matrix Testing

**Purpose**: Ensure compatibility across supported dependency versions

**Applies When**: Library specifies minimum supported Rust version (MSRV) or dependency ranges

**N/A Justification**: Only if no external dependencies and no MSRV commitment

**Requirements**:

**1. MSRV Testing**:
```bash
# Test with minimum supported Rust version
cargo +1.70.0 build
cargo +1.70.0 test
```

**2. Dependency Range Testing**:
```bash
# Test with minimum versions
cargo +nightly -Z minimal-versions build
cargo +nightly -Z minimal-versions test

# Test with latest versions
cargo update
cargo test
```

**CI Matrix**:
```yaml
strategy:
  matrix:
    rust: [1.70.0, stable, beta, nightly]
    deps: [minimal, latest]
```

**CI Requirements**:
- [ ] MSRV tested on every PR
- [ ] Minimal versions tested weekly
- [ ] Beta/nightly tested for early warning
- [ ] Dependency updates tested before merge

---

# 9. Test Quality Standards

## 9.1 Test Independence

**Requirement**: Tests must not depend on execution order or shared state.

- [ ] Each test sets up its own state
- [ ] Tests can run in parallel
- [ ] Tests can run in any order
- [ ] No global mutable state between tests

## 9.2 Test Naming

**Convention**: `test_<unit>_<scenario>_<expected>`

Examples:
- `test_cas_success_returns_old_value`
- `test_stack_pop_empty_returns_none`
- `test_epoch_pin_nested_increments_count`

## 9.3 Test Documentation

**Requirement**: Complex tests must document:
- What is being tested
- Why this test exists (especially regression tests)
- What a failure indicates

```rust
/// Regression test for issue #42: MCS unlock race
/// 
/// Under high contention, the previous implementation could race
/// between unlock and a new lock acquisition, causing hangs.
/// 
/// Failure indicates: Race condition reintroduced in unlock path.
#[test]
fn regression_issue_42_mcs_unlock_race() { ... }
```

## 9.4 Assertion Quality

**Requirements**:
- [ ] Assertions have descriptive messages
- [ ] Expected value first: `assert_eq!(expected, actual)`
- [ ] Test one logical concept per test
- [ ] Use appropriate assertion (eq, ne, matches, etc.)

```rust
// Good
assert_eq!(8, result, "FAA should return previous value + addend");

// Bad
assert!(result == 8);
```

## 9.5 Flaky Test Policy

**Policy**: Flaky tests are bugs. Zero tolerance.

- [ ] No `#[ignore]` for flaky tests
- [ ] Flaky test = immediate investigation
- [ ] Root cause must be found (test bug or real race)
- [ ] Legitimate non-determinism must be made deterministic via Loom

---

# 10. Acceptance Criteria

## 10.1 Per-Module Completion Criteria

A module is **not complete** until:

- [ ] All §5 testing levels addressed (implemented or N/A justified)
- [ ] All applicable feature-triggered requirements satisfied
- [ ] Mutation testing score >90%
- [ ] Static analysis clean (zero clippy warnings)
- [ ] Miri passes (if unsafe code)
- [ ] TSan passes (if concurrent code)
- [ ] Documentation tests pass
- [ ] API compatibility verified

## 10.2 Release Criteria

A release **cannot ship** until:

- [ ] All modules meet completion criteria
- [ ] Full test suite passes on all target platforms
- [ ] Performance benchmarks show no regression
- [ ] Security audit completed (for major releases)
- [ ] Semver compliance verified
- [ ] MSRV tested
- [ ] Changelog documents all changes

## 10.3 Enterprise-Grade Reliability Checklist

**The "FAANG Standard" Verification**:

| Category | Requirement | Verification |
|----------|-------------|--------------|
| **Correctness** | Code does what it claims | Unit + Integration + Property tests |
| **Safety** | No UB, no data races | Miri + Sanitizers + Loom |
| **Robustness** | Handles edge cases | Fuzzing + Fault injection |
| **Security** | No vulnerabilities | Audit + Static analysis |
| **Performance** | Meets requirements | Benchmarks + No regression |
| **Reliability** | Works under stress | Stress tests + Platform matrix |
| **Maintainability** | Tests catch regressions | Mutation testing + CI gates |
| **Compatibility** | Doesn't break users | Semver checks + MSRV |
| **Verifiability** | Provably correct | TLA+ / Formal verification |

**If all boxes checked**: Confidence level matches FAANG production standards.

---

# 11. Continuous Integration Requirements

## 11.1 PR Gate (Every Pull Request)

**Must Pass**:
```yaml
- cargo build --all-features
- cargo test --all-features
- cargo clippy -- -D warnings
- cargo fmt --check
- cargo doc --no-deps
- cargo audit
- RUSTFLAGS="--cfg loom" cargo test --release (if concurrent)
- cargo miri test (if unsafe)
```

## 11.2 Nightly CI

**Extended Testing**:
```yaml
- cargo +nightly -Z minimal-versions test
- RUSTFLAGS="-Zsanitizer=address" cargo +nightly test
- RUSTFLAGS="-Zsanitizer=thread" cargo +nightly test
- cargo mutants --timeout-multiplier 3
- cargo fuzz run <target> -- -max_total_time=3600
```

## 11.3 Release CI

**Full Verification**:
```yaml
- All PR gate checks
- All nightly checks
- Platform matrix (x86_64, aarch64, windows, macos)
- MSRV verification
- Semver compliance check
- Benchmark comparison vs previous release
- Documentation build and link check
```

---

# Appendix A: Test Category Quick Reference

| § | Category | Tool/Method | When Required |
|---|----------|-------------|---------------|
| 5.1 | Unit Testing | cargo test | Always |
| 5.2 | Model Checking | Loom | Concurrent code |
| 5.3 | Integration | cargo test --test | Always |
| 5.4 | Property-Based | proptest | Data structures, algorithms |
| 5.5 | Stress | Custom harness | Concurrent, stateful code |
| 5.6 | Performance | Criterion | Performance-critical code |
| 5.7 | Regression | cargo test | After any bug fix |
| 5.8 | Fuzzing | cargo-fuzz | Input processing |
| 5.9 | Sanitizers | ASan/TSan/MSan | Unsafe/concurrent code |
| 5.10 | Doc Tests | cargo test --doc | Public API |
| 5.11 | Compile-Fail | trybuild | Type-level safety |
| 5.12 | no_std | --no-default-features | Core libraries |
| 5.13 | Resource Exhaustion | Fault injection | Dynamic resources |
| 5.14 | Platform/Arch | CI matrix | Concurrent/platform code |
| 5.15 | Determinism | Repeated runs | Pure functions |
| 5.16 | Mutation | cargo-mutants | Always (validates tests) |
| 5.17 | Static Analysis | clippy, audit | Always |
| 5.18 | API Compat | cargo-semver-checks | Public libraries |
| 5.19 | Formal Verification | TLA+, Kani | Lock-free algorithms |
| 5.20 | Fault Injection | Custom allocator | Fallible operations |
| 5.21 | Security | Audit, review | Systems code |
| 5.22 | Dependency Matrix | CI matrix | MSRV, ranges |

