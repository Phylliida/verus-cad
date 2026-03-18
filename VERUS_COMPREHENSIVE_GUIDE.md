# Comprehensive Verus Usage Guide

This guide provides detailed documentation on Verus, including its features, tools, and usage patterns based on the Verus MCP server and codebase analysis.

## Table of Contents
1. [Introduction to Verus](#introduction-to-verus)
2. [Verus MCP Server](#verus-mcp-server)
3. [Installation](#installation)
4. [Basic Usage](#basic-usage)
5. [Verus Modes](#verus-modes)
6. [Writing Verus Code](#writing-verus-code)
7. [Advanced Features](#advanced-features)
8. [Common Annotations](#common-annotations)
9. [Verification Process](#verification-process)
10. [Examples](#examples)
11. [Resources](#resources)
12. [Troubleshooting](#troubleshooting)

---

## Introduction to Verus

Verus is a static verifier for Rust that:
- Proves code correctness for all possible executions
- Uses SMT solvers (Z3, cvc5) to automatically verify properties
- Supports ghost code (specifications erased during compilation)
- Works with a subset of Rust with verification-specific extensions

### Key Statistics (from Verus MCP)
- **11,409 functions** across 22 crates
- **681 types** and **16 traits**
- **Breakdown**: 3,607 spec, 5,765 proof, 2,037 exec functions
- **Proof debt**: 20 `assume(false)` instances

---

## Verus MCP Server

The Verus MCP (Model Context Protocol) server provides tools for browsing and understanding Verus code.

### MCP Capabilities

The `verus-mcp` server (located in `verus-mcp/src/server.rs`) provides 68 functions for:
- **Searching**: Find functions by name, type, or property
- **Browsing**: Explore modules and their contents
- **Lookup**: Get detailed information about functions
- **Verification**: Run Verus checks
- **Context Management**: Track looked-up items across sessions

### Key MCP Functions

#### Search Functions
- `search(query)` - Find functions by name substring
- `search_ensures(query)` - Find lemmas proving specific properties
- `search_requires(query)` - Find preconditions for lemmas
- `search_body(query)` - Find functions using specific lemmas
- `search_signature(param_type, return_type)` - Find by type signature
- `search_types(query)` - Find types by name
- `search_trait(name)` - Find trait definitions and implementors

#### Lookup Functions
- `lookup(name)` - Get full details (signature, requires/ensures)
- `lookup_source(name)` - Get complete source code
- `batch_lookup(names)` - Lookup multiple items at once

#### Verification Functions
- `check(crate_name)` - Verify entire crate
- `compile(crate_name)` - Compile without verification
- `run(crate_name)` - Run compiled binary
- `profile(crate_name)` - Get performance breakdown

#### Context Management
- `context_list()` - List recent contexts
- `context_activate(name)` - Resume or create context
- Items are auto-captured when looked up

### Using the MCP Server

```
1. Call context_list() to see existing contexts
2. Call context_activate("my-context") to create/resume
3. Use lookup(), search(), or other functions
4. Items are automatically tracked in the context
5. Reactivate context later to resume work
```

---

## Installation

### 1. Build Verus from Source

```bash
cd verus/source
./tools/get-z3.sh          # Download Z3 solver
source ../tools/activate  # Set up environment
vargo build --release      # Build Verus
cd ../..
```

### 2. Verify Individual Crates

```bash
cd verus-bigint && ./scripts/check.sh
cd verus-rational && ./scripts/check.sh
cd verus-algebra && ./scripts/check.sh
# ... etc
```

### 3. Run Verification

```bash
# From source directory
vargo run -p rust_verify --release -- ../examples/vectors.rs

# Or directly
./target-verus/release/verus ./examples/vectors.rs
```

### 4. Using MCP Server

The MCP server is built automatically with Verus:
- Located in `verus-mcp/` directory
- Provides LSP-like functionality for Verus code
- Tracks context across sessions

---

## Basic Usage

### Verifying a Single File

```bash
verus my_file.rs
```

### Verifying with Compilation

```bash
verus my_file.rs --compile
```

### Verifying with Verbose Output

```bash
verus my_file.rs --verbose
```

### Setting Timeout

```bash
verus my_file.rs --timeout 120
```

### Verifying Entire Crate

```bash
verus src/lib.rs  # For libraries
verus src/main.rs  # For executables
```

---

## Verus Modes

Verus has three primary modes that control how code is treated:

### 1. `spec` Mode (Specification)

- **Purpose**: Pure mathematical specifications
- **Behavior**: Erased during compilation, cannot execute
- **Used for**:
  - Function preconditions (`requires`)
  - Function postconditions (`ensures`)
  - Loop invariants (`invariant`)
  - Type invariants
  - Mathematical definitions

**Example**:
```rust
spec fn is_sorted(v: &Vec<u64>) -> bool
    ensures forall|i: int, j: int| 0 <= i <= j < v.len() ==> v[i] <= v[j]
{
    // Pure specification, no implementation
}
```

### 2. `proof` Mode (Proof)

- **Purpose**: Verification code that proves specifications
- **Behavior**: Erased during compilation, can use tactics
- **Used for**:
  - Proof blocks (`proof { }`)
  - Lemma statements
  - Intermediate proof steps

**Example**:
```rust
proof {
    assert(x > 0);
    have h : x + 1 > 1 := by linarith;
    exact h;
}
```

### 3. `exec` Mode (Executable)

- **Purpose**: Actual executable code
- **Behavior**: Compiled and runs normally
- **Used for**:
  - Function implementations
  - Data structure operations
  - Runtime code

**Example**:
```rust
fn add(x: u64, y: u64) -> u64
    ensures result == x + y
{
    x + y  // Actual implementation
}
```

---

## Writing Verus Code

### Basic Structure

All verified code must be inside a `verus!` macro:

```rust
verus! {
    // Your verified code here
    
    fn my_function(x: u64) -> (result: u64) {
        // Implementation
    }
}
```

### Function Specifications

```rust
fn function_name(param: Type) -> (result: Type)
    requires precondition1,
    requires precondition2,
    ensures postcondition1,
    ensures postcondition2,
    decreases measure_for_termination,
{
    // Implementation
}
```

### Loop Invariants

```rust
while condition
    invariant invariant_condition
    decreases measure
{
    // Loop body
}
```

### Proof Blocks

```rust
proof {
    // Proof steps
    assert(condition);
    have intermediate := calculate();
    apply lemma_name;
}
```

---

## Advanced Features

### Ghost Variables

Mark variables as ghost (removed during compilation):

```rust
let ghost my_spec = value;  // Ghost specification
let tracked tracked_value: T;  // Tracked (verified) value
```

### Type Invariants

```rust
#[verifier::type_invariant]
impl MyType {
    fn invariant(self: &Self) -> bool {
        // Type invariant
    }
}
```

### Multiple Return Values

```rust
fn my_func() -> (a: u64, b: u64)
    ensures a + b == 10
{
    (5, 5)
}
```

### Decreases Clauses

For termination checking in recursive functions:

```rust
fn recursive(n: u64) -> u64
    decreases n  // Must decrease with each call
{
    if n == 0 { 0 } else { recursive(n - 1) + 1 }
}
```

### Set Comprehensions

```rust
ensures forall|i: int| 0 <= i < v.len() ==> v[i] > 0
ensures exists|i: int| v[i] == target
```

### Old Expressions

Refer to previous state:

```rust
fn update(x: &mut u64)
    ensures *x == old(*x) + 1
{
    *x = *x + 1;
}
```

---

## Common Annotations

### `#[verifier::loop_isolation(false)]`

Disable loop isolation optimization (useful for debugging).

### `#[verifier::auto]`

Auto-apply tactic or lemma.

### `#[verifier::external]`

Mark function as external (skip verification).

### `#[verifier::recommended]`

Mark as recommended pattern.

---

## Verification Process

Verus transforms code through multiple stages:

```
Rust Source → HIR → VIR-AST → VIR-SST → AIR → SMT-LIB → Z3/cvc5 → Results
```

### Stages Explained

1. **Rust Source**: Parsed by rustc with Verus macros
2. **HIR**: High-level IR with macro expansion
3. **VIR-AST**: Verification IR (Abstract Syntax Tree)
4. **VIR-SST**: Statement-oriented Syntax Tree
5. **AIR**: Assertion IR for SMT encoding
6. **SMT-LIB**: Query language for SMT solvers
7. **Solvers**: Z3 or cvc5 prove the queries

### Verification Output

```
verification results:: 9 verified, 0 errors
```

- First number: Successfully verified statements
- Second number: Errors found (0 = success)

### Understanding Failures

When verification fails, examine:
1. **Counterexample**: Values that violate the property
2. **Error location**: Where the failure was detected
3. **Context**: Surrounding code and invariants

---

## Examples from Codebase

### Example 1: Binary Search (vectors.rs)

```rust
fn binary_search(v: &Vec<u64>, k: u64) -> (r: usize)
    requires
        forall|i: int, j: int| 0 <= i <= j < v.len() ==> v[i] <= v[j],
        exists|i: int| 0 <= i < v.len() && k == v[i],
    ensures
        r < v.len(),
        k == v[r as int],
{
    let mut i1: usize = 0;
    let mut i2: usize = v.len() - 1;
    while i1 != i2
        invariant
            i2 < v.len(),
            exists|i: int| i1 <= i <= i2 && k == v[i],
            forall|i: int, j: int| 0 <= i <= j < v.len() ==> v[i] <= v[j],
        decreases i2 - i1,
    {
        let ix = i1 + (i2 - i1) / 2;
        if v[ix] < k {
            i1 = ix + 1;
        } else {
            i2 = ix;
        }
    }
    i1
}
```

### Example 2: Vector Reversal

```rust
fn reverse(v: &mut Vec<u64>)
    ensures
        v.len() == old(v).len(),
        forall|i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1],
{
    let length = v.len();
    let ghost v1 = v@;
    for n in 0..(length / 2)
        invariant
            length == v.len(),
            forall|i: int| 0 <= i < n ==> v[i] == v1[length - i - 1],
            forall|i: int| n <= i && i + n < length ==> v[i] == v1[i],
    {
        let x = v[n];
        let y = v[length - 1 - n];
        v.set(n, y);
        v.set(length - 1 - n, x);
    }
}
```

### Example 3: Loop Invariant (from scan.rs)

```rust
proof fn lemma_scan_increases_index(
    scan: ScanState,
    idx: u64,
    len: u64,
) {
    requires scan.ty == ScanTy::Idx
    requires idx <= len
    ensures idx < scan.i
}
```

---

## Resources

### Official Documentation
- **[Verus Guide](https://verus-lang.github.io/verus/guide/getting_started.html)** - Getting started tutorial
- **[Verus API Docs](https://verus-lang.github.io/verus/verusdoc/vstd/)** - Standard library documentation
- **[Verus State Machines](https://verus-lang.github.io/verus/state_machines/)** - Concurrent code verification
- **[Verus Publications](https://verus-lang.github.io/verus/publications-and-projects/)** - Research papers and projects

### Community
- **[Verus Zulip Chat](https://verus-lang.zulipchat.com/)** - Real-time discussions and help
- **[GitHub Issues](https://github.com/verus-lang/verus/issues)** - Report bugs
- **[GitHub Discussions](https://github.com/verus-lang/verus/discussions)** - Feature requests and Q&A

### Learning Resources
- **[Verus Playground](https://play.verus-lang.org/)** - Try Verus in browser
- **[Videos and Slides](https://verus-lang.github.io/event-sites/2024-sosp/)** - Tutorial materials
- **[Examples Repository](https://github.com/secure-foundations/human-eval-verus/)** - Practical examples
- **[Verus Videos](https://verus-lang.github.io/event-sites/2024-sosp/)** - Day-long tutorial

### Development
- **[Contributing to Verus](CONTRIBUTING.md)**
- **[Verus Architecture](verus/source/CODE.md)** - Detailed architecture overview
- **[Build Instructions](verus/BUILD.md)** - Complete build guide
- **[Verus Source Code](verus/source/)** - Explore the compiler

### MCP Server Documentation
- **Server Location**: `verus-mcp/src/server.rs`
- **Functions**: 68 tools for code browsing and verification
- **Context Tracking**: Automatic capture of looked-up items
- **Context Management**: Save and resume work sessions

---

## Verus Codebase Overview

Based on MCP analysis, the codebase includes:

### Major Crates

1. **verus-vulkan** (3,673 functions): Graphics and Vulkan support
2. **verus-cutedsl** (1,233 functions): DSL for parallel computations
3. **verus-bigint** (328 functions): Big integer support
4. **verus-rational** (274 functions): Rational number support
5. **verus-geometry** (761 functions): Geometric computations
6. **verus-linalg** (772 functions): Linear algebra
7. **verus-mcp** (209 functions): MCP server implementation

### Key Modules

- **runtime**: Runtime system and state management
- **construction**: Memory construction and initialization
- **algebra**: Algebraic structures and operations
- **interval**: Interval arithmetic
- **text_model**: Text editing and modeling
- **safety**: Safety proofs and resource management
- **asset_pipeline**: Asset processing pipeline

---

## Tips and Best Practices

### 1. Start Small
- Begin with simple functions and incrementally add complexity
- Use `verus!` blocks to separate verified from non-verified code

### 2. Use Ghost Code Effectively
- Mark pure specifications with `ghost`
- Use `Tracked` for values that need verification
- Keep ghost code separate from executable logic

### 3. Write Clear Invariants
- Always specify loop invariants for non-trivial loops
- Use `decreases` for recursive functions
- Make invariants precise and checkable

### 4. Break Down Complex Proofs
- Split large proofs into smaller lemmas
- Use intermediate `have` statements
- Structure proofs hierarchically

### 5. Handle Counterexamples
- When verification fails, study the counterexample carefully
- Check if the specification is correct or too strict
- Use intermediate assertions to narrow down the issue

### 6. Use MCP Server
- Leverage `context_activate` to resume work
- Use `lookup` and `search` to explore code
- Track items automatically for later reference

---

## Troubleshooting

### Common Issues

#### Resource Limits
**Symptom**: Verification times out or hits solver limits
**Solutions**:
- Break proof into smaller lemmas
- Add intermediate assertions to guide solver
- Use `set_option` to increase solver resources
- Simplify specifications

#### Timeouts
**Symptom**: Verification takes too long
**Solutions**:
- Add `decreases` clauses to help with termination
- Structure recursive functions to decrease measures
- Consider if proof can be restructured
- Use `#[verifier::loop_isolation(false)]` if needed

#### Type Errors
**Symptom**: Verus rejects valid Rust types
**Solutions**:
- Be explicit about types, especially with ghost code
- Use type annotations for complex expressions
- Check that types are supported in spec mode

#### Invariant Failures
**Symptom**: Loop or type invariants not satisfied
**Solutions**:
- Strengthen the invariant
- Add intermediate assertions
- Check loop condition and update logic
- Use `assert` to verify invariant at specific points

### Debugging Tools

1. **Verbose Output**: Use `--verbose` flag
2. **MCP Lookup**: Use `lookup()` to get function details
3. **Search**: Use `search()` to find related functions
4. **Context**: Use `context_list()` and `context_activate()`

---

## Advanced Topics

### State Machines
Verus supports complex state machine specifications for concurrent code:
- Define states and transitions
- Prove safety properties
- Verify liveness conditions

### Field Extensions
- Work with finite field extensions
- Prove properties about algebraic structures
- Support for quadratic and higher extensions

### Interval Arithmetic
- Reason about numerical bounds
- Prove properties involving approximations
- Support for complex intervals

### Algebraic Structures
- Fields, rings, groups
- Ordered structures
- Additive and multiplicative structures

### Resource Management
- Memory allocation and deallocation
- Resource tracking and validation
- Safety proofs for complex operations

---

This guide provides a comprehensive starting point for using Verus. For complete and up-to-date documentation, always refer to the [official Verus documentation](https://verus-lang.github.io/verus/guide/) and use the [Verus MCP server](verus-mcp/) for code exploration.
