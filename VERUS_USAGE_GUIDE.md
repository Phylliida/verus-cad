# Verus Usage Guide

This guide provides comprehensive documentation on how to use Verus, a static verifier for Rust code.

## Table of Contents
1. [Introduction to Verus](#introduction-to-verus)
2. [Installation](#installation)
3. [Basic Usage](#basic-usage)
4. [Verus Modes](#verus-modes)
5. [Writing Verus Code](#writing-verus-code)
6. [Common Annotations](#common-annotations)
7. [Verification Process](#verification-process)
8. [Examples](#examples)
9. [Resources](#resources)
10. [Quick Reference](#quick-reference)

---

## Introduction to Verus

Verus is a tool for verifying the correctness of Rust code. It allows developers to:
- Write specifications (preconditions, postconditions, invariants)
- Statically prove that code satisfies specifications
- Catch bugs at compile time rather than runtime
- Verify memory safety and other properties

Verus uses SMT solvers (like Z3) to automatically prove correctness properties.

---

## Installation

### 1. Build Verus from Source

```bash
cd verus/source
./tools/get-z3.sh
source ../tools/activate
vargo build --release
cd ../..
```

Note: You may need to install the Rust toolchain as indicated by the build process.

### 2. Verify Individual Repositories

Once Verus is built, you can verify any crate using the verus mcp check tool

### 3. Run Verus on a File

```bash
# From source directory
vargo run -p rust_verify --release -- ../examples/vectors.rs

# Or directly
./target-verus/release/verus ./examples/vectors.rs
```

---

## Basic Usage

### Verifying a Single File

```bash
verus my_file.rs
```

### Verifying an Entire Crate

```bash
verus src/lib.rs  # For libraries
verus src/main.rs  # For executables
```

### Common Command-line Options

- `--compile`: Compile the code after verification
- `--verbose`: Show detailed output
- `--log`: Enable logging
- `--timeout <seconds>`: Set verification timeout

---

## Verus Modes

Verus has three modes that control how code is treated:

### 1. `spec` mode (Specification)
- Used for pure, mathematical specifications
- Erased during compilation
- Cannot contain side effects
- Used for:
  - Function preconditions (`requires`)
  - Function postconditions (`ensures`)
  - Loop invariants (`invariant`)
  - Type invariants

### 2. `proof` mode (Proof)
- Used for proof code that verifies specifications
- Erased during compilation
- Can use tactics and intermediate steps
- Used for:
  - Proof blocks (`proof { }`)
  - Lemma statements

### 3. `exec` mode (Executable)
- Used for actual executable code
- Compiled and runs normally
- Can use mutable state
- Used for:
  - Function implementations
  - Data structure operations

---

## Writing Verus Code

### Basic Structure

```rust
verus! {
    // Your verified code here
    
    // Functions with specifications
    fn my_function(x: u64) -> (result: u64)
        requires x > 0
        ensures result > x
    {
        // Implementation
        x + 1
    }
}
```

### Key Components

#### 1. Function Specifications

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

#### 2. Loop Invariants

```rust
for i in 0..n
    invariant invariant_condition
    decreases measure
{
    // Loop body
}
```

#### 3. Proof Blocks

```rust
proof {
    // Proof steps
    assert(something);
    have intermediate := calculate_something();
    // ...
}
```

---

## Common Annotations

### 1. `verus!` Macro

Wraps Rust code to enable Verus verification. All verified code must be inside a `verus!` block.

### 2. `requires`

Specifies preconditions that must be true when a function is called.

```rust
fn divide(a: u64, b: u64) -> (result: u64)
    requires b != 0  // Must not divide by zero
{
    a / b
}
```

### 3. `ensures`

Specifies postconditions that must be true when a function returns.

```rust
fn divide(a: u64, b: u64) -> (result: u64)
    ensures b != 0 ==> a == result * b + (a % b)
```

### 4. `invariant`

Specifies loop invariants that must be maintained.

```rust
while i < n
    invariant i <= n
    decreases n - i
{
    i = i + 1;
}
```

### 5. `decreases`

Specifies a measure for termination checking.

```rust
fn recursive_function(x: u64) -> u64
    decreases x
{
    if x == 0 { 0 } else { recursive_function(x - 1) + 1 }
}
```

### 6. `ghost`

Marks code or data as ghost code (removed during compilation).

```rust
let ghost original = my_vector@;
```

### 7. `Tracked` and `Ghost`

Wrappers for tracked and ghost data.

```rust
let tracked tracked_value: T;
let ghost ghost_value: T;
```

---

## Verification Process

Verus transforms Rust code through multiple stages:

1. **Rust Source Code** → Parsed by rustc
2. **HIR (High-level IR)** → Converted to VIR
3. **VIR-AST** → Simplified and normalized
4. **VIR-SST** → Statement-oriented form
5. **AIR** → Assertion IR for SMT encoding
6. **SMT-LIB queries** → Sent to Z3/cvc5
7. **Verification Results** → Valid or counterexample

### Understanding Verification Output

Successful verification:
```
verification results:: 9 verified, 0 errors
```

Failed verification (with counterexample):
```
verification results:: 0 verified, 1 errors
```

---

## Examples

### Example 1: Binary Search

```rust
verus! {

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

}
```

### Example 2: Vector Reversal

```rust
verus! {

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
            forall|i: int| 0 <= i < n ==> v1[i] == v[length - i - 1],
            forall|i: int| n <= i && i + n < length ==> #[trigger] v[i] == v1[i],
    {
        let x = v[n];
        let y = v[length - 1 - n];
        v.set(n, y);
        v.set(length - 1 - n, x);
    }
}

}
```

---

## Resources

### Official Documentation
- [Verus Guide](https://verus-lang.github.io/verus/guide/getting_started.html) - Getting started tutorial
- [Verus API Documentation](https://verus-lang.github.io/verus/verusdoc/vstd/) - Standard library docs
- [Verus State Machines](https://verus-lang.github.io/verus/state_machines/) - Concurrent code verification

### Community
- [Verus Zulip Chat](https://verus-lang.zulipchat.com/) - Get help and discuss Verus
- [GitHub Issues](https://github.com/verus-lang/verus/issues) - Report bugs
- [GitHub Discussions](https://github.com/verus-lang/verus/discussions) - Feature requests and Q&A

### Learning Resources
- [Verus Playground](https://play.verus-lang.org/) - Try Verus in your browser
- [Videos and Slides](https://verus-lang.github.io/event-sites/2024-sosp/) - Tutorial materials
- [Examples Repository](https://github.com/secure-foundations/human-eval-verus/) - Practical examples

### Development
- [Contributing to Verus](CONTRIBUTING.md)
- [Verus Source Code](verus/source/CODE.md) - Architecture overview
- [Build Instructions](verus/BUILD.md) - Detailed build guide

---

## Quick Reference

### Verification Commands

```bash
# Verify a single file
./target-verus/release/verus path/to/file.rs

# Verify with compilation
./target-verus/release/verus path/to/file.rs --compile

# Verify verbose output
./target-verus/release/verus path/to/file.rs --verbose

# Verify an entire crate
./target-verus/release/verus src/lib.rs
```

### Common Patterns

```rust
// Function with pre/post conditions
fn my_func(x: u64) -> (result: u64)
    requires x > 0
    ensures result > 0
{
    x + 1
}

// Loop with invariant
for i in 0..n
    invariant i <= n
    decreases n - i
{
    // loop body
}

// Ghost variable
ghost! { let x = value; }

// Proof block
proof {
    assert!(condition);
}
```

### Useful Attributes

```rust
#[verifier::loop_isolation(false)]  // Disable loop isolation
#[verifier::auto]                    // Auto-apply tactic
```

---

## Tips and Best Practices

1. **Start Small**: Begin with simple functions and gradually add complexity.
2. **Use Ghost Code**: Leverage ghost code for specifications and intermediate values.
3. **Write Invariants**: Always specify loop invariants for complex loops.
4. **Check Counterexamples**: When verification fails, carefully examine the counterexample.
5. **Iterate**: Verification is an iterative process - refine your specifications and code.

---

## Troubleshooting

### Common Issues

1. **Resource Limits**: Large proofs may hit SMT solver limits. Try:
   - Breaking into smaller lemmas
   - Using `set_option` to increase limits
   - Simplifying specifications

2. **Timeouts**: If verification takes too long:
   - Add intermediate assertions
   - Use `decreases` to help with termination
   - Consider if the proof can be structured differently

3. **Type Errors**: Verus has stricter typing than Rust:
   - Explicit conversions may be needed
   - Some Rust operations aren't supported in spec mode

---

This guide provides a starting point for using Verus. For complete documentation, always refer to the [official Verus documentation](https://verus-lang.github.io/verus/guide/).
