# Verus Documentation Summary

This document summarizes the key information about Verus gathered from the codebase.

## What is Verus?

Verus is a static verifier for Rust code that:
- Allows developers to write specifications (preconditions, postconditions, invariants)
- Statically proves code satisfies specifications for all possible executions
- Uses SMT solvers (Z3, cvc5) to automatically prove correctness
- Supports three modes: `spec` (ghost specifications), `proof` (verification code), and `exec` (executable code)

## Installation & Setup

### Build from Source
```bash
cd verus/source
./tools/get-z3.sh
source ../tools/activate
vargo build --release
cd ../..
```

### Verify Crates
```bash
cd verus-bigint && ./scripts/check.sh
cd verus-rational && ./scripts/check.sh
cd verus-algebra && ./scripts/check.sh
# etc.
```

### Run Verus
```bash
# From source directory
vargo run -p rust_verify --release -- ../examples/vectors.rs

# Or directly
./target-verus/release/verus ./examples/vectors.rs
```

## Core Concepts

### Three Modes
1. **`spec`**: Pure mathematical specifications (erased during compilation)
2. **`proof`**: Verification code (erased during compilation)
3. **`exec`**: Executable code (compiled normally)

### Key Annotations

- `verus! { }`: Macro wrapping all verified code
- `requires`: Precondition specification
- `ensures`: Postcondition specification
- `invariant`: Loop invariant
- `decreases`: Termination measure
- `ghost`: Ghost variable (removed during compilation)
- `proof { }`: Proof block

### Verification Process

1. Rust source → HIR (via rustc)
2. HIR → VIR (Verification IR)
3. VIR → AIR (Assertion IR)
4. AIR → SMT-LIB queries
5. Z3/cvc5 solver → Verification results

## Verified Examples

The repository includes working examples:
- `verus/examples/vectors.rs`: Binary search, vector reversal, etc.
- `verus/examples/doubly_linked_xor.rs`: XOR linked list operations

Both verify successfully with 0 errors.

## Learning Resources

1. **Official Documentation**:
   - [Verus Guide](https://verus-lang.github.io/verus/guide/getting_started.html)
   - [Verus API Docs](https://verus-lang.github.io/verus/verusdoc/vstd/)

2. **Community**:
   - [Verus Zulip Chat](https://verus-lang.zulipchat.com/)
   - GitHub Issues/Discussions

3. **Learning Materials**:
   - [Verus Playground](https://play.verus-lang.org/)
   - Tutorial videos and slides
   - Example repositories

## Common Commands

```bash
# Verify file
verus my_file.rs

# Verify with compilation
verus my_file.rs --compile

# Verify verbose
verus my_file.rs --verbose

# Verify crate
verus src/lib.rs
```

## Verification Results Format

```
verification results:: 9 verified, 0 errors
```

- First number: successfully verified statements
- Second number: errors found

## Key Files & Directories

- `verus/source/`: Verus compiler source
- `verus/source/CODE.md`: Architecture documentation
- `verus/source/BUILD.md`: Build instructions
- `verus/source/examples/`: Example code
- `verus2/`: Alternative Verus implementation
- `verus2/examples/`: More examples

## Tips for Success

1. Start with simple functions and add specifications incrementally
2. Use ghost variables for specifications that don't affect execution
3. Always provide loop invariants for non-trivial loops
4. Use `decreases` for recursive functions to prove termination
5. When verification fails, carefully examine counterexamples
6. Break complex proofs into smaller lemmas

## Troubleshooting

- **Resource limits**: Break into smaller pieces or increase solver limits
- **Timeouts**: Add intermediate assertions or simplify specifications
- **Type errors**: Be explicit about types, especially with ghost code

---

For complete and up-to-date documentation, always refer to the official [Verus Guide](https://verus-lang.github.io/verus/guide/getting_started.html).
