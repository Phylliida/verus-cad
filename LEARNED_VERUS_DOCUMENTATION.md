# Learned Verus Documentation

This document summarizes what was learned about Verus by using the Verus MCP server and exploring the codebase.

## What I Learned

### 1. Verus MCP Server Capabilities

The Verus MCP server (`verus-mcp/src/server.rs`) provides 68 functions for:
- **Searching functions**: By name, type signature, requires/ensures clauses
- **Browsing modules**: Explore the entire Verus codebase structure
- **Lookup functions**: Get detailed information including source code
- **Verification**: Run Verus checks directly from MCP
- **Context management**: Save and resume work sessions automatically

**Key insight**: The MCP server tracks context across sessions using `context_list()` and `context_activate()`, making it perfect for ongoing Verus exploration.

### 2. Verus Scale and Complexity

From `verus_stats()`:
- **11,409 total functions** across 22 crates
- **681 types** and **16 traits**
- **Breakdown**: 3,607 spec, 5,765 proof, 2,037 exec functions
- **Proof debt**: 20 `assume(false)` instances (areas needing proof)

**Key insight**: Verus is a large, actively-developed system with substantial proof infrastructure, particularly in:
- `verus-vulkan` (3,673 functions) - graphics and Vulkan support
- `verus-cutedsl` (1,233 functions) - parallel computation DSL
- `verus-bigint` and `verus-rational` - number theory support

### 3. Verus Architecture

From `verus/source/CODE.md`:

**Pipeline**: Rust → HIR → VIR-AST → VIR-SST → AIR → SMT-LIB → Z3/cvc5

**Key components**:
- `rust_verify`: Main verifier driver
- `vir`: Verification IR generation
- `air`: Assertion IR for SMT encoding
- `vstd`: Verus standard library (verified itself)

**Key insight**: Verus is a sophisticated compiler that transforms Rust code through multiple IRs before sending to SMT solvers.

### 4. Key Verus Features

#### Modes
- **`spec`**: Pure specifications (erased, ghost)
- **`proof`**: Verification code (erased, can use tactics)
- **`exec`**: Executable code (compiled normally)

#### Advanced Features
- **Ghost variables**: `let ghost x = value;` (removed during compilation)
- **Tracked values**: `let tracked x: T;` (verified but not executed)
- **Decreases clauses**: For termination checking in recursion
- **Loop invariants**: Essential for non-trivial loops
- **Set comprehensions**: `forall`, `exists` in specifications
- **Old expressions**: `old(x)` to refer to previous state

### 5. Verification Process

Verus works by:
1. Converting Rust code to VIR (Verification IR)
2. Encoding VIR to AIR (Assertion IR)
3. Translating AIR to SMT-LIB queries
4. Sending queries to Z3/cvc5 SMT solvers
5. Checking if properties hold for all possible executions

**Key insight**: The power of Verus comes from its ability to automatically prove properties that would be tedious to prove manually.

### 6. Error Handling

When verification fails:
- **Counterexamples** show values that violate properties
- **Error locations** pinpoint where failures occur
- **Context** helps understand surrounding code

**Key insight**: Verification failures provide detailed information to debug specifications and code.

### 7. MCP Server Workflow

**Recommended workflow**:
1. `context_list()` - See existing contexts
2. `context_activate("my-task")` - Create or resume context
3. `search(query)` - Find relevant functions
4. `lookup(name)` - Get detailed information
5. `batch_lookup(names)` - Look up multiple items
6. Save context for later: automatically persisted

**Key insight**: The MCP server's context tracking makes it ideal for learning and exploring Verus incrementally.

### 8. Codebase Organization

Major crates by function count:
1. `verus-vulkan`: Graphics and Vulkan API verification
2. `verus-cutedsl`: Parallel computation DSL and proofs
3. `verus-bigint`: Big integer arithmetic
4. `verus-rational`: Rational number support
5. `verus-geometry`: Geometric computations
6. `verus-linalg`: Linear algebra
7. `verus-mcp`: MCP server implementation

**Key insight**: Verus has extensive support for verifying complex systems, particularly graphics and algebraic computations.

### 9. Example Patterns

From verified examples:
- **Binary search**: Uses loop invariants and set comprehensions
- **Vector reversal**: Demonstrates ghost variables and array manipulation
- **Scan operations**: Shows parallel computation patterns
- **Resource management**: Complex state machine specifications

**Key insight**: Real Verus code uses sophisticated patterns combining specifications, proofs, and executable code.

### 10. Integration with Tools

Verus integrates with:
- **Z3/cvc5**: SMT solvers for automated reasoning
- **Rust compiler**: Parses and type-checks code
- **vstd**: Verified standard library
- **MCP server**: For code browsing and exploration

**Key insight**: Verus is part of a larger ecosystem of verification tools.

---

## Documentation Created

I created two comprehensive guides:

### 1. VERUS_USAGE_GUIDE.md (~10KB)
- Introductory guide for beginners
- Covers basics of installation, usage, and examples
- Includes quick reference section
- 460 lines

### 2. VERUS_COMPREHENSIVE_GUIDE.md (~24KB)
- Detailed guide covering all aspects of Verus
- Includes MCP server documentation
- Explores advanced features and codebase structure
- 640 lines

Both guides include:
- Installation instructions
- Basic and advanced usage patterns
- Example code from the repository
- Links to official documentation
- Troubleshooting tips

---

## Key Resources Discovered

1. **Official Documentation**:
   - [Verus Guide](https://verus-lang.github.io/verus/guide/getting_started.html)
   - [Verus API Docs](https://verus-lang.github.io/verus/verusdoc/vstd/)
   - [State Machines](https://verus-lang.github.io/verus/state_machines/)

2. **Community**:
   - [Verus Zulip Chat](https://verus-lang.zulipchat.com/)
   - GitHub issues and discussions

3. **Learning Materials**:
   - [Verus Playground](https://play.verus-lang.org/)
   - [Tutorial Videos](https://verus-lang.github.io/event-sites/2024-sosp/)
   - [Examples](https://github.com/secure-foundations/human-eval-verus/)

4. **Source Code**:
   - `verus/source/CODE.md` - Architecture overview
   - `verus/source/BUILD.md` - Build instructions
   - `verus-mcp/src/server.rs` - MCP server implementation

---

## Technical Details

### Verification Example

```bash
# Verify a file
./target-verus/release/verus ./verus/examples/vectors.rs
# Output: verification results:: 9 verified, 0 errors
```

### MCP Server Example

```
1. context_list() -> See existing contexts
2. context_activate("learning-verus") -> Create context
3. search("decreases") -> Find termination-related functions
4. lookup("lemma_free_decreases_total") -> Get details
5. context_activate("learning-verus") later -> Resume work
```

### Key Functions Found

- **`decreases`**: Termination checking (6 results)
- **`invariant`**: Loop invariants (10+ results)
- **`ghost`**: Ghost variables (72 results)
- **`proof`**: Proof mode functions
- **`spec`**: Specification mode functions

---

## Summary

Verus is a powerful, actively-developed verification tool for Rust that:
- Uses SMT solvers to automatically prove correctness
- Supports ghost code for specifications
- Has extensive support for complex domains (graphics, algebra)
- Provides sophisticated tools for code exploration via MCP
- Is used in research and industry for critical systems

The MCP server makes Verus accessible by providing LSP-like functionality for code browsing, search, and verification.

For anyone learning Verus, I recommend:
1. Start with the official [Getting Started Guide](https://verus-lang.github.io/verus/guide/getting_started.html)
2. Use the Verus MCP server to explore examples
3. Begin with simple functions and gradually add specifications
4. Use `verus!` blocks to separate verified from non-verified code
5. Leverage `ghost` and `Tracked` for specifications
6. Always provide `decreases` and `invariant` clauses

---

## Files Created

- `VERUS_USAGE_GUIDE.md` - Beginner-friendly guide
- `VERUS_COMPREHENSIVE_GUIDE.md` - Detailed reference
- `LEARNED_VERUS_DOCUMENTATION.md` - This summary

All files are in `/Users/yams/Prog/verus-cad/`
