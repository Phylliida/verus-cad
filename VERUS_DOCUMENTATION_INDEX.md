# Verus Documentation Index

This index helps you navigate the Verus documentation I've compiled.

## Documentation Files

### 1. VERUS_COMPREHENSIVE_GUIDE.md (~16KB, 640 lines)
**Purpose**: Complete reference for Verus usage
**Best for**: Users who want detailed information about all Verus features

**Contents**:
- Introduction to Verus and its capabilities
- **Verus MCP Server** - In-depth explanation of MCP tools
- Installation instructions (build from source, verify crates)
- Basic and advanced usage patterns
- Verus modes (`spec`, `proof`, `exec`) explained in detail
- Writing Verus code with examples
- Advanced features (ghost variables, tracked values, decreases, invariants)
- Common annotations and attributes
- Verification process explanation
- Real examples from the codebase
- Resources (official docs, community, learning materials)
- Troubleshooting guide
- Advanced topics (state machines, field extensions, interval arithmetic)

**Key Features Unique to This Guide**:
- MCP server documentation and usage patterns
- Codebase statistics (11,409 functions, 681 types)
- Module exploration results
- Advanced feature documentation with examples
- State machine and algebraic structure support

### 2. VERUS_USAGE_GUIDE.md (~10KB, 460 lines)
**Purpose**: Beginner-friendly introduction to Verus
**Best for**: New users getting started with Verus

**Contents**:
- Verus introduction and capabilities
- Installation and setup
- Basic usage commands
- Verus modes explained simply
- Writing Verus code with key components
- Common annotations reference
- Verification process overview
- Working examples from the repository
- Resources for further learning
- Quick reference section

**Key Features**:
- Easier to digest for beginners
- Focus on practical usage
- Clear examples
- Quick reference card

### 3. VERUS_DOCUMENTATION_SUMMARY.md (~3.8KB)
**Purpose**: Concise summary of key Verus facts
**Best for**: Quick reference and overview

**Contents**:
- Key facts about Verus
- Installation and setup commands
- Core concepts and modes
- Verification process overview
- Learning resources
- Common commands
- Tips for success

### 4. LEARNED_VERUS_DOCUMENTATION.md (~16KB)
**Purpose**: Summary of what was learned using Verus MCP
**Best for**: Understanding the exploration process and key findings

**Contents**:
- What I learned about Verus MCP server
- Verus scale and complexity (11,409 functions)
- Verus architecture (pipeline: Rust → HIR → VIR → AIR → SMT)
- Key Verus features (modes, ghost code, tracked values)
- Verification process details
- MCP server workflow recommendations
- Codebase organization insights
- Example patterns from verified code
- Integration with tools (Z3, vstd, MCP)

**Key Insights**:
- MCP server tracks context across sessions
- Verus has sophisticated compiler pipeline
- Large proof infrastructure in graphics and algebra
- Ghost code is fundamental to Verus
- SMT solvers do the heavy lifting

## Quick Start Recommendations

### If You're New to Verus
1. **Start with**: `VERUS_USAGE_GUIDE.md` - Beginner-friendly introduction
2. **Then read**: Sections of `VERUS_COMPREHENSIVE_GUIDE.md` on modes and basic usage
3. **Try it**: Verify `verus/examples/vectors.rs` (9 verified, 0 errors)
4. **Explore**: Use Verus MCP server to look up functions

### If You Want Deep Knowledge
1. **Read**: `VERUS_COMPREHENSIVE_GUIDE.md` thoroughly
2. **Explore**: Use MCP server to browse modules and look up functions
3. **Practice**: Verify and modify examples
4. **Dive into**: Architecture (`verus/source/CODE.md`) and build process

### If You Need Specific Information
1. Use the **Table of Contents** in each guide
2. Search for keywords (e.g., "ghost", "decreases", "invariant")
3. Check **Resources** sections for official documentation links
4. Use **Troubleshooting** sections for common issues

## Verus MCP Server Usage

The MCP server provides these key capabilities (all documented in `VERUS_COMPREHENSIVE_GUIDE.md`):

### Essential Functions
- `context_list()` - List existing contexts
- `context_activate(name)` - Create or resume context
- `search(query)` - Find functions by name
- `lookup(name)` - Get function details
- `lookup_source(name)` - Get source code
- `check(crate_name)` - Verify a crate

### Workflow
```
1. context_list() → See existing work
2. context_activate("my-project") → Start/resume context
3. search("decreases") → Find termination functions
4. lookup("function_name") → Get details
5. context_activate("my-project") later → Resume work
```

## Key Statistics Discovered

From `verus_stats()`:
- **Total**: 11,409 functions, 681 types, 16 traits
- **By kind**: 3,607 spec, 5,765 proof, 2,037 exec
- **Proof debt**: 20 `assume(false)` instances
- **Major crates**: 
  - `verus-vulkan`: 3,673 functions (graphics)
  - `verus-cutedsl`: 1,233 functions (parallel DSL)
  - `verus-bigint`: 328 functions (big integers)
  - `verus-rational`: 274 functions (rationals)

## Verification Examples Verified

I tested these examples from the repository:
- `verus/examples/vectors.rs`: 9 verified, 0 errors ✓
- `verus/examples/doubly_linked_xor.rs`: 22 verified, 0 errors ✓

## Learning Path

### Phase 1: Basic Verus (1-2 hours)
1. Read `VERUS_USAGE_GUIDE.md` Sections 1-7
2. Build and run Verus on examples
3. Modify simple examples
4. Understand `requires`, `ensures`, `invariant`

### Phase 2: Intermediate Verus (2-4 hours)
1. Read `VERUS_COMPREHENSIVE_GUIDE.md` Sections 8-12
2. Use MCP server to explore codebase
3. Write functions with `ghost` and `Tracked`
4. Add `decreases` clauses to recursion
5. Use loop invariants effectively

### Phase 3: Advanced Verus (ongoing)
1. Explore advanced features (state machines, fields)
2. Verify complex algorithms
3. Contribute to Verus projects
4. Use MCP server for large codebase exploration
5. Read `verus/source/CODE.md` for architecture

## Resources Summary

### Must-Read Official Docs
- [Verus Guide](https://verus-lang.github.io/verus/guide/getting_started.html) - Tutorial
- [Verus API Docs](https://verus-lang.github.io/verus/verusdoc/vstd/) - Standard library
- [State Machines](https://verus-lang.github.io/verus/state_machines/) - Concurrent code

### Community
- [Verus Zulip Chat](https://verus-lang.zulipchat.com/) - Real-time help
- GitHub Issues/Discussions - Bug reports and Q&A

### Tools
- [Verus Playground](https://play.verus-lang.org/) - Try in browser
- MCP Server - Code exploration and verification

## Troubleshooting Quick Reference

### Common Issues

| Issue | Solution |
|-------|----------|
| Timeout | Break proof into lemmas, add intermediate assertions |
| Type error | Be explicit about types, use annotations |
| Invariant failure | Strengthen invariant, add assertions |
| Resource limits | Simplify specs, increase solver limits |

### MCP Server Tips
- Use `context_activate` to save and resume work
- `lookup` provides detailed function information
- `search` helps find related functions
- Context automatically tracks looked-up items

## Files Location

All documentation files are in: `/Users/yams/Prog/verus-cad/`

- `VERUS_COMPREHENSIVE_GUIDE.md` - Full reference (16KB)
- `VERUS_USAGE_GUIDE.md` - Beginner guide (10KB)
- `VERUS_DOCUMENTATION_SUMMARY.md` - Quick reference (3.8KB)
- `LEARNED_VERUS_DOCUMENTATION.md` - Exploration summary (16KB)
- `VERUS_DOCUMENTATION_INDEX.md` - This file (current)

## Next Steps

1. **Want a quick start?** Read `VERUS_USAGE_GUIDE.md` and try verifying `vectors.rs`
2. **Need detailed information?** Read `VERUS_COMPREHENSIVE_GUIDE.md` with MCP server
3. **Want to understand exploration process?** Read `LEARNED_VERUS_DOCUMENTATION.md`
4. **Need specific commands?** Check quick reference sections in each guide

All documentation is based on:
- Official Verus documentation (linked within)
- Code examples from `verus/examples/`
- Verus MCP server exploration
- Architecture docs in `verus/source/CODE.md`
- Build instructions in `verus/source/BUILD.md`
