# Verus Quick Reference

## Table of Contents
0. [First Principles](#0-first-principles)
1. [Quick Reference](#1-quick-reference)
2. [When to Use What](#2-when-to-use-what)
3. [Core Concepts](#3-core-concepts)
4. [Patterns & Techniques](#4-patterns--techniques)
5. [Common Errors & Fixes](#5-common-errors--fixes)
6. [Common Pitfalls](#6-common-pitfalls)
7. [MCP Tools](#7-mcp-tools)
8. [Workspace Overview](#8-workspace-overview)

---

## 0. First Principles

**`#[verifier::external_body]`, `assume`, and `admit` are FORBIDDEN** except where truly unavoidable (e.g., calling external C libraries). If you must use them, **always report it** to the user.

The goal is **full end-to-end verification**—if something can't be verified, tell the user rather than papering over it with external_body, assume(false), or admit.

**It's okay if something is hard.** Take your time, work through it incrementally:
1. Build helper functions and lemmas
2. Check your work along the way
3. If stuck, break into smaller subtasks

**Hard problems are solvable.** Don't reach for `assume(false)` or `admit` just because something is difficult. Take time to break it down, build helper lemmas, and work through it incrementally. Verification rewards persistence.

**Take your time.** Verification is slow and methodical. Don't rush to use `assume(false)` or skip lemmas due to time pressure. Quality over speed.

**When in doubt, ask the user.** Hard design questions, unclear requirements, or architectural choices belong in conversation. But respect their time—try to solve it yourself first.

**Plan first, make a todo list.** Before writing any code:
1. Read the existing code and understand the patterns
2. Break the task into small, verifiable steps
3. Write the todo list and verify each step before moving on
4. Check your work incrementally with `verus_check` on individual modules

**Build shared lemmas.** If a helper lemma would be useful across crates, add it to the appropriate library rather than working around it locally.

**Report recommendations.** When done, include suggestions for polish, architectural improvements, remaining work, and preferred follow-up changes.

**Flag suspicious code.** If code you write seems like a workaround, overly complex, or could be cleaner, report it as technical debt worth addressing.

---

---

## 1. Quick Reference

### Function Modes
```rust
spec fn ...    // Mathematical, ghost, no side effects
proof fn ...   // Verification proofs, ghost
fn ...         // exec mode (default), compiled to Rust
```

### Basic Specification
```rust
fn add_one(x: u32) -> (y: u32)
    requires x < 0xFFFF_FFFF
    ensures y == x + 1
{ x + 1 }
```

### Proof Block / Assert By
```rust
proof { lemma_min(10, 20); }           // lemma result available after

assert(x == y) by { lemma_equal(x, y); }  // only x==y leaks out
```

### Recursive Spec with Fuel
```rust
proof { reveal_with_fuel(triangle, 11); }
assert(triangle(10) == 55);
```

### Loop with Invariant
```rust
while idx < n
    invariant idx <= n, sum == triangle(idx as nat),
    decreases n - idx
{ ... }
```

### Quantifier with Trigger
```rust
forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] > 0
```

### Key Attributes
| Attribute | Use |
|-----------|-----|
| `#[verifier::external_body]` | Call unverified code |
| `#[verifier::opaque]` | Hide spec function body |
| `#[verifier::type_invariant]` | Auto-enforced invariant |
| `#[verifier::memoize]` | Cache compute results |

---

## 2. When to Use What

### spec fn vs proof fn vs fn (exec)

| Use | spec fn | proof fn | fn |
|-----|---------|----------|-----|
| Define mathematical specs | ✓ | | |
| Prove properties | | ✓ | |
| Executable code | | | ✓ |

### Which Solver?

| Situation | Solver |
|-----------|--------|
| Bitwise ops, truncation | `by(bit_vector)` |
| Symbolic mult/div | `by(nonlinear_arith)` |
| Congruences, mod | `by(integer_ring)` |
| Unroll recursive fns | `by(compute)` |

### Loop vs Recursion

| Use loop when | Use recursion when |
|---------------|-------------------|
| Simple invariants | 20+ iterations |
| Few pass-through facts | Quadratic `forall\|i,j\|` |
| | Heavy per-step computation |

### reveal vs reveal_with_fuel vs hide

| Directive | Effect |
|-----------|--------|
| `reveal(f)` | Unfold once |
| `reveal_with_fuel(f, n)` | Unfold recursive f n times |
| `hide(f)` | Treat as uninterpreted |
| `#[verifier::opaque]` | Hide by default |

---

## 3. Core Concepts

### Integer Types
| Type | Use |
|------|-----|
| `int` | Spec code (default, SMT-optimized) |
| `nat` | Spec when non-negativity needed |
| `u8..u128`, `i8..` | Exec code |

**Arithmetic:** Ghost code: `+,-,*` never overflow. Exec code: overflow must be proven impossible.

### Equality
- Ghost: `==` is equivalence relation
- Exec: `==` calls `PartialEq::eq()`
- Collections: use `=~=` (extensional)

### Function Signatures
```rust
fn name(arg: u32) -> (ret: u64)
    requires arg < 100
    ensures ret == f(arg)
    no_unwind when arg < 100

proof fn lemma(x: int)
    requires x < y
    ensures x + 1 <= y

spec fn abs(n: int) -> int
    decreases n.abs()
{ if n < 0 { -n } else { n } }
```

### Loop Invariants (3 requirements)
1. Hold on initial entry
2. Maintained at end of each iteration
3. Strong enough to prove postcondition

**Loop invariant inheritance:** Loops don't auto-inherit preconditions—repeat them.

### Decreases Clause
Required for recursive spec functions. Use `via` clause for separate termination proof:
```rust
spec fn f(n: u64) -> int
    decreases n
    via f_decreases_proof
{ ... }

#[via_fn]
proof fn f_decreases_proof(n: u64) {
    assert(n > 1 ==> (n >> 1) < n) by(bit_vector);
}
```

### Collections (Seq, Set, Map)
```rust
Seq::new(5, |i| 10 * i)   // construction
s.len(), s[i], s.push(v)    // Seq ops
s.contains(x), s.insert(x) // Set ops
m.dom(), m[k], m.insert(k, v) // Map ops
v@                             // Vec to Seq view
```

### Algebraic Trait Hierarchy
```rust
trait Ring { eqv, add, sub, neg, mul, zero, one }
trait OrderedRing : Ring { le, lt, lemma_trichotomy }
trait OrderedField : OrderedRing { div, recip }
```

### Runtime Layer Pattern
```rust
struct RuntimeVec2<R> {
    coords: (R, R),
    model: Ghost<Vec2<R>>,  // spec abstraction
}

fn add_exec(a: &RuntimeVec2<R>, b: &RuntimeVec2<R>) -> (r: RuntimeVec2<R>)
    ensures r.model@ === a.model@.add(b.model@)
```

### Key Lemma Patterns
```rust
// Trichotomy: exactly one of a<b, a===b, b<a
lemma_trichotomy(a, b)

// Equivalence chains
axiom_eqv_symmetric(a, b)     // flip direction
axiom_eqv_transitive(a, b, c) // chain

// Negation
neg_involution(a)  // a.neg().neg() === a
```

### Broadcast Lemmas (Ambient Facts)
```rust
broadcast proof fn seq_contains_after_push<A>(s: Seq<A>, x: A)
    requires s.contains(x)
    ensures s.push(v).contains(x)
{ }
use broadcast seq_contains_after_push;  // auto-applies
```

### choose (Witness Extraction)
```rust
let w = choose |i| s[i] > 10;
assert(s[w] > 10);
```

---

## 4. Patterns & Techniques

### Post-Phase Check Loop
Verify properties AFTER construction, not during:
```rust
let mut check: usize = 0;
while check < hcnt
    invariant forall|k| 0 <= k < check ==> twin(twin(k)) == k
{
    if half_edges[twin(check)].twin != check { return Err(...); }
    check += 1;
}
```

### Ghost Snapshot Chaining
```rust
let ghost post_phase_b = half_edges@;
// ... modifications ...
let ghost pre_phase_d = half_edges@;

// Chain in proof:
assert(mesh.half_edges@[h].next == pre_phase_d[h].next);
assert(pre_phase_d[h].next == post_phase_b[h].next);
```

### Frame Invariant (Unchanged Fields)
```rust
forall|k| hcnt ==> {
    half_edges@[k].next == post_phase_b[k].next
    half_edges@[k].prev == post_phase_b[k].prev
}
// After set():
by { if k == h as int {} else { assert(half_edges@[k] == pre_set[k]); } }
```

### Opaque Spec for Recursive Fns
```rust
#[verifier::opaque]
spec fn heavy_spec(...) { ... }

proof fn caller() {
    reveal(heavy_spec);  // unfold only where needed
}
```

### Roundtrip Contradiction for Injectivity
```rust
if linearize(c) == linearize(d) {
    lemma_roundtrip(c, shape);
    lemma_roundtrip(d, shape);
    assert(false);  // c =~= d contradiction
}
```

### Extract `assert forall` with Function Calls
```rust
// BAD
assert forall |i| P(i) implies Q(i) by { lemma_heavy(i); }

// GOOD: extract lemma first
proof fn helper(i) requires P(i) ensures Q(i) { ... }
assert forall |i| P(i) implies helper(i) { }
```

### Breaking Long Proofs
```rust
// Extract to lemma
proof fn part1(x) requires r ensures mid1 { P1; }
proof fn part2(x, y) requires mid1 ensures mid2 { P2; }
proof fn part3(x, y) requires mid2 ensures e { P3; }
```

---

## 5. Common Errors & Fixes

### "assertion failed"
1. Run with `--expand-errors`
2. Add `assume(postcondition)` to check structure
3. Add `assert(midpoint)` to narrow down
4. Check quantifier triggers

### "possible arithmetic overflow"
1. Add precondition: `requires x <= u64::MAX - y`
2. Use runtime checks: `x.checked_add(y)`
3. Use `CheckedU64` type

### "rlimit exceeded"
**NEVER just increase rlimit.** Instead:
1. Profile: `verus --profile module`
2. Look for quantifier instantiation storms
3. Extract expensive blocks into helpers (Z3 context per function)
4. Expand/inline proof steps to help Z3 along
5. Simplify triggers

### "cannot prove termination"
1. Add `decreases` clause
2. Use `via` clause with termination proof
3. Add inline: `proof { assert(decreases_condition); }`

### Quantifier trigger loop
```rust
// BAD: causes infinite matching
forall |i| 0 <= i < n - 1 ==> #[trigger] s[i] <= s[i + 1]

// GOOD: two-variable
forall |i, j| 0 <= i <= j < n ==> s[i] <= s[j]
```

---

## 6. Common Pitfalls

### No f32/f64 Support
Verus does not support `f32` or `f64` - using them causes Verus to panic. Use rational types (e.g., `Rational`, `BigInt`) or custom fixed-point implementations instead.

### Ghost `let` Not in Loop Body
```rust
// BAD: x not available in loop
let ghost x = Seq::new(n, f);
while i < n { assert(x[i] == f(i)); }  // FAILS

// GOOD: use invariant
while i < n
    invariant forall|j| 0 <= j < n ==> x[j] == f(j)
```

### Or Patterns in Spec Match
```rust
// BAD: breaks Z3 extraction
A { .. } | B { .. } => ...

// GOOD: separate arms
A { .. } => { let x = children; ... }
B { .. } => { let x = children; ... }
```

### nat vs usize Fuel
```rust
// Bridge inside assert forall:
assert forall |i| ... by {
    assert((fuel as nat - 1) as nat == (fuel - 1) as nat);
}
```

### Cast Identity (Platform-Dependent)
```rust
let len = vec.len();  // capture as usize
assert((val as int) < (len as int));  // works
```

### eqv() Direction
```rust
// neg_involution gives a.neg().neg() === a
// NOT a === a.neg().neg()
// Use axiom_eqv_symmetric to flip
```

### Seq::new vs Seq::map
```rust
// Seq::new unfolds better
Seq::new(len, |i| seq[i]@)

// Seq::map may not unfold
seq.map(|_i, p| p@)
```

### Helper Functions Pollute Module Triggers
Adding a helper to a module affects ALL functions in that module. Put proof helpers in separate files (e.g., `proofs.rs`).

### Lemma Ordering
Reflexive axioms MUST come before congruence/transitive: `axiom_eqv_symmetric` before `axiom_eqv_transitive`.

---

## 7. MCP Tools

**Prefer MCP lookup over reading files.** Use `verus_search`, `verus_lookup`, `verus_batch_lookup`, etc. instead of direct file reads when looking up functions or types. Lookups are recorded in context across compactions for future reference.

**Note on function counts.** The indexed counts (spec/proof/exec) exclude spec functions that are transparent and don't require verification - only functions that Verus actually checks are counted.

The "N verified" count includes proof fn and exec fn (both require proof obligations). Spec fn bodies are treated as definitions/axioms, not proof obligations - they are NOT counted. Recommends clauses are not checked by default (enable with `#[verifier::recommends_check]` to include).

| Function mode | Has proof obligation? | Counted? |
|---------------|------------------------|----------|
| spec (open/closed) | No (body is a definition) | No |
| proof | Yes (requires/ensures) | Yes |
| exec | Yes (requires/ensures) | Yes |

### Verification Workflow
- **Check early and often** - verify after each logical unit
- **Keep changes small** - incremental edits are easier to debug
- **Build helpers up** - create smaller lemmas, check each one
- **Don't use `raw=True`** on `verus_check` - it's very verbose and fills context; rarely needed
- **No need to clean builds** - Verus is reproducible and builds are always up to date

### Session Start Workflow
```bash
# 1. List existing contexts
verus_context_list()

# 2. Activate or create context
verus_context_activate("my-task")  # creates if new

# 3. Search for functions
verus_search("orient2d")
verus_search_ensures("div.*mul")  # regex support
verus_search_requires("三角")
```

**Use specific context names.** E.g., `"verus-topology-delaunay"` rather than `"topology"`. Specific names help future sessions find relevant context.

### Function Lookup
```bash
verus_lookup("lemma_fib_monotonic")    # full signature
verus_lookup_source("triangle")       # source code
verus_batch_lookup(["fn1", "fn2"])    # up to 10
```

### Verification
```bash
verus_check("verus-geometry")         # verify crate
verus_check("verus-topology", "module") # verify module only
verus_profile("verus-gui")            # performance profile
```

### Search Functions
```bash
verus_search("orient2d")                   # name substring
verus_search("orient*")                    # * wildcard supported
verus_search_doc("computes orientation")  # doc comments
verus_search_signature(param_type, return_type)  # by type
verus_search_trait("TotalOrdered")          # trait + impls
verus_find_dependencies("lemma_name")       # callers/callees
```

### Profiling
```bash
verus_profile("crate", top_n=25)  # sorted by rlimit
# Use rlimit (deterministic), not SMT time (2x variance)
```

---

## 8. Workspace Overview

### Core Foundation Crates

**verus-algebra** (~420 fns)
- Core traits: `Ring`, `OrderedRing`, `OrderedField`
- Lemmas for add/mul associativity, distributivity, congruence
- Summation, binomial coefficients, convex combination

**verus-bigint** (~328 fns)
- Arbitrary-precision integers, signed/unsigned
- Zero-trust implementation with machine-checked proofs

**verus-rational** (~328 fns)
- Exact rational arithmetic
- RationalModel type for specs

**verus-linalg** (~772 fns)
- `Vec2<T>`, `Vec3<T>`, `Vec4<T>` - generic over Ring
- `Mat2x2<T>`, `Mat3x3<T>`, `Mat4x4<T>`, `Quat<T>`
- Runtime counterparts: `RuntimeVec2`, `RuntimeMat3x3`, etc.

### Geometry & Topology

**verus-geometry** (~761 fns)
- **Predicates**: orient2d, orient3d, incircle, insphere, collinear, coplanar, sidedness
- **Geometry types**: Point2/3, Circle2, Line2, Polygon, Segment
- **Intersection**: segment-segment, segment-triangle, triangle-triangle
- **2D algorithms**: convexity, Delaunay triangulation, Voronoi
- **Closest point**: point-to-segment, segment-to-segment distance
- **Area/winding**: signed area, winding number, point-in-polygon
- **Runtime**: verified runtime implementations with RationalModel

**verus-topology** (~273 fns)
- **Core**: HalfEdge, Mesh structs
- **Construction**: from face cycles, tetrahedron, cube
- **Euler operators**: split_edge, split_face, flip_edge, collapse_edge
- **Invariants**: twin_involution, prev_next_bidirectional, face_representative_cycles, vertex_manifold
- **Queries**: face_degree, vertex_degree, euler_characteristic, genus
- **Connectivity**: is_connected, check_connected
- **Delaunay**: Lawson flip algorithm in 2D
- **Point in solid**: ray crossing algorithm

### Graphics & Rendering

**verus-gui** (~981 fns)
- **Layouts**: linear (stack), flex, grid, wrap, absolute, scroll
- **Text model**: cursor, selection, word wrap, undo/redo
- **Draw commands**: flatten_node_to_draws, draw state
- **Widget system**: RuntimeWidget hierarchy
- **Animation**: frame loop, event routing
- **Cache**: RuntimeLayoutCache for incremental layout

**verus-canvas** (~86 fns)
- 2D canvas drawing inspired by Raph Levien's Vello pipeline
- **Scene**: PathSegment, Shape, Paint, Graphic tree
- **Flatten**: transform composition, bbox, z-order
- **Bezier**: de Casteljau subdivision, path flattening
- **Tile**: 16x16 tile binning with conservativeness proofs
- **Blend**: Porter-Duff source-over compositing

**verus-ray-marching** (~45 fns)
- Ray-sphere, ray-plane, ray-box, ray-cylinder intersection
- SDF fractals: menger, sierpinski, mandelbulb, torus, pyramid
- CSG operations, scene composition
- GPU workgroup dispatch for parallel rendering

**verus-mandelbrot** (~52 fns)
- Infinite zoom Mandelbrot with exact rational arithmetic
- Perturbation theory, series approximation for acceleration
- Depends on: verus-bigint, verus-rational, verus-interval-arithmetic

**verus-vulkan** (~3673 fns)
- Vulkan API bindings - not verified (external_body)
- Used as runtime backend for GPU operations

### Algebra & Number Theory

**verus-quadratic-extension** (~83 fns)
- Exact quadratic extension arithmetic F(root(d))
- `SpecQuadExt<F, R>` representing `re + im*root(d)`
- Field instances: sqrt2, sqrt3, sqrt5, etc.
- Dynamic tower extensions, extensive proof lemmas

**verus-field-extension** (~14 fns)
- Algebraic field extensions F[x]/(P) where P is irreducible polynomial
- `SpecExt<F, P>` - field extension element as coefficient vector
- Example: `CubeRoot2` (Q(cuberoot(2)))

**verus-interval-arithmetic** (~193 fns)
- Precise interval arithmetic using BigInt rationals
- Ghost spec functions: add_spec, mul_spec, div_spec, etc.
- ~100+ proof lemmas for all operations
- Runtime: `RuntimeInterval` with bisect, horner_eval, etc.

**verus-group-theory** (~397 fns)
- Extensive formal group theory library
- Core: symbol, word, reduction, group, subgroup, presentation
- Constructions: free_product, hnn, amalgamated_free_product, coset_group
- Algorithms: todd_coxeter, tietze, schreier
- Proofs: britton, britton_proof, schreier_proofs, completeness

### CAD & Constraints

**verus-2d-constraint-satisfaction** (~332 fns)
- Formally verified 2D constraint satisfaction for CAD
- **Entities**: EntityId, FreePoint, FixedPoint, ResolvedPoints
- **Locus**: geometric locus computation
- **Solver**: constraint solver with pipeline architecture

### GPU Kernel Building

**verus-cutedsl** (~840 fns)
- NVIDIA CuTe layout algebra for verified GPU kernels
- **Shape**: Shape as Seq<nat>, size, delinearize, linearize
- **Layout**: LayoutSpec (shape + stride), offset, cosize
- **Composition**: layout composition A(B(x))
- **Operations**: complement, divide, product, swizzle, tiling
- **Algorithms**: scan (blelloch, brent_kung, multiblock), radix_sort
- **GEMM**: matrix multiplication layouts, tensor contraction

### Computability & Logic

**verus-computability-theory** (~84 fns)
- CEERs (computably enumerable equivalence relations)
- Register machine, computable functions
- ZFC set theory foundations
- Group theory connection: CEER to group embedding, Higman's theorem

### Developer Tools

**verus-mcp** (Rust binary, ~50 fns)
- MCP server indexing all Verus spec/proof/exec functions
- Provides: search, lookup, search_ensures, search_requires
- Tree-sitter based Verus parser
- Verification tools: verus_check, verus_profile, etc.

**verus-docgenerator** (~39 fns)
- Documentation generator for Verus code
- Tree-sitter parsing, extracts spec functions and lemmas
- Generates markdown documentation
