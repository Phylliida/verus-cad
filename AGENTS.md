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

---

## 0. First Principles

**`#[verifier::external_body]` and `assume` are FORBIDDEN** except where truly unavoidable (e.g., calling external C libraries).

The goal is **full end-to-end verification**—if something can't be verified, tell the user rather than papering over it with external_body or assume(false).

**It's okay if something is hard.** Take your time, work through it incrementally:
1. Build helper functions and lemmas
2. Check your work along the way
3. If stuck, break into smaller subtasks

**When in doubt, ask the user.** Hard design questions, unclear requirements, or architectural choices belong in conversation. But respect their time—try to solve it yourself first.

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

### Verification Workflow
- **Check early and often** - verify after each logical unit
- **Keep changes small** - incremental edits are easier to debug
- **Build helpers up** - create smaller lemmas, check each one
- **Don't use `raw=True`** on `verus_check` - it's very verbose and fills context; rarely needed

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

*End of Quick Reference*
