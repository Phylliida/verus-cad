# Comprehensive Guide to Reducing Verus Rlimit Usage

## Table of Contents
1. [Measuring Performance](#measuring-performance)
2. [Quick Wins (Try First)](#quick-wins)
3. [Opaque + Reveal](#opaque--reveal)
4. [Breaking Proofs into Smaller Pieces](#breaking-proofs-into-smaller-pieces)
5. [Module Splitting](#module-splitting)
6. [Loop Optimization](#loop-optimization)
7. [Quantifier Management](#quantifier-management)
8. [Proof by Computation](#proof-by-computation)
9. [Anti-Patterns (Things That Make It Worse)](#anti-patterns)
10. [Decision Flowchart](#decision-flowchart)

---

## Measuring Performance

### Use the MCP `profile` tool (preferred)

The primary way to measure rlimit in this project is the **Verus MCP server's `profile` tool**:

```
profile(crate_name)                  # Full crate — per-function rlimit table sorted by cost
profile(crate_name, module)          # Single module — faster iteration
profile(crate_name, module, top_n)   # Limit to top N functions
```

This runs `cargo verus verify` with profiling flags and returns a clean per-function rlimit breakdown. Use it to:
1. **Identify hot functions** — profile the whole crate, look at the top 25
2. **Isolate a module** — profile just that module for faster feedback
3. **Measure optimization impact** — profile before and after a change, compare rlimit numbers

**Always use rlimit (deterministic) not SMT time (2x variance between runs) to measure optimization impact.**

### Raw Verus CLI flags (for reference)

If you need to run Verus directly outside the MCP server:
```
verus --time           # Per-function time + rlimit breakdown
verus --time-expanded  # More detail
verus --output-json    # Machine-readable
```

### Quantifier profiling
When a function times out or is slow, run Verus directly with `--profile --rlimit 1`:
- Shows per-quantifier instantiation counts and costs
- Cost metric: sum of downstream instantiation work caused by each quantifier
- High instantiation count + high cost = the culprit
- If ALL quantifiers have small counts, quantifiers aren't your problem — look elsewhere
- Use `--profile-all` + `--verify-function` to profile a function that verifies successfully but slowly

### Profiling workflow
1. `profile(crate_name)` — identify top-N hot functions
2. `profile(crate_name, module)` — isolate the module
3. Make a change
4. `profile(crate_name, module)` again — compare rlimit (not SMT time)

---

## Quick Wins

### 1. `assert(...) by { ... }` — Isolate subproofs

The single most impactful local change. Facts introduced inside `by { ... }` are **not visible** to the rest of the function.

```rust
//  BAD: lemma_B's facts pollute the entire function
lemma_A();
lemma_B();  //  introduces forall|i: int| b(i)
assert(F);  //  solver thinks about b(i) here too
assert(G);  //  ...and here

//  GOOD: lemma_B's facts scoped to proving F only
lemma_A();
assert(F) by { lemma_B(); };
assert(G);  //  solver only knows about lemma_A's facts
```

**When to use**: Any time you call a lemma (especially one with quantified ensures) that's only needed for one subsequent assertion.

### 2. `calc!` — Structured transitive proofs

Chains `a R b R c R ... R z` without repeating intermediate expressions and without polluting outer context:

```rust
calc! {
    (<=)
    x;     { /* proof x <= x + 3 */ }
    x + 3; { /* proof x + 3 <= 5 */ }
    5;
}
//  Outer context only sees: x <= 5
```

Supports mixed relations: `(<=)` top-level with `(==)` or `(<)` inline for individual steps.

### 3. Mirror spec structure in exec

If the spec already factors a computation into helpers, the exec should too. Z3 works best when exec structure mirrors spec structure — each exec helper's ensures directly references its spec counterpart.

**Example**: A spec `undo_splice_params_full` had 7-arm match. The exec originally inlined all 7 arms in one function (53.6M rlimit). Extracting to match the spec: 14.1M (-74%).

---

## Opaque + Reveal

Mark a spec function `#[verifier::opaque]` to prevent Z3 from auto-unfolding its body. Use `reveal(fn_name)` where you need the definition.

```rust
#[verifier::opaque]
spec fn complex_layout(widget: Widget) -> LayoutResult { ... }

//  In exec:
proof { reveal(complex_layout); }
assert(result@ == complex_layout(widget@));
```

### When opaque works well (big wins)

| Scenario | Example | Savings |
|----------|---------|---------|
| **Narrowly-used specs (≤6 callers)** | Stack layout specs (6 callers) | -74% on target |
| **Complex dispatcher targets** | 15-arm `layout_widget` match no longer unfolds each sub-layout | -59% on dispatcher |
| **Recursive specs with heavy bodies** | Group theory induction specs | 90M → instant |

### When opaque fails (wash or regression)

| Scenario | Why | Example |
|----------|-----|---------|
| **Widely-used specs (18+ callers)** | Reveal overhead accumulates | Column/row helpers: -0.15% net |
| **Specs used in loop invariants** | Must `reveal()` inside EVERY loop body | Per-loop reveal cost dominates |
| **Recursive specs tracked by loop structure** | Loop body naturally mirrors recursive case; opaque breaks the connection | `column_children` opaque: +3.0M regression |

### Critical: `reveal()` does NOT propagate into loop bodies

```rust
proof { reveal(my_spec); }  //  Visible here...
while i < n
    invariant
        result@ == my_spec(...)  //  ...but NOT here!
{
    proof { reveal(my_spec); }  //  Must reveal INSIDE the loop
    ...
}
```

### Bridge lemma pattern

When two specs cross-reference each other in proofs: make one opaque, write a proof-only lemma that reveals it and proves the connection. Exec calls the lemma (cheap focused context) instead of Z3 discovering the connection (expensive).

```rust
#[verifier::opaque]
spec fn spec_a(...) -> T { ... }

proof fn lemma_a_matches_b(x: X)
    requires spec_b(x) == some_value
    ensures  spec_a(x) == expected_result
{
    reveal(spec_a);
    //  Small focused proof
}

//  In exec: call lemma_a_matches_b instead of relying on auto-unfolding
```

**Results**: `undo_splice_params_full` opaque + bridge → session module -25% (-15.5M).

### Per-arm bridge lemmas for multi-arm specs

When a spec has N arms and M exec callers each handle 1-2 arms:
1. Make the spec opaque
2. Write per-arm lemmas that reveal + prove output for each arm
3. Each caller invokes only its arm's lemma → SMT goes from O(N) to O(1) arms

**Results**: `apply_key_to_session` (9 bridge lemmas) → session module -26% (-12.2M).

---

## Breaking Proofs into Smaller Pieces

SMT solver response time is **superlinear** in proof size. Twice as many facts → far more than twice the search space. Breaking functions down can be the difference between timeout and instant success.

### Strategy A: Extract a subproof into a lemma

Find a modest-size proof block P that establishes facts S. Move P into a lemma with:
- `requires`: the context P needs
- `ensures`: the facts S it establishes

```rust
//  Before: everything in one function
fn my_long_function(x: u64) {
    ...  //  establishes f(x, y)
    P1; P2; P3; P4;  //  proves s1, s2
    ...  //  uses s1, s2
}

//  After: subproof extracted
proof fn helper(x: u64, y: int)
    requires f(x, y)
    ensures s1(x), s2(x, y)
{
    P1; P4;  //  Often LESS proof needed in focused context!
}

fn my_long_function(x: u64) {
    ...
    helper(x, y);
    ...
}
```

**Key insight**: The lemma often needs LESS proof code than the original inline block, because the solver has a smaller, more focused context.

### Strategy B: Divide proof into sequential parts

Split into n consecutive lemmas that chain: part1's ensures = part2's requires, etc.

```rust
proof fn part1(x: u64) -> (y: int)
    requires r(x)
    ensures mid1(x, y)
{ P1 }

proof fn part2(x: u64, y: int)
    requires mid1(x, y)
    ensures mid2(x, y)
{ P2 }

proof fn part3(x: u64, y: int)
    requires mid2(x, y)
    ensures e(x)
{ P3 }

proof fn original(x: u64)
    requires r(x)
    ensures e(x)
{
    let y = part1(x);
    part2(x, y);
    part3(x, y);
}
```

Consider factoring the intermediate predicates (`mid1`, `mid2`) into spec functions to avoid repetition.

### When extraction works vs. fails

**Works well:**
- Branchy computations (7+ arm match) → path explosion reduction (-86%)
- `assert forall by { proof_fn() }` blocks → quantifier instantiation reduction (-72%)
- Heavy blocks in recursive functions → verified once instead of per-recursion (-83%)
- Parent eliminates cases via early returns (no spec-level precondition needed)

**Fails or washes:**
- Preconditions reference the spec being verified → Z3 must unfold to verify the precondition (+26%)
- Sequential loops without branch explosion → no path products to eliminate
- Cross-module extraction when module has many functions → import pollution offsets savings
- Small proof blocks (< 20 lines) → overhead of requires/ensures verification exceeds savings

---

## Module Splitting

Every function in a module has ALL sibling function bodies in its SMT context. Moving functions to separate modules removes their bodies from siblings' contexts.

### When to split

- Module has 5+ exec functions with 10M+ rlimit each
- Functions are independent (don't share mutual recursion)
- No complex cross-references between functions

### Splitting rules

1. **Move ALL heavy helpers at once** — moving one at a time can regress remaining functions (cross-module reference adds to ALL remaining functions' contexts)
2. **Keep mutually recursive functions together** — they share decreases measures and benefit from each other's bodies
3. **Put proof helpers in separate `_proofs.rs` modules** — isolates trigger pollution from exec code

### Import trimming is useless

Replacing `use crate::layout::*` with named imports has **zero effect** on rlimit. What matters is which function BODIES are in the same module, not import resolution.

### Results from practice

| Split | Before | After | Change |
|-------|--------|-------|--------|
| 6 widget helpers → own modules | 101M | 95.4M | -5.6M |
| 4 measure helpers → measure_helpers.rs | 25.8M | 22.5M | -12.9% |
| 9 event helpers → event_helpers.rs | 17.2M | 15.2M | -11.6% |
| 17 session helpers → session_helpers.rs | 34.5M | 31.1M | -9.7% |

### Caveat: functions that benefit from sibling context

Some functions (especially those in mutual recursion groups or with complex Column/Row branching) **benefit from having sibling function bodies visible**. Flex in its own module: 27.2M (+94%). Flex in widget.rs with siblings: 14.0M. The sibling bodies serve as Z3 "stepping stones."

---

## Loop Optimization

### Recursion over loops (for heavy invariants)

Replace exec `while` loops with tail-recursive exec functions when the loop has many pass-through invariants.

**Why it works**: Loop invariants are the ONLY facts available inside a loop body — function requires are NOT carried in. This forces forwarding all preconditions as invariants. With recursion, `requires` are automatically available in the body.

```rust
//  Before: 24 invariants, 600M rlimit
while index < n
    invariant
        //  10 progress invariants (change each iteration)
        //  14 pass-through foralls (never change, just forwarded)
{
    ...
}

//  After: 25M rlimit (-96%)
fn process_recursive(vec: Vec<T>, index: usize, ...)
    requires
        //  14 pass-through foralls (verified once at call site)
        //  10 progress invariants (verified once at call site)
    ensures ...
    decreases n - index
{
    if index >= n { return; }
    //  Pass-through foralls available for free!
    //  ... do one iteration ...
    process_recursive(vec, index + 1, ...);
}
```

**When to apply**: Loops with ≥13 invariants where ≥40% are pass-through `forall`s about immutable data, especially with quadratic `forall|i,j|`.

**When NOT to apply**: Loops with ≤6 invariants. Tested on GUI layout loops (3-10 children, simple `forall|i|`): all 4 conversions INCREASED rlimit. The function-call overhead exceeds savings when invariants are cheap.

### Nested loops are often cheaper than flattening

A nested inner loop with 5 simple invariants is cheaper for Z3 than adding 1 extra invariant to an outer loop with 20+ clauses.

Z3 rlimit measures **term manipulation**, not algorithmic complexity. An O(n²) nested loop is cheap if inner invariants are simple. Don't flatten to O(n) if it means adding invariants to a heavy outer loop.

### Ghost variable identity in nested loops

Use `=~=` (extensional equality) as an invariant when you need to preserve ghost Seq identity across inner loop iterations:
```rust
invariant ghost_seq =~= original_ghost_seq
```

### Loop extraction: mutually recursive functions can't be extracted

Loops that call mutually recursive functions (e.g., `layout_widget_exec` from `layout_listview_widget_exec`) can't be extracted to helpers — the decreases measure won't work across the call boundary.

---

## Quantifier Management

### Quantifier triggers

Z3 trigger matching is **syntactic**. `stride[j+1]` won't match `stride[k]` for arbitrary `k`. When extracting helpers with quantifier requires:

```rust
//  BAD: stride[j+1] won't match stride[k] in caller
forall|j| 0 <= j < k-1 ==> ... == #[trigger] stride[j + 1]

//  GOOD: use a term the caller naturally produces
forall|j| 1 <= j < k ==> ... #[trigger] rest_shape.take(j) ...
```

### `assert forall` doesn't propagate into loop bodies

Facts established by `assert forall` outside a loop are NOT available inside. Must be stated as loop invariants.

### Ghost `let` not available in loops

```rust
let ghost x = Seq::new(n, f);  //  NOT available inside loop body
//  Must carry as invariant:
while ...
    invariant forall|j| 0 <= j < n ==> x[j] == f(j)
```

### int/nat trigger matching

When a quantifier binds `i: int` with trigger `f(x, i as nat)`, creating `f(x, some_nat)` won't match. Must go through int:
```rust
let i_int: int = some_nat as int;
assert(f(x, i_int as nat) == ...);
```

### Or patterns break Z3 unfolding

```rust
//  BAD: prevents Z3 from extracting match results
A { children, .. } | B { children, .. } => ...

//  GOOD: separate arms
A { children, .. } => ...
B { children, .. } => ...
```

---

## Proof by Computation

For proofs that are "obvious" by computing on concrete values:

```rust
proof fn concrete_pow() {
    //  Z3 can't unroll pow enough by default
    assert(pow(2, 8) == 256) by (compute);       //  Interpreter reduces, Z3 sees `true`
    assert(pow(2, 8) == 256) by (compute_only);   //  Fully deterministic, no Z3 fallback
}
```

### Range proofs
```rust
use vstd::compute::RangeAll;

assert((25..100int).all_spec(|x| p(x as usize))) by (compute_only);
let prop = |x| p(x as usize);
assert(prop(u));  //  Trigger the quantifier
```

### Limitations
- No context from surrounding environment (fully isolated)
- Must be spec-mode expressions only
- Use `#[verifier::memoize]` for functions with overlapping subproblems (e.g., Fibonacci)
- Timeout = `--rlimit` seconds

---

## Anti-Patterns

### DON'T remove "dead" intermediate ghost constructions

Intermediate `Seq::new` constructions create trigger terms (`Seq::new(n, f)[i] == f(i)`) that guide Z3's term rewriting. Removing them forces Z3 to search longer inference chains.

**Example**: Removing 5 "dead" Seq::new from a function → rlimit exceeded (was 18M).

### DON'T add helper functions that pollute module triggers

A helper's ensures clause becomes background axioms for ALL functions in the module. If it mentions common terms, it creates additional trigger matches for unrelated functions.

**Mitigation**: Put helpers in a SEPARATE module (e.g., `_proofs.rs`).

### DON'T remove explicit proof hints to "simplify"

Z3 needs explicit assertions in loop bodies. Removing intermediate assertions INCREASES rlimit because Z3 must find longer inference paths.

**Example**: Removing `assert(prefix_has_positive(..., i+1))`: 7M → 18M.

### DON'T use composite specs in inner loop invariants

Heavy composite specs (10+ conjuncts like `structurally_valid(m)`) in loop invariants are expensive. Pass only the specific conjuncts needed.

### DON'T add spec-unfolding assertions for multi-arm specs

Adding assertions that pre-unfold a spec's specific variant doesn't help — Z3 still has to unfold ALL arms to VERIFY each assertion, then tracks additional terms.

**Example**: Pre-unfolding `layout_widget` for SizedBox variant: 9M → timeout.

### DON'T flatten O(n²) nested loops if inner invariants are simple

Z3 cost = per-iteration invariant checking, not total iterations. A cheap inner loop (5 invariants) nested in an outer loop is cheaper than adding 1 invariant to a 20-clause outer loop.

---

## Decision Flowchart

```
Function is slow (>5M rlimit) or times out
│
├─ Profile with --profile --rlimit 1
│   └─ Quantifier instantiations high?
│       ├─ YES → Fix triggers, reduce quantifier scope, assert-by isolation
│       └─ NO → Problem is elsewhere (unfolding, branches, loop size)
│
├─ Function has multi-arm match (7+ arms)?
│   ├─ YES → Extract arms into helpers (path reduction)
│   └─ Spec has multi-arm match called by many functions?
│       └─ YES → Make spec opaque + per-arm bridge lemmas
│
├─ Function has heavy inline proof block?
│   └─ YES → assert(fact) by { proof } or extract to lemma
│
├─ Function is in a large module (10+ siblings)?
│   └─ YES → Move independent functions to separate module
│
├─ Loop has ≥13 invariants with ≥40% pass-through foralls?
│   └─ YES → Convert to tail recursion
│
├─ Spec function auto-unfolded where not needed?
│   ├─ ≤6 callers → Make opaque + targeted reveal
│   └─ >6 callers → Probably not worth it (reveal overhead)
│
├─ Two specs cross-reference each other?
│   └─ YES → Bridge lemma pattern (opaque one + proof lemma)
│
└─ Proof chains through a ≡ b ≡ c ≡ ... ≡ z?
    └─ YES → Use calc! macro
```

### Rules of thumb

| Technique | Typical savings | Effort |
|-----------|----------------|--------|
| `assert(F) by { ... }` | 20-50% on target block | Low |
| Extract branchy computation | 50-86% on target | Medium |
| Opaque narrowly-used spec | 40-74% on target | Medium |
| Module split | 10-15% on module | Medium |
| Recursion over loops | Up to 96% on target | High |
| Enum stratification | 15-55% on dispatchers | High |
| Bridge lemma pattern | 25-35% on callers | Medium |
| Per-arm bridge lemmas | 25-50% on callers | High |

### Optimization floor

Some costs are irreducible:
- **Multi-arm dispatchers**: ~1.0M per arm floor (15-arm dispatch ≈ 15M minimum)
- **Mutual recursion**: Can't split functions that share decreases measures
- **Loop invariant verification**: Each invariant clause costs something per iteration
- **Widely-used specs (30+ callers)**: Too many reveals to make opaque worthwhile
