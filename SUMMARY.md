# Verus Quick Reference & Guide

## Table of Contents

1. [Quick Reference Cheat Sheet](#1-quick-reference-cheat-sheet)
2. [Core Concepts](#2-core-concepts)
   - [spec vs proof vs exec](#spec-vs-proof-vs-exec)
   - [Function Signatures](#function-signatures)
3. [Types & Arithmetic](#3-types--arithmetic)
4. [Control Flow](#4-control-flow)
   - [Recursion & Termination](#recursion--termination)
   - [Loops & Invariants](#loops--invariants)
5. [Collections: Seq, Set, Map](#5-collections-seq-set-map)
6. [Proof Techniques](#6-proof-techniques)
7. [Advanced Topics](#7-advanced-topics)
8. [Common Errors & Fixes](#8-common-errors--fixes)
9. [Advanced Proof Patterns](#9-advanced-proof-patterns-from-real-projects)
10. [Rlimit Optimization](#10-rlimit-optimization)
11. [Common Pitfalls](#11-common-pitfalls)

---

## 1. Quick Reference Cheat Sheet

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

### Proof Block
```rust
fn exec_fn() {
    proof {
        lemma_min(10, 20);
    }
}
```

### Assert By (scoped proof)
```rust
assert(x == y) by {
    lemma_equal(x, y);
}
// Only x == y leaks out, not lemma internals
```

### Recursive Spec with Fuel
```rust
spec fn triangle(n: nat) -> nat decreases n { ... }

proof { reveal_with_fuel(triangle, 11); }  // unfold 11 times
assert(triangle(10) == 55);
```

### Loop with Invariant
```rust
while idx < n
    invariant
        idx <= n,
        sum == triangle(idx as nat),
    decreases n - idx
{ ... }
```

### Quantifier with Trigger
```rust
forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] > 0
```

### View Operator (@)
```rust
v@                    // Seq view of Vec
expr@                 // shorthand for expr.view()
```

### Key Attributes
| Attribute | Use |
|-----------|-----|
| `#[verifier::external_body]` | Call unverified code |
| `#[verifier::opaque]` | Hide spec function body |
| `#[verifier::type_invariant]` | Auto-enforced type invariant |
| `#[verifier::memoize]` | Cache compute results |

---

## 2. Core Concepts

### spec vs proof vs exec

| Feature | `spec fn` | `proof fn` | `fn` (exec) |
|---------|-----------|------------|-------------|
| Compiled | No | No | Yes |
| Mutation | No | Yes | Yes |
| Can call spec | Yes | Yes | Yes |
| Can call proof | No | Yes | Yes |
| Has requires/ensures | No (recommends) | Yes | Yes |
| Types | `int`, `nat` | ghost/tracked | Rust types |

**When to use:**
- **`spec fn`**: Define mathematical specifications, invariants, abstract state
- **`proof fn`**: Lemmas, inductive proofs, verification conditions
- **`fn` (exec)**: Actual executable code

### Choosing Between Proof Block Forms

| Form | Use When |
|------|----------|
| `proof { lemma(); }` | Lemma result should be available after the block |
| `assert P by { ... }` | Only `P` should be available after, not proof internals |
| `assert forall \|x\| P implies Q by { ... }` | Proving forall with bound variable in scope |

### Variable Modes

| Code Mode | Default | Can Use |
|-----------|---------|---------|
| spec | ghost | ghost only |
| proof | ghost | ghost + tracked |
| exec | exec | ghost + tracked + exec |

```rust
let ghost x = ...;           // Create ghost variable
let tracked t = ...;         // Create tracked variable
let Ghost(val) = Ghost(expr); // Unwrap pattern
let Tracked(val) = Tracked(expr);
```

### Function Signatures

```rust
// Exec function
fn name(arg: u32) -> (ret: u64)
    requires arg < 100
    ensures ret == f(arg)
    no_unwind when arg < 100
{ ... }

// Proof function
proof fn lemma(x: int, y: int)
    requires x < y
    ensures x + 1 <= y
{ ... }

// Spec function
spec fn abs(n: int) -> int
    recommends n >= 0
    decreases n.abs()
{ if n < 0 { -n } else { n } }
```

**Key clauses:**
- `requires` - precondition (checked at call site)
- `ensures` - postcondition (guaranteed on return)
- `decreases` - termination measure (recursive functions)
- `recommends` - soft precondition (diagnostics only)
- `no_unwind when` - unwind guarantee condition

### Ghost Code Properties

Ghost code can:
- Create values of any type (even with private constructors)
- Duplicate values freely
- **Cannot** leak into exec code (compile-time error)

---

## 3. Types & Arithmetic

### Integer Types

| Type | Description | Use Case |
|------|-------------|----------|
| `int` | Arbitrary precision | Spec code (default) |
| `nat` | Non-negative integers | Spec when non-neg needed |
| `u8..u128`, `i8..i128` | Fixed-width | Exec code |
| `usize`, `isize` | Architecture-dependent | Exec code |

**Rule:** Use `int` in specs (SMT-optimized). Use `nat` when you need to assert non-negativity.

### Arithmetic Differences

**Ghost code:** `+`, `-`, `*` never overflow (widened to `int`)

**Exec code:** Overflow must be proven impossible
```rust
// Use runtime checks
x.checked_add(y)  // returns Option

// Or prove bounds
fn safe_add(x: u64, y: u64) -> (r: u64)
    requires x <= u64::MAX - y
    ensures r == x + y
{ x + y }
```

### Euclidean Division

In spec code, `/` and `%` use Euclidean division:
- `a / b` and `a % b` produce unique q, r where `b*q + r == a` and `0 <= r < |b|`
- Remainder is **always non-negative**

```rust
// Examples
5 / 2  == 2      5 % 2  == 1
(-5) / 2 == -2   (-5) % 2 == 1   // Note: remainder is positive!
```

### Coercion with `as`

| Target | Behavior |
|--------|----------|
| `int` | Always valid, no truncation |
| `nat` | Unspecified if negative |
| `u8..usize` | Truncation (lower N bits) |
| `char` | Unspecified if outside valid range |

```rust
let i: int = u as int;      // Always valid
let n: nat = u as nat;       // Only if u >= 0
#[verifier::truncate]        // Silence warns for intentional truncation
let b: u8 = v as u8;
```

### Equality

**Ghost code:** `==` is always an equivalence relation

**Exec code:** `==` calls `PartialEq::eq()`

**Collections:** Use extensional equality:
```rust
s1 =~= s2   // shallow: same elements, same structure
s1 =~~= s2  // deep: recursively compares nested collections
```

### Spec Closures

```rust
let f = |x: int| x + 1;  // Type: spec_fn(int) -> int

Seq::new(5, |i: int| 10 * i)  // Common use in Seq construction
```

---

## 4. Control Flow

### Recursion & Termination

#### Decreases Clause (Required for recursive spec functions)

```rust
spec fn factorial(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { n * factorial((n - 1) as nat) }
}
```

Without `decreases`, nonterminating functions would allow proving `false`.

#### Fuel for Recursive Functions

SMT can't inline deeply. Use `reveal_with_fuel`:
```rust
assert(triangle(10) == 55);  // FAILS - not enough fuel

proof { reveal_with_fuel(triangle, 11); }
assert(triangle(10) == 55);  // succeeds
```

**Default fuel:** 1. Each recursive inlining consumes 1 unit.

#### Lexicographic Decreases

When one parameter doesn't always decrease:
```rust
spec fn ackermann(m: nat, n: nat) -> nat
    decreases m, n  // m first, then n
{ ... }
```

#### Termination Proofs

**Inline proof:**
```rust
spec fn floor_log2(n: u64) -> int
    decreases n
{
    if n <= 1 { 0 }
    else {
        proof { assert(n > 1 ==> (n >> 1) < n) by(bit_vector); }
        floor_log2(n >> 1) + 1
    }
}
```

**Via clause (separate proof function):**
```rust
spec fn floor_log2_via(n: u64) -> int
    decreases n
    via floor_log2_decreases_proof
{ ... }

#[via_fn]
proof fn floor_log2_decreases_proof(n: u64) {
    assert(n > 1 ==> (n >> 1) < n) by(bit_vector);
}
```

### Loops & Invariants

#### Loop Invariants

Three requirements:
1. Hold on initial entry
2. Maintained at end of each iteration
3. Strong enough to prove postcondition

```rust
while idx < n
    invariant
        idx <= n,
        sum == triangle(idx as nat),
    decreases n - idx
{
    idx = idx + 1;
    sum = sum + idx;
}
```

#### Loop Invariant Inheritance

Loops don't auto-inherit preconditions—repeat them in invariant:
```rust
fn loop_triangle(n: u32) -> (sum: u32)
    requires triangle(n as nat) < 0x1_0000_0000  // NOT inherited
{
    while idx < n
        invariant
            triangle(n as nat) < 0x1_0000_0000,  // Must repeat!
        ...
}
```

**Opt out:** `#[verifier::loop_isolation(false)]` on function/module/crate.

#### Break and Return

**Return in loop:** Exit early
```rust
if overflow { return special_value; }
```

**Break with invariant_except_break:**
```rust
while idx < n
    invariant_except_break idx <= n
    ensures sum == triangle(n) || sum == sentinel
{ ... if condition { sum = sentinel; break; } }
```

#### For Loops

```rust
for idx in iter: 0..n
    invariant sum == triangle(idx as nat)
{
    sum = sum + idx + 1;
}
```
- `iter.start`, `iter.cur`, `iter.end` - iterator state
- `iter@` - elements so far (e.g., `seq![0,1,2]`)

---

## 5. Collections: Seq, Set, Map

### Overview

| Type | Description | Size |
|------|-------------|------|
| `Seq<T>` | Ordered sequence | Finite |
| `Set<T>` | Unordered set | Finite or infinite |
| `Map<K, V>` | Key-value mapping | Finite or infinite |

**Key difference from Rust:** Size is `nat` (unbounded).

### Construction

```rust
Seq::new(5, |i: int| 10 * i)     // Seq with 5 elements
set![1, 2, 3, 4, 5]              // Set literal
map![1 => 10, 2 => 20]            // Map literal
```

### Common Operations

```rust
// Seq
s.len()                  // nat
s[i]                     // index (returns A)
s.push(v)               // new Seq with v appended
s.take(n)               // first n elements
s.drop(n)               // elements after n
s.subrange(i, j)        // elements [i, j)
s =~= t                  // extensional equality

// Set  
s.contains(x)           // bool
s.insert(x)             // new Set
s.remove(x)             // new Set
s.intersection(t)       // intersection
s.union(t)              // union
s.is_empty()            // bool

// Map
m.dom()                 // domain as Set
m.contains_key(k)      // bool
m[k]                    // get value
m.insert(k, v)         // new Map
```

### Vec and @ Operator

Vec is exec-only; use `@` to get Seq view:
```rust
let mut v: Vec<u32> = Vec::new();
v.push(42);
assert(v@ =~= seq![42]);
assert(v@[0] == 42);
```

**Best practice:** Write specs using Seq/Set/Map, not Vec.

---

## 6. Proof Techniques

### Debugging Proofs

**Process:**
1. Add `assume(postcondition)` → if verifies, issue is in proof
2. Move `assume` into branches to isolate
3. Replace `assume` with `assert` to see failure
4. Add needed lemmas/assertions

```rust
// Start: assumes to check structure
assume(final_result_is_correct);

// Then narrow down
if condition {
    assert(goal1);
} else {
    assert(goal2);
}
```

### Induction Proofs

Write as recursive proof functions:
```rust
proof fn lemma_fib_monotonic(i: nat, j: nat)
    requires i <= j
    ensures fib(i) <= fib(j)
    decreases j
{
    if j < 2 { }  // base cases
    else {
        lemma_fib_monotonic(i, (j - 1) as nat);
    }
}
```

### forall with assert-by

```rust
assert forall |i: int| P(i) implies Q(i) by {
    // i is in scope here
    reveal(spec_fn);
    assert(Q(i));
}
```

### choose (Witness Extraction)

```rust
proof fn demo(s: Seq<int>)
    requires exists |i| s[i] > 10
{
    let w = choose |i| s[i] > 10;
    assert(s[w] > 10);
}
```

### Broadcast Lemmas (Ambient Facts)

Make lemmas always available:
```rust
broadcast proof fn seq_contains_after_push<A>(s: Seq<A>, v: A, x: A)
    requires s.contains(x)
    ensures s.push(v).contains(x)
{ }

use broadcast seq_contains_after_push;  // auto-applies
```

### calc! Macro (Structured Proofs)

```rust
calc! {
    (==)
    x + y; {}
    y + x; {}  // commutative
    2 * x; {}
}
// Proves x + y == 2 * x
```

### Breaking Long Proofs

**Extract to lemma:**
```rust
// Before
P1; P2; P3;  // establishing s1, s2

// After
proof fn helper(x, y) requires f(x,y) ensures s1, s2 { P2; P3; }
my_fn() { P1; helper(x, y); ... }
```

**Pipeline:**
```rust
proof fn part1(x) requires r ensures mid1 { ... }
proof fn part2(x, y) requires mid1 ensures mid2 { ... }
proof fn part3(x, y) requires mid2 ensures e { ... }
```

### Specialized Solvers

| Solver | Use When |
|--------|----------|
| `by(bit_vector)` | Bitwise ops, truncation, concrete bitwidths |
| `by(nonlinear_arith)` | Multiplication/division of symbolic values |
| `by(integer_ring)` | Congruences, modular arithmetic |
| `by(compute)` | Unroll recursive functions |

```rust
assert(x * y <= 100) by(nonlinear_arith)
    requires x <= 10, y <= 10;

assert(b & 7 == b % 8) by(bit_vector);

proof fn mod_congruence(a, b, c, n) by(integer_ring)
    requires a % n == b % n
    ensures (a * c) % n == (b * c) % n
{ }
```

---

## 7. Advanced Topics

### Type Invariants

Auto-enforced invariants for封装:
```rust
#[verifier::type_invariant]
spec fn well_formed(self) -> bool {
    self.min <= self.max
}
```

Verus checks invariant at construction and modification. Client code can assume it:
```rust
proof { use_type_invariant(&x); }
assert(x.min <= x.max);
```

### External Code Integration

**Call unverified code:**
```rust
#[verifier::external_body]
fn fast_fib(n: u64) -> (r: u64)
    requires fib(n as nat) <= u64::MAX
    ensures r == fib(n as nat)
{ ... }  // Unverified impl
```

**Apply specs to existing functions:**
```rust
assume_specification<T>[core::mem::swap::<T>](a: &mut T, b: &mut T)
    ensures *a == *old(b), *b == *old(a);
```

### Uninterpreted Spec Functions

Functions with known signature but unknown behavior:
```rust
uninterp spec fn my_fun(x: int, y: int) -> int;

// Axioms about it:
broadcast proof fn my_fun_property()
    ensures forall |x| my_fun(x, x) == x
{ }
```

### Memory Safety

**Interior mutability:** Use `InvCell<T>` with invariant:
```rust
fn memoized(cell: &InvCell<Option<u64>>) -> (res: u64)
    requires cell.inv(...)
{
    match cell.get() {
        Some(i) => i,
        None => {
            let i = expensive_computation();
            cell.replace(Option::Some(i));
            i
        }
    }
}
```

### Traits with Specifications

```rust
trait TotalOrdered {
    spec fn le(self, other: Self) -> bool;
    
    proof fn transitive(x, y, z: Self)
        requires Self::le(x, y), Self::le(y, z)
        ensures Self::le(x, z);
}
```

### Unwinding

```rust
fn get_unchecked(s: &str, i: usize) -> (c: char)
    ensures if i < s.len() { c == s[i] } else { true }
    no_unwind when i < s.len()
{ ... }
```

**Cannot unwind when invariant is open.**

### Ghost Erasure

```rust
#[cfg(verus_only)]
use crate::ghost_module::ghost_fn;  // Erased at compile time
```

### Global Layout Directive

```rust
global layout usize is size == 8;  // On 64-bit platform
global layout MyStruct is size == 16, align == 8;
```

---

## 8. Common Errors & Fixes

### "assertion failed"

**Debugging steps:**
1. Run with `--expand-errors`
2. Check if preconditions are satisfied
3. Add intermediate `assert` statements
4. Verify quantifier triggers are correct
5. Try specialized solvers (`by(bit_vector)`, `by(nonlinear_arith)`)

### "possible arithmetic overflow"

**Fixes (in order of preference):**
1. Add precondition ensuring result fits
2. Use `checked_*` functions
3. Use `CheckedU64` type for overflow-free arithmetic
4. Add explicit bounds check at runtime

```rust
// Instead of:
x + y  // might overflow

// Use:
x.checked_add(y)  // returns Option

// Or prove it can't overflow:
fn safe_add(x: u64, y: u64) -> (r: u64)
    requires x <= u64::MAX - y
{ x + y }
```

### "rlimit exceeded"

**Solutions:**
1. Profile: `verus --profile ...`
2. Check for quantifier instantiation storms
3. Break proof into smaller lemmas
4. Increase rlimit: `#[verifier::rlimit(100)]`
5. Make triggers more selective

### "cannot prove termination"

**Fixes:**
1. Add `decreases` clause
2. Provide termination proof with `via` clause
3. Use `proof { assert(decreases_condition); }` inside function

### Quantifier instantiation issues

**Problem:** "trigger loop" or infinite instantiation

**Fix:** Avoid matching loops in triggers
```rust
// BAD: causes infinite matching
forall |i| 0 <= i < n - 1 ==> #[trigger] s[i] <= s[i + 1]

// GOOD: two-variable quantification
forall |i, j| 0 <= i <= j < n ==> s[i] <= s[j]
```

### Struct/Enum equality not working

**Use extensional equality:**
```rust
s1 =~= s2  // instead of s1 == s2
```

Or mark type:
```rust
#[verifier::ext_equal]
struct Foo { ... }
```

### Recursive spec function not inlining enough

**Use `reveal_with_fuel`:**
```rust
proof { reveal_with_fuel(my_recursive_fn, N); }
assert(my_recursive_fn(k) == expected);
```

### When to use `reveal` vs `reveal_with_fuel` vs `hide`

| Directive | Effect |
|-----------|--------|
| `reveal(f)` | Unfold f's definition once |
| `reveal_with_fuel(f, n)` | Unfold recursive f n times |
| `hide(f)` | Treat f as uninterpreted |
| `#[verifier::opaque]` | Keep body hidden by default |

---

## 9. Advanced Proof Patterns (from Real Projects)

### Post-Phase Check Loops

Instead of maintaining complex invariants through a multi-phase construction algorithm, add a **verification loop AFTER** the construction to check properties element-by-element. Each iteration verifies one element, reducing Z3's workload.

```rust
// Instead of threading twin_involution through Phase C:
// Add a check loop AFTER Phase C:
let mut check: usize = 0;
while check < hcnt
    invariant
        forall|k| 0 <= k < check ==> twin(twin(k)) == k,
{
    if half_edges[twin(check)].twin != check { return Err(...); }
    check += 1;
}
```

**Why this works:** Z3 only proves one iteration at a time, not the entire algorithm.

### Ghost Snapshot Chaining

Capture ghost state between phases, then chain through in the final proof:
```rust
let ghost post_phase_b = half_edges@;
// ... Phase C modifies twin field ...
let ghost pre_phase_d = half_edges@;
// ... Phase D modifies edge field ...

// In end proof:
assert(mesh.half_edges@[h].next == pre_phase_d[h].next);  // Phase D frame
assert(pre_phase_d[h].next == post_phase_b[h].next);       // Phase C frame
```

### Frame Invariant Pattern

When modifying one field, prove all other fields unchanged:
```rust
// Track that fields 0,1,2 are unchanged
forall|k| 0 <= k < hcnt ==> {
    half_edges@[k].next == post_phase_b[k].next
    half_edges@[k].prev == post_phase_b[k].prev
}

// After set(), prove frame:
by { if k == h as int {} else { assert(half_edges@[k] == pre_set[k]); } }
```

---

## 10. Rlimit Optimization

**Core principle:** Help Z3, don't just increase rlimit.

### Extract Branchy Computations

Functions with many if-else branches cause path explosion. Extract into helpers:
```
7-way branch: 63 paths → 19 paths (-86% rlimit)
```

### Extract `assert forall` with Function Calls

Calling proof fns inside `assert forall by { ... }` is expensive. Extract the lemma first:
```rust
// BAD: calls lemma inside forall
assert forall |i| P(i) implies Q(i) by {
    lemma_heavy(i);  // expensive per i
}

// GOOD: call extracted lemma
proof fn helper(i: int) requires P(i) ensures Q(i) { ... }
assert forall |i| P(i) implies helper(i) { }
```

### Opaque Specs for Recursive Functions

When a recursive spec passes through requires, Z3 unfolds it at every step:
```rust
#[verifier::opaque]
spec fn heavy_recursive_spec(...) { ... }  // hidden by default

proof fn caller() {
    reveal(heavy_recursive_spec);  // unfold only where needed
}
```

### Replace Loops with Recursion (for Heavy Invariants)

**When loop invariants are expensive:** Loop invariants are re-verified every iteration. Recursive functions only verify `requires` once at the call site.

**When it works:**
- Loop runs 20+ iterations
- Invariants have quadratic `forall|i, j|` quantifiers
- Heavy per-step computation

**Example:** 600M rlimit → 25M (-96%) by converting to recursion.

**When it doesn't work:** GUI layout loops with 3-10 children and simple invariants—function-call overhead exceeds savings.

### Roundtrip Contradiction for Injectivity

Instead of manually unfolding complex functions, use a roundtrip lemma:
```rust
if linearize(coords1, shape) == linearize(coords2, shape) {
    lemma_roundtrip(coords1, shape);  // proves coords1 =~= delinearize(...)
    lemma_roundtrip(coords2, shape);
    assert(false);  // contradiction!
}
```
**Result:** 143 lines → 47 lines, 3.13M → 90K rlimit (-97%)

### Trigger Shift Avoidance

When extracting helpers with shifted indices:
```rust
// BAD: trigger stride[j+1] won't match stride[k]
forall|j| 0 <= j < k-1 ==> ... #[trigger] stride[j + 1]

// GOOD: use same shape
forall|j| 1 <= j < k ==> ... #[trigger] rest_shape.take(j)
```

---

## 11. Common Pitfalls

### Ghost `let` Not Available in Loops

```rust
// BAD: x is not available inside loop body
let ghost x = Seq::new(n, f);
while i < n {  // x not in scope here!
    assert(x[i] == f(i));  // FAILS
}

// GOOD: use invariant
while i < n
    invariant forall|j| 0 <= j < n ==> x[j] == f(j)
{ ... }
```

### Or Patterns in Spec Match Break Z3

```rust
// BAD: prevents Z3 from extracting results
match mesh {
    A { children, .. } | B { children, .. } => ...
}

// GOOD: separate arms
match mesh {
    A { children, .. } => { let x = children; ... }
    B { children, .. } => { let x = children; ... }
}
```

### nat vs usize in Fuel Arithmetic

Z3 can't unify `(fuel as nat - 1) as nat` with `(fuel - 1) as nat`:
```rust
// Bridge with assertion inside assert forall:
assert forall |i| ... by {
    assert((fuel as nat - 1) as nat == (fuel - 1) as nat);
    // now Z3 can proceed
}
```

### Seq::new vs Seq::map

```rust
// Seq::new unfolds better (auto-trigger fires)
Seq::new(len, |i| seq[i]@)

// Seq::map may not unfold
seq.map(|_i, p| p@)
```

### Don't Add Helpers to Pollute Module Triggers

Adding a helper function to a module introduces its signature into Z3's background axioms for ALL functions. If the ensures mentions common terms, it creates trigger matches that **increase** rlimit for unrelated functions.

**Solution:** Put proof helpers in a **separate module** (e.g., `proofs.rs` separate from `construction.rs`).

---

## Appendix: Common Patterns

### Binary Search
```rust
fn binary_search(v: &Vec<u64>, k: u64) -> (r: usize)
    requires
        forall |i, j| 0 <= i <= j < v.len() ==> v[i] <= v[j],
        exists |i| 0 <= i < v.len() && k == v[i],
    ensures k == v[r as int]
{
    let mut lo = 0;
    let mut hi = v.len() - 1;
    while lo != hi
        invariant
            exists |i| lo <= i <= hi && k == v[i],
        decreases hi - lo
    {
        let mid = lo + (hi - lo) / 2;
        if v[mid] < k { lo = mid + 1; }
        else { hi = mid; }
    }
    lo
}
```

### Fibonacci with Invariants
```rust
spec fn fib(n: nat) -> nat decreases n {
    if n == 0 { 0 } else if n == 1 { 1 } else { fib(n-2) + fib(n-1) }
}

fn fib_impl(n: u64) -> (r: u64)
    requires fib(n as nat) <= u64::MAX
    ensures r == fib(n as nat)
{
    if n == 0 { return 0; }
    let mut prev = 0u64;
    let mut cur = 1u64;
    let mut i = 1u64;
    while i < n
        invariant
            0 < i <= n,
            cur == fib(i as nat),
            prev == fib((i - 1) as nat),
        decreases n - i
    {
        i = i + 1;
        let next = cur + prev;
        prev = cur;
        cur = next;
    }
    cur
}
```

### TreeMap Key Methods
```rust
// Abstract view
spec fn as_map(self) -> Map<K, V> { ... }

// Constructor
pub fn new() -> Self
    ensures tree_map@ == Map::empty()
{ TreeMap { root: None } }

// Insert  
pub fn insert(&mut self, k: K, v: V)
    ensures self@ == old(self)@.insert(k, v)

// Get
pub fn get(&self, k: K) -> Option<&V>
    returns if self@.dom().contains(k) { Some(&self@[k]) } else { None }
```

---

*Generated from Verus documentation*
