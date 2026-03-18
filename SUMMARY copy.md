# Verus Guide Summary (First 500 Lines)

## Overview
Verus is a tool for **static verification** of Rust code, using SMT (Z3) to prove full functional correctness. It extends Rust syntax with verification features but code compiles to normal Rust executables.

**Key Principles:**
- No runtime overhead - verification code is ghost code, erased at compile time
- Modular verification via requires/ensures contracts
- Three code modes: `spec` (mathematical), `proof` (verification), `exec` (executable)

---

## Getting Started

### Setup
- Run via command line: `/path/to/verus file.rs`
- Or use VSCode with `verus-analyzer` extension
- Compile with `--compile` flag to generate binaries

### Basic Structure
```rust
use vstd::prelude::*;
verus! {
    // Verus code here
}
```

---

## Basic Specifications

### Preconditions (`requires`)
```rust
fn octuple(x1: i8) -> i8
    requires -16 <= x1 < 16
{ ... }
```
- Constraints on function inputs
- Checked at call sites
- Can chain: `-16 <= x1 < 16` means `-16 <= x1 && x1 < 16`

### Postconditions (`ensures`)
```rust
fn f(x1: i8) -> (x8: i8)
    ensures x8 == 8 * x1
{ ... }
```
- Name return value with `-> (name: type)` syntax
- Describes what function guarantees

### Assertions
- `assert(expr)` - asks SMT to prove, fails if not provable
- `assume(expr)` - accepts without proof (**dangerous**, use sparingly)
- Never use `assume` in final code; only for debugging

### Ghost vs Executable Code
- `requires`, `ensures`, `assert`, `assume` are ghost code
- Mark unverified functions with `#[verifier::external_body]`

---

## Integer Types

| Type | Description | Used in |
|------|-------------|---------|
| `int` | Arbitrary-precision mathematical integer | Spec code |
| `nat` | Non-negative integers (>= 0) | Spec code |
| `u8/u16/.../u128`, `i8/...` | Fixed-width Rust integers | Exec code |

**Rule:** Use `int` by default in specifications; it's most efficient for SMT. Use `nat` when you need non-negativity info.

**In ghost code:** `+`, `-`, `*` never overflow (widened to `int`).  
**In exec code:** Overflow checked and must be proven impossible.

---

## Specification Operators

### Chained Inequalities
`0 <= i <= j < len` means `0 <= i && i <= j && j < len`

### Implication
`a ==> b` is `!a || b` (low precedence)

### Triple operators (low precedence)
- `&&&` - like `&&` but lower precedence
- `|||` - like `||` but lower precedence

### Equality
- `==` in ghost code is always an equivalence relation (reflexive, symmetric, transitive)
- Struct/enum equality compares field-by-field

---

## Integer Constants & Coercions

### Constants
- Type suffixes: `7u8`, `7u32`, `7int`, `7nat`
- `int`/`nat` constants can be arbitrarily large
- Different integer types can be compared in ghost code

### Type Coercion (`as`)
```rust
let i: int = u as int;   // always valid
let n: nat = u as nat;    // only valid if u >= 0
let u8_val = v as u8;     // truncates if out of range
```
**Warning:** Use `#[verifier::truncate]` to silence out-of-range warnings.

---

## Integer Arithmetic

### Ghost Code (spec/proof)
- `+`, `-`, `*` **never overflow** - widened to `int`
- `/` and `%` use **Euclidean division** (result always non-negative)
- `add()`, `sub()`, `mul()` - truncating versions

### Exec Code
- Overflow **must be proven impossible**
- Use `checked_add`, `wrapped_add` for runtime checks

---

## Equality

### Ghost Code
- `==` is always an **equivalence relation** (reflexive, symmetric, transitive)
- Struct/enum equality compares field-by-field

### Exec Code
- `==` calls `PartialEq::eq()` - may have side effects
- For collections (Seq, Set, Map), use **extensional equality**: `=~=`

---

## Three Code Modes

### 1. `spec` Functions
- Pure mathematical functions
- Can use `int`/`nat` types
- Body may be visible (`open`) or hidden (`closed`)
- No `requires`/`ensures`, only `recommends` (soft preconditions)

### 2. `proof` Functions
- Prove properties about specs
- Ghost code, not compiled
- May have `requires`/`ensures`
- Can call other proof/spec functions
- **Non-deterministic** - same input might return different values

### 3. `exec` Functions
- Regular Rust code
- Can call spec/proof only via `proof { ... }` blocks
- Default mode (omitted annotation)

| Feature | spec | proof | exec |
|---------|------|-------|------|
| Compiled | No | No | Yes |
| Mutation | No | Yes | Yes |
| Can call spec | Yes | Yes | Yes |
| Can call proof | No | Yes | Yes |
| Has requires/ensures | No (recommends) | Yes | Yes |

---

## Proof Blocks & Lemma Calling

### Proof Blocks
```rust
fn exec_fn() {
    proof {
        let ghost_val = some_spec_fn(x);
        lemma_min(10, 20);
    }
}
```

### `assert ... by { ... }` (Scoped Proof)
```rust
assert(x == y) by {
    lemma_equal(x, y);
}
```
- Information **contained** within the `by` block
- Doesn't leak to surrounding context

### Lemma Functions
```rust
proof fn lemma_min(x: int, y: int)
    ensures min(x, y) <= x, min(x, y) <= y
{ }
```
- Used to prove properties about `closed spec fn`
- Call inside `proof { }` or `assert ... by { }`

---

## Key Takeaways

1. **No `assume` in production** - always prove things fully
2. **Write `requires`/`ensures`** for function contracts
3. **Use `int` in specs**, not fixed-width types
4. **Modular verification** - each function verified independently
5. **Ghost code erased** - no runtime overhead
6. **Proof blocks** for calling lemmas from exec code
7. **`assert by { }`** to scope lemma information

---

*Lines 501-1000 covered: integer constants/coercions, arithmetic differences, equality, spec/proof/exec modes, proof blocks*

---

## Sections 1001-1500

### Ghost Code Properties

**Ghost code abilities:**
- Can create values of any type, even types with private constructors
- Can copy/duplicate any value
- Values cannot leak into exec code (compile-time error)
- Example: `duplicate_S(s)` can duplicate a struct S even with private fields

### Const Declarations

Consts are like 0-argument functions, can be marked spec/proof/exec or dual spec/exec:

```rust
spec const SPEC_ONE: int = 1;

exec const C: u64
    ensures C == 7
{ 7 }

// Dual-use const (both exec and spec)
const ONE: u8 = 1;
```

**Using exec const as spec:** Add `#[verifier::when_used_as_spec(SPEC_DEF)]` annotation.

**Overflow troubleshooting:** Use `#[verifier::nonlinear]` on const declarations.

### Putting It All Together: Triangle Example

Complete example combining spec, proof, and exec:

```rust
spec fn triangle(n: nat) -> nat
    decreases n,
{
    if n == 0 { 0 } else { n + triangle((n - 1) as nat) }
}

proof fn triangle_is_monotonic(i: nat, j: nat)
    ensures i <= j ==> triangle(i) <= triangle(j),
    decreases j,
{
    if j == 0 { } // base case trivial
    else {
        triangle_is_monotonic(i, (j - 1) as nat);
    }
}

fn loop_triangle(n: u32) -> (sum: u32)
    requires triangle(n as nat) < 0x1_0000_0000,
    ensures sum == triangle(n as nat),
{
    let mut sum: u32 = 0;
    let mut idx: u32 = 0;
    while idx < n
        invariant idx <= n, sum == triangle(idx as nat),
        decreases n - idx,
    {
        idx = idx + 1;
        assert(sum + idx < 0x1_0000_0000) by {
            triangle_is_monotonic(idx as nat, n as nat);
        }
        sum = sum + idx;
    }
    sum
}
```

---

## Recursion and Loops (1300+)

### Decreases Clause (Termination)

**Required for recursive spec functions** to prove termination:

```rust
spec fn triangle(n: nat) -> nat
    decreases n,  // MUST be strictly decreasing
{
    if n == 0 { 0 } else { n + triangle((n - 1) as nat) }
}
```

Without `decreases`, nonterminating functions would allow proving `false`.

### Fuel and Recursive Functions

**Problem:** SMT can't automatically inline recursive functions deeply.

```rust
assert(triangle(10) == 55);  // FAILS - not enough fuel
```

**Solution:** Use `reveal_with_fuel`:

```rust
fn test() {
    proof { reveal_with_fuel(triangle, 11); }
    assert(triangle(10) == 55);  // succeeds
}
```

Default fuel is 1. Each recursive inlining consumes 1 fuel unit.

### Recursive Exec Functions

Exec functions can also be recursive but don't need decreases clause (Verus checks termination differently).

**Important:** Overflow must be proven impossible:

```rust
fn rec_triangle(n: u32) -> (sum: u32)
    requires triangle(n as nat) < 0x1_0000_0000,
    ensures sum == triangle(n as nat),
    decreases n,  // needed for spec call
{
    if n == 0 { 0 } else { n + rec_triangle(n - 1) }
}
```

### Old Values in Specifications

Use `*old(val)` to refer to initial value of a variable:

```rust
fn tail_triangle(n: u32, idx: u32, sum: &mut u32)
    requires
        *old(sum) == triangle(idx as nat),  // initial value
    ensures *sum == triangle(n as nat),
{ ... }
```

### Proofs by Induction

Write inductive proofs as recursive proof functions:

```rust
proof fn triangle_is_monotonic(i: nat, j: nat)
    ensures i <= j ==> triangle(i) <= triangle(j),
    decreases j,
{
    if j == 0 { }  // base case
    else {
        triangle_is_monotonic(i, (j - 1) as nat);  // induction step
    }
}
```

---

*Lines 1001-1500 covered: ghost code properties, const declarations, triangle example, recursion, decreases, fuel, induction proofs*

---

## Sections 1501-2000

### Loops and Invariants

**Loop invariants** describe what must be true before/after each iteration:

```rust
while idx < n
    invariant
        idx <= n,           // holds at start and after each iteration
        sum == triangle(idx as nat),
        triangle(n as nat) < 0x1_0000_0000,
    decreases n - idx,
{
    idx = idx + 1;
    sum = sum + idx;
}
```

**Three requirements for invariants:**
1. Hold upon initial entry to loop
2. Maintained at end of loop body
3. Strong enough to prove postcondition

**Loop invariant inheritance:** Loops don't auto-inherit surrounding preconditions—must be repeated in invariant.

**Opt out:** Use `#[verifier::loop_isolation(false)]` on function/module/crate.

### Loops with Break/Return

**Return inside loop:** Can exit early with `return`:

```rust
while idx < n {
    if overflow_detected {
        return 0xffff_ffff;
    }
    sum = sum + idx;
}
```

**Break inside loop:** Use `invariant_except_break` for invariants that don't hold after break:

```rust
while idx < n
    invariant_except_break
        idx <= n,
        sum == triangle(idx as nat),
    ensures  // explicit postcondition required
        sum == triangle(n as nat) || sum == 0xffff_ffff,
{ ... }
```

### For Loops

For loops auto-increment index; use `iter: 0..n` syntax:

```rust
for idx in iter: 0..n
    invariant sum == triangle(idx as nat),
{
    sum = sum + idx + 1;
}
```

- `iter.start`, `iter.cur`, `iter.end` - iterator state
- `iter@` - elements iterated so far (e.g., `seq![0,1,2]`)

### Lexicographic Decreases

For functions with multiple recursive calls where one parameter doesn't always decrease:

```rust
spec fn ackermann(m: nat, n: nat) -> nat
    decreases m, n,  // lexicographic: m first, then n
{
    if m == 0 { n + 1 }
    else if n == 0 { ackermann((m - 1) as nat, 1) }
    else { ackermann((m - 1) as nat, ackermann(m, (n - 1) as nat)) }
}
```

### Mutual Recursion

Functions can be mutually recursive:

```rust
spec fn is_even(i: int) -> bool
    decreases abs(i),
{
    if i == 0 { true }
    else if i > 0 { is_odd(i - 1) }
    else { is_odd(i + 1) }
}

spec fn is_odd(i: int) -> bool
    decreases abs(i),
{
    if i == 0 { false }
    else if i > 0 { is_even(i - 1) }
    else { is_even(i + 1) }
}
```

### Structs

```rust
struct Point { x: int, y: int }

impl Point {
    spec fn len2(&self) -> int {
        self.x * self.x + self.y * self.y
    }
}
```

### Enums

```rust
enum Beverage {
    Coffee { creamers: nat, sugar: bool },
    Soda { flavor: Syrup },
    Water { ice: bool },
}
```

**Enum operators in specs:**
- `is` operator: `bev is Soda` (returns bool)
- `!is` shorthand: `bev !is Coffee`
- Arrow access: `bev->creamers`

**matches syntax** for binding fields:

```rust
spec fn cuddly(l: Life) -> bool {
    ||| l matches Mammal { legs, .. } && legs == 4
    ||| l matches Arthropod { legs, wings } && legs == 8
}
```

---

## Libraries: Seq, Set, Map

Verus standard library (`vstd`) provides immutable collection types for specifications:

### Seq\<T\> - Sequences

```rust
let s: Seq<int> = seq![0, 10, 20, 30, 40];
assert(s.len() == 5);
assert(s[2] == 20);
```

### Set\<T\> - Sets

```rust
let s: Set<int> = set![1, 2, 3, 4, 5];
assert(s.contains(3));
```

### Map\<K, V\> - Maps

```rust
let m: Map<int, int> = map![1 => 10, 2 => 20];
assert(m[1] == 10);
```

**Key difference from Rust collections:** Size is `nat` (unbounded), can represent infinite sets/maps.

---

*Lines 1501-2000 covered: loop invariants, break/return, for loops, lexicographic decreases, mutual recursion, structs, enums, matches syntax, Seq/Set/Map libraries*

---

## Sections 2001-2500

### Seq, Set, Map Construction

**Macros for finite collections:**
```rust
Seq::new(5, |i: int| 10 * i)     // Seq with 5 elements
Set::new(|i: int| i % 10 == 0)   // Finite or infinite sets
Map::new(pred, |i| 10 * i)        // Map with domain predicate
```

### Extensional Equality (=~=)

Collections with same elements may not auto-equal via `==`. Use `=~=`:

```rust
let s1 = seq![0, 10, 20, 30, 40];
let s2 = seq![0, 10] + seq![20] + seq![30, 40];
assert(s1 =~= s2);  // forces element-by-element comparison
```

**When needed:** After operations like `.remove()`, `.intersect()`, etc.

### Vec Executable Library

Executable Vec connected to Seq via `@` operator:

```rust
let mut v: Vec<u32> = Vec::new();
v.push(0);
assert(v@ =~= seq![0, 10, 21, 30, 40]);  // Seq view of Vec
assert(v@[2] == 21);                      // Index into Seq
assert(v@.subrange(2, 4) =~= seq![21, 30]);  // Subsequence
```

**Best practice:** Write specs using Seq/Set/Map, not Vec directly.

### Spec Closures

Anonymous ghost functions in spec/proof code:

```rust
let s = Seq::new(5, |i: int| 10 * i);

spec fn adder(x: int) -> spec_fn(int) -> int {
    |y: int| x + y
}
```

- Type is `spec_fn(args) -> ret`, not a trait
- Can return closures directly from spec functions
- Subject to same restrictions as named spec functions

---

## Developing Proofs

### Debugging Proofs with Assert/Assume

**Technique:** Use `assume` to isolate where proof fails:

```rust
// Start with assumes to check structure
assume(postcondition_holds);

// Then narrow down
if s1.is_empty() {
    assert(s1.intersect(s2) =~= Set::empty());
} else {
    // ... 
}
```

**Process:**
1. Add `assume(postcondition)` → if verifies, the issue is in the proof
2. Move assume into branches to isolate failure
3. Replace assume with assert to see what fails
4. Add needed lemmas/assertions

### Proving Base Cases

For empty sets, may need explicit extensionality:
```rust
if s1.is_empty() {
    assert(s1.intersect(s2) =~= Set::<A>::empty());
    assert(s1.intersect(s2).len() == 0);
}
```

### Induction Step Tips

1. Use `.choose()` and `.remove(a)` to make set smaller
2. After recursive call, explicitly state what it gives you
3. May need `=~=` to relate operations on collections

---

*Lines 2001-2500 covered: Seq/Set/Map construction, extensional equality, Vec @ operator, spec closures, proof debugging techniques*

---

## Sections 2501-3000

### Proving Induction Steps (lemma_len_intersect cont.)

**Key technique:** Work backwards from what you need to prove:

```rust
// Given induction hypothesis:
assert(s1.remove(a).intersect(s2).len() <= s1.remove(a).len());

// Need to show:
assume(s1.intersect(s2).len() <= s1.len());

// Relate via cardinality:
assert(s1.remove(a).len() == s1.len() - 1);  // removing decreases size
assert(s1.remove(a).intersect(s2).len() <= s1.len() - 1);

// Use extensionality to relate .remove() and .intersect():
assert(s1.intersect(s2).remove(a) =~= s1.remove(a).intersect(s2));
```

### Devising Loop Invariants: Fibonacci Example

**Spec:**
```rust
spec fn fib(n: nat) -> nat
    decreases n,
{
    if n == 0 { 0 } else if n == 1 { 1 } else { fib(n-2) + fib(n-1) }
}
```

**Implementation with invariants:**
```rust
fn fib_impl(n: u64) -> (result: u64)
    requires fib(n as nat) <= u64::MAX,
    ensures result == fib(n as nat),
{
    if n == 0 { return 0; }
    let mut prev: u64 = 0;
    let mut cur: u64 = 1;
    let mut i: u64 = 1;
    while i < n
        invariant
            0 < i <= n,
            fib(n as nat) <= u64::MAX,
            cur == fib(i as nat),
            prev == fib((i - 1) as nat),
        decreases n - i,
    {
        i = i + 1;
        proof { lemma_fib_is_monotonic(i as nat, n as nat); }
        let new_cur = cur + prev;
        prev = cur;
        cur = new_cur;
    }
    cur
}
```

**Key invariants needed:**
- `cur == fib(i)` - current fib value
- `prev == fib(i-1)` - previous fib value
- `fib(n) <= u64::MAX` - to prevent overflow (inherited from requires)
- Need monotonicity lemma to prove overflow won't happen

**Monotonicity lemma:**
```rust
proof fn lemma_fib_is_monotonic(i: nat, j: nat)
    requires i <= j,
    ensures fib(i) <= fib(j),
    decreases j - i,
{
    if j < 2 { }  // base cases
    else if i == j { }
    else if i == j - 1 { }
    else {
        lemma_fib_is_monotonic(i, (j - 1) as nat);
        lemma_fib_is_monotonic(i, (j - 2) as nat);
    }
}
```

### Account Balance Example

**Problem:** Check if running sum of operations stays non-negative.

```rust
fn non_negative(operations: &[i64]) -> (r: bool)
    ensures r == always_non_negative(operations@),
{
    let mut s = 0i128;
    for i in 0..operations.len()
        invariant
            s == sum(operations@.take(i as int)),
            forall|j| 0 <= j <= i ==> sum(operations@.take(j)) >= 0,
            i64::MIN <= s <= i64::MAX * i,
    {
        assert(operations@.take(i as int) =~= operations@.take((i + 1) as int).drop_last());
        s = s + operations[i] as i128;
        if s < 0 { return false; }
    }
    true
}
```

### Proving Absence of Overflow

**Method 1: Explicit bounds**
```rust
fn compute_sum(x: u64, y: u64) -> (result: u64)
    requires x < 1000000, y < 1000000,
    ensures result == x + y,
{ x + y }  // provably no overflow
```

**Method 2: Runtime checks**
```rust
fn compute_sum(x: u64, y: u64) -> (result: Option<u64>)
    ensures match result { Some(z) => z == x + y, None => x + y > u64::MAX },
{
    x.checked_add(y)  // returns None on overflow
}
```

---

*Lines 2501-3000 covered: detailed induction proof, Fibonacci loop invariants, monotonicity lemma, account balance with forall, overflow proofs*

---

## Sections 3001-3500

### CheckedU64 for Overflow-Free Arithmetic

Use `CheckedU64` to avoid overflow proofs:
```rust
fn fib_checked(n: u64) -> (result: u64)
    requires fib(n as nat) <= u64::MAX,
    ensures result == fib(n as nat),
{
    let mut cur = CheckedU64::new(1);
    let mut prev = CheckedU64::new(0);
    let mut i: u64 = 1;
    while i < n {
        invariant 0 < i <= n, cur@ == fib(i as nat), prev@ == fib((i-1) as nat),
        decreases n - i,
        {
            i = i + 1;
            let new_cur = cur.add_checked(&prev);
            prev = cur;
            cur = new_cur;
        }
    }
    cur.unwrap()
}
```
- `cur@` extracts the Seq view (ghost state)
- No monotonicity lemma needed!

---

## Quantifiers: forall and exists

### forall (Universal Quantifier)

```rust
forall|i: int| 0 <= i < s.len() ==> #[trigger] is_even(s[i])
```
- Means: for ALL i satisfying condition, property holds
- Infinite conjunction: `f(-2) && f(-1) && f(0) && ...`

### exists (Existential Quantifier)

```rust
exists|i: int| #[trigger] is_even(i)
```
- Means: there EXISTS at least one i with property
- Needs a witness value

---

## Triggers

**Purpose:** Tell SMT which expressions to match for quantifier instantiation.

### Basic Usage

```rust
forall|i: int| 0 <= i < s.len() ==> #[trigger] is_even(s[i])
```

When verifying `assert(is_even(s[3]))`, SMT matches `is_even(s[3])` against trigger `is_even(s[i])` → instantiates with i=3.

### Trigger Rules

1. **Must mention all quantified variables**
2. **Cannot contain:** `==`, `!=`, `<=`, `+` (arithmetic/equality/bool ops)
3. **Can be:** function calls, field access, bitwise ops

### Good vs Bad Triggers

**Bad:** `0 <= i` - too broad, matches anything non-negative

**Good:** `s[i]` - precise, matches actual sequence elements

```rust
// Auto-selected trigger works
forall|i: int| 0 <= i < s.len() ==> is_even(s[i])  // Verus picks s[i]

// Explicit trigger
forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] is_even
```

### Multiple Variables

```rust
forall|i: int, j: int| 0 <= i < j < s.len() ==> #[trigger] s[i] != #[trigger] s[j]
```

Each `#[trigger]` in a group must match simultaneously.

### Multiple Triggers

```rust
forall|i: int, j: int|
    #![trigger a[i], b[j]]
    #![trigger a[i], c[j]]
    0 <= i < j < a.len() ==> a[i] != b[j] && a[i] != c[j]
```
SMT uses ANY matching trigger.

### Matching Loops (AVOID!)

```rust
// BAD: causes infinite matching
forall|i: int| 0 <= i < s.len() - 1 ==> #[trigger] s[i] <= s[i + 1]
```
When SMT sees `s[2]`, it creates `s[3]`, which creates `s[4]`, etc. → potential infinite loop.

**Fix:** Use two-variable quantification instead:
```rust
forall|i: int, j: int| 0 <= i <= j < s.len() ==> s[i] <= s[j]
```

### exists Triggers

```rust
assert(exists|i: int| #[trigger] is_even(i));  // succeeds with witness
```

---

*Lines 3001-3500 covered: CheckedU64, forall/exists quantifiers, triggers, matching loops*

---

## Sections 3501-4000

### choose Expression

Extract witness from proven `exists`:
```rust
proof fn test_choose(s: Seq<int>)
    requires exists|i: int| f(i),
{
    let w = choose|i: int| f(i);  // get the witness
    assert(f(w));  // must hold
}
```

If `exists` not proven, `choose` returns arbitrary value.

### Proving forall with assert-by

Bring quantifier variables into scope:
```rust
proof fn test_even_f()
    ensures forall|i: int| is_even(i) ==> f(i),
{
    assert forall|i: int| is_even(i) implies f(i) by {
        lemma_even_f(i);  // i is now in scope
    }
}
```

### Using exists with choose

```rust
proof fn test_g_proves_f(i: int)
    requires exists|j: int| g(i, j),
    ensures f(i),
{
    lemma_g_proves_f(i, choose|j: int| g(i, j));
}
```

### Binary Search Example

```rust
fn binary_search(v: &Vec<u64>, k: u64) -> (r: usize)
    requires
        forall|i: int, j: int| 0 <= i <= j < v.len() ==> v[i] <= v[j],
        exists|i: int| 0 <= i < v.len() && k == v[i],
    ensures k == v[r as int],
{
    let mut i1: usize = 0;
    let mut i2: usize = v.len() - 1;
    while i1 != i2
        invariant
            exists|i: int| i1 <= i <= i2 && k == v[i],
        decreases i2 - i1,
    {
        let ix = i1 + (i2 - i1) / 2;
        if v[ix] < k { i1 = ix + 1; }
        else { i2 = ix; }
    }
    i1
}
```

---

## Broadcast Lemmas (Ambient Facts)

`broadcast proof fn` makes lemmas always available without calling them:

```rust
pub broadcast proof fn seq_contains_after_push<A>(s: Seq<A>, v: A, x: A)
    requires s.contains(x)
    ensures #[trigger] s.push(v).contains(x)
{ }

use broadcast seq_contains_after_push;  // bring into scope
```

**Groups:** `broadcast use vstd::seq_lib::group_seq_properties;`

---

## SMT Limitations

- Proving with quantifiers relies on triggers
- Opaque/closed functions hide bodies
- Inductive invariants need manual proofs
- Extensional equality needs explicit assertions
- Standard library axioms may be incomplete

---

## Nonlinear Arithmetic

**Default mode:** Linear arithmetic only (4*x + 3*y - z).

**For nonlinear (x*y):** Use specialized solvers.

### nonlinear_arith

```rust
assert(x * y <= 100) by(nonlinear_arith)
    requires x <= 10, y <= 10;

// Or in proof function:
proof fn bound_check(x: u32, y: u32) by(nonlinear_arith)
    requires x <= 8, y <= 8,
    ensures x * y <= 64,
{ }
```

### integer_ring

For ring-based properties (congruences):
```rust
proof fn lemma_congruence(a: int, b: int, c: int, n: int) by(integer_ring)
    requires a % n == b % n,
    ensures (a * c) % n == (b * c) % n,
{ }
```

**Alternative:** Use library lemmas like `lemma_mul_is_commutative`, `lemma_mul_is_distributive_add`, etc.

---

*Lines 3501-4000 covered: choose, forall/exists proofs, binary search, broadcast lemmas, SMT limitations, nonlinear arithmetic*

---

## Sections 4001-4500

### integer_ring Limitations

- Only `int` parameters
- No inequalities
- No division
- Functions treated as uninterpreted (use `reveal` to inline)
- Divisor must not be zero

**Modulus encoding:** `a % b == x` becomes `a - b*tmp == x` (no bounds)

### Combining integer_ring + nonlinear_arith

Use `integer_ring` for equalities, `nonlinear_arith` for inequalities:

```rust
pub proof fn lemma_mod_diff_helper(...) by(integer_ring)
    requires small_x == x % d, ...
    ensures (tmp1 - tmp2) % d == 0
{}

pub proof fn lemma_mod_diff(...) by(nonlinear_arith)
    requires d > 0, x <= y, ...
    ensures y % d - x % d == y - x
{
    lemma_mod_diff_helper(...);  // ring part
    // nonlinear handles rest
}
```

---

## Bit Vectors

**Default:** Bitwise ops are uninterpreted.

### bit_vector Solver

```rust
fn test(b: u32) {
    assert(b & 7 == b % 8) by(bit_vector);
    assert(b & 0xff < 0x100) by(bit_vector);
}
```

**What it handles:** `&`, `|`, `^`, `<<`, `>>`, arithmetic on bounded ints

**Cannot handle:** Symbolic `int` values (use concrete bitwidths)

### Helper Functions

```rust
spec fn get_bit(val: u32, index: u32) -> bool {
    0x1u32 & (val >> index) == 1
}

fn test() { assert(get_bit(128u32, 7)) by(bit_vector); }
```

---

## Extensional Equality (Recap)

**Operators:** `=~=` (shallow), `=~~=` (deep/nested)

**For structs/enums:** Add `#[verifier::ext_equal]` attribute:
```rust
#[verifier::ext_equal]
struct Foo { a: Seq<int>, b: Set<int> }

assert(f1 =~= f2);  // now works directly
```

---

## Proof Performance

### Measuring

- `--time` - detailed breakdown
- `--time-expanded` - even more detail
- `--output-json` - machine-readable
- `--profile` - quantifier profiler (use with `--rlimit 1`)

### Quantifier Profiling

Profile shows which quantifiers cause instantiation storms:
```
note: Cost * Instantiations: 2269911826 top quantifier
note: Triggers selected: f(x + 1, 2 * y) && ... ==> #[trigger] f(x, y)
```

### Common Issues

1. **Trigger loops** - quantifier triggers itself infinitely
2. **Too many instantiations** - triggers too broad
3. **Inductive lemmas not unfolding** - use `reveal_with_fuel`

---

## Modules: opaque and reveal

Hide function bodies to speed up verification:
```rust
#[verifier::opaque]
spec fn tricky_spec(...) { ... }

proof fn use_spec() {
    // body hidden - uses axioms only
    reveal(tricky_spec);  // unfold for this call
}
```

---

*Lines 4001-4500 covered: integer_ring, bit_vector, extensional equality, proof performance, quantifier profiling, opaque/reveal*

---

## Sections 4501-5000

### calc! Macro (Structured Proofs)

Prove relations via intermediate steps:

```rust
let x: int = 2;
calc! {
    (<=)                    // relation to prove
    x; {}                   // x
    x + 3; {}               // x + 3
    5;                      // 5
}
// proves x <= 5 via x <= x+3 <= 5
```

**Intermediate relations:**
```rust
calc! {
    (<=)
    x; (==) {}             // intermediate ==
    5 - 3; (<) {}          // intermediate <
    5int; {}
    y;
}
```

---

## Proof by Computation

Force evaluation of recursive functions:

```rust
spec fn pow(base: nat, exp: nat) -> nat { ... }

proof fn test() {
    assert(pow(2, 8) == 256) by (compute);      // evaluates
    assert(pow(2, 9) == 512);  // succeeds via assumption
    
    assert(pow(2, 8) == 256) by (compute_only); // fails if not fully reduced
}
```

**No context inheritance** - variables treated symbolically.

---

## Breaking Proofs into Pieces

### 1. Extract subproofs to lemmas

```rust
// Before: long proof P in function
P1; P2; P3;  // establishing s1, s2

// After: extract to lemma
proof fn helper(x, y) requires f(x,y) ensures s1(x), s2(x,y) { P2; P3; }
my_long_function() { P1; helper(x,y); ... }
```

### 2. Sequential lemmas (pipeline)

```rust
proof fn part1(x) requires r(x) ensures mid1(x, y) { P1; }
proof fn part2(x, y) requires mid1(x,y) ensures mid2(x,y) { P2; }
proof fn part3(x, y) requires mid2(x,y) ensures e(x) { P3; }

proof fn my_long_function(x) requires r(x) ensures e(x) {
    let y = part1(x);
    part2(x, y);
    part3(x, y);
}
```

---

## Debugging Proofs Checklist

**Proof failing:**
1. Run with `--expand-errors`
2. Check recommends-failures
3. Add assert statements
4. Check quantifier triggers
5. Try `nonlinear_arith` for nonlinear arithmetic
6. Try `bit_vector` for bitwise ops
7. Use extensional equality `=~=` for collections
8. Understand fuel for recursive functions

**Rlimit exceeded:**
1. Run quantifier profiler (`--profile`)
2. Break proof into pieces
3. Increase rlimit

**Flaky proofs:**
1. Add `#[verifier::spinoff_prover]`
2. Break proof into pieces

---

## References and Borrowing

### Immutable References (`&T`)

Treated same as value - no pointer reasoning needed:
```rust
let x: u32 = 0;
let r = &x;
assert(*r == 0);
```

### Mutable References (`&mut T`)

```rust
fn modify(a: &mut u32)
    requires *old(a) < u32::MAX,
    ensures *a == *old(a) + 1
{
    *a = *a + 1;
}
```

**Key:** `*old(x)` = pre-state, `*x` = post-state

---

## Higher-Order Functions

Reason about function preconditions via spec functions:

```rust
call_requires(f, args)   // f's precondition
call_ensures(f, args, output)  // f's postcondition

// Or via method syntax:
f.requires(args)
f.ensures(args, output)
```

**Note:** Calling `impl Fn` requires Verus to verify precondition satisfied.

---

*Lines 4501-5000 covered: calc! macro, proof by computation, breaking proofs, debugging checklist, references/borrowing, higher-order functions*

---

## Sections 5001-5500

### Higher-Order Functions (call_requires/call_ensures)

```rust
fn double(x: u8) -> (res: u8)
    requires 0 <= x < 128,
    ensures res == 2 * x { 2 * x }

fn higher_order_fn(f: impl Fn(u8) -> u8) -> (res: u8)
    requires call_requires(f, (50,)),
    ensures res % 2 == 0
{
    f(50)
}
```

**Key insight:** Use `forall` to constrain postconditions:
```rust
forall|x, y| call_ensures(f, x, y) ==> y % 2 == 0
```

### Closures

Closures can capture variables:
```rust
let x: u8 = 20;
let f = || {
    assert(x == 20);  // captures x
    x
};
```

**Note:** Verus doesn't support mutable borrows in closures yet.

---

## Strings

```rust
let x = "hello world";
proof { reveal_strlit("hello world"); }
assert(x@.len() == 11);  // x@ is Seq<char>
```

**Important:** String literals are opaque by default - need `reveal_strlit`.

---

## Interior Mutability

**Problem:** `&T` values can't change, but `Cell<T>` contents can.

**Solution:** Cell is just a unique identifier, not its contents.

### InvCell (Data Invariants)

Use `InvCell<T>` with invariant predicate:

```rust
spec fn cell_is_valid(cell: &InvCell<Option<u64>>) -> bool {
    forall|v| cell.inv(v) <==> match v {
        Option::Some(i) => i == result_of_computation(),
        Option::None => true,
    }
}

fn memoized(cell: &InvCell<Option<u64>>) -> (res: u64)
    requires cell_is_valid(cell),
    ensures res == result_of_computation(),
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

---

## Container Library: Binary Search Tree

### Tree Definition

```rust
struct Node<V> {
    key: u64,
    value: V,
    left: Option<Box<Node<V>>>,
    right: Option<Box<Node<V>>>,
}

pub struct TreeMap<V> { root: Option<Box<Node<V>>> }
```

### Abstract View (Map interpretation)

```rust
impl<V> TreeMap<V> {
    pub closed spec fn as_map(self) -> Map<u64, V> {
        Node::optional_as_map(self.root)
    }
}

impl<V> View for TreeMap<V> {
    type V = Map<u64, V>;
    open spec fn view(&self) -> Map<u64, V> { self.as_map() }
}
```

### Well-formedness (BST Ordering)

```rust
spec fn well_formed(self) -> bool {
    &&& (forall |elem| left.dom().contains(elem) ==> elem < self.key)
    &&& (forall |elem| right.dom().contains(elem) ==> elem > self.key)
    &&& (self.left.well_formed() && self.right.well_formed())
}
```

---

*Lines 5001-5500 covered: higher-order functions, closures, strings, interior mutability, InvCell, BST TreeMap case study*

---

## Sections 5501-6000

### TreeMap Implementation

**Constructor:**
```rust
pub fn new() -> (tree_map: Self)
    ensures tree_map@ == Map::<u64, V>::empty()
{ TreeMap { root: None } }
```

**Insert:**
```rust
pub fn insert(&mut self, key: u64, value: V)
    ensures self@ == old(self)@.insert(key, value)
{
    Node::insert_into_optional(&mut self.root, key, value);
}
```

**Get:**
```rust
pub fn get(&self, key: u64) -> Option<&V>
    returns (if self@.dom().contains(key) { Some(&self@[key]) } else { None })
{
    Node::get_from_optional(&self.root, key)
}
```

**Delete:** Uses `delete_rightmost` to find replacement node.

---

## Type Invariants

Remove `well_formed()` from client requires by using type_invariant:

```rust
#[verifier::type_invariant]
spec fn well_formed(self) -> bool { ... }
```

**Effect:**
1. Verus checks invariant at construction/modification
2. Client can assume invariant without explicit requires

**Usage:**
```rust
proof { use_type_invariant(&*self); }  // establish invariant
```

---

## Generic TreeMap: TotalOrdered Trait

```rust
pub trait TotalOrdered : Sized {
    spec fn le(self, other: Self) -> bool;
    
    proof fn reflexive(x: Self) ensures Self::le(x, x);
    proof fn transitive(x: Self, y: Self, z: Self)
        requires Self::le(x, y), Self::le(y, z)
        ensures Self::le(x, z);
    proof fn antisymmetric(x: Self, y: Self)
        requires Self::le(x, y), Self::le(y, x)
        ensures x == y;
}
```

---

*Lines 5501-6000 covered: TreeMap ops, delete, get, type invariants, TotalOrdered trait*

---

## Sections 6001-6500

### Generic TreeMap with TotalOrdered

```rust
struct Node<K: TotalOrdered, V> {
    key: K,
    value: V,
    left: Option<Box<Node<K, V>>>,
    right: Option<Box<Node<K, V>>>,
}
```

**Using TotalOrdered in proofs:**
```rust
proof {
    if right.dom().contains(key) {
        TotalOrdered::antisymmetric(self.key, key);
        assert(false);
    }
}
```

---

## Implementing Clone for TreeMap

**Clone signature using `cloned<>`:**
```rust
impl<K: Copy + TotalOrdered, V: Clone> Clone for TreeMap<K, V> {
    fn clone(&self) -> (res: Self)
        ensures
            self@.dom() =~= res@.dom(),
            forall |key| #[trigger] res@.dom().contains(key) ==>
                cloned::<V>(self@[key], res@[key]),
    {
        TreeMap { root: self.root.clone() }
    }
}
```

**`cloned<T>(a, b)`** = helper for `call_ensures(V::clone, (&a,), b)`

---

## TreeMap Full Source Structure

```rust
// 1. Node + TreeMap structs
// 2. as_map() - abstract Map view
// 3. View trait implementation  
// 4. well_formed() - BST invariants
// 5. new() - constructor
// 6. insert() / insert_into_optional()
// 7. delete() / delete_from_optional() / delete_rightmost()
// 8. get() / get_from_optional()
// 9. Clone implementation
```

---

## Key Patterns Summary

1. **Spec functions** for abstract interpretation (`as_map`)
2. **Recursive specs** with `decreases` for termination
3. **Type invariants** `#[verifier::type_invariant]` auto-enforced
4. **`use_type_invariant()`** to establish invariant
5. **Quantifiers with triggers** for BST ordering proofs
6. **Extensional equality** `=~=` for Map/Seq comparisons

---

*Lines 6001-6500 covered: Generic TreeMap, TotalOrdered proofs, Clone impl, full source*

---

## Sections 6501-7000

This section contains **full source code** for three TreeMap implementations:
1. Basic u64 key version
2. Type invariant version
3. Generic K: TotalOrdered version with Clone

Key implementation notes:
- Use `Option::take()` to get ownership from `&mut Option<T>`
- Use `std::mem::swap()` pattern for type invariant preservation
- `#[verifier::type_invariant]` removes need for client `requires well_formed()`

---

## Sections 7001-7500

This section continues the full generic TreeMap source (K: TotalOrdered, V) with Clone implementation.

**TotalOrdered for u64:**
```rust
impl TotalOrdered for u64 {
    open spec fn le(self, other: Self) -> bool { self <= other }
    proof fn reflexive(x: Self) { }
    proof fn transitive(x: Self, y: Self, z: Self) { }
    proof fn antisymmetric(x: Self, y: Self) { }
    proof fn total(x: Self, y: Self) { }
    fn compare(&self, other: &Self) -> (c: Cmp) { ... }
}
```

---

## Interacting with Unverified Code

### #[verifier::external_body]

Use to call unverified code from verified code:
```rust
#[verifier::external_body]
fn fib_impl(n: u64) -> (result: u64)
    requires fib(n as nat) <= u64::MAX,
    ensures result == fib(n as nat),
{
    // Unverified implementation
    ...
}
```

**Warning:** Wrong specs here can subvert verification guarantees!

---

*Lines 7001-7500 covered: Generic TreeMap source completion, TotalOrdered impl, external_body*

---

## Sections 7501-8000

### External Code Integration

**assume_specification** - apply specs to existing functions:
```rust
pub assume_specification<T>[ std::mem::swap::<T> ](a: &mut T, b: &mut T)
    ensures *a == *old(b), *b == *old(a);
```

**external_type_specification** - make Verus aware of types:
```rust
#[verifier::external_type_specification]
struct ExSomeStruct(SomeStruct);
```

**external_trait_specification** - add specs to external traits.

### Eliminating Preconditions

Use wrapper with dynamic check + unsafe inner:
```rust
pub unsafe fn index_unchecked<T>(vec: &Vec<T>, i: usize)
    requires i < vec.len() { ... }

pub fn index<T>(vec: &Vec<T>, i: usize) -> Option<&T> {
    if i < vec.len() { Some(index_unchecked(vec, i)) }
    else { None }
}
```

### Memory Safety Philosophy

**Rust:** Safe/unsafe distinction, unsafe encapsulation
**Verus:** No unsafe/safe distinction, verification ensures memory safety

### Ghost Erasure

`verus_only` flag guards code only needed during verification:
```rust
#[cfg(verus_only)]
use crate::ghost_mod::ghost_fn;
```

---

## Supported Rust Features (Summary)

| Feature | Status |
|---------|--------|
| Functions, methods | Supported |
| Structs, enums | Supported |
| Closures | Supported |
| & and &mut | Partially supported |
| Async/await | Not supported |
| Traits | Supported |
| impl types | Partially supported |
| Unsafe blocks | Supported |
| Raw pointers | Partially supported |
| Multi-threading | Supported (vstd) |

---

*Lines 7501-8000 covered: external specs, preconditions elimination, memory safety, ghost erasure, supported features*

---

## Sections 8001-8500

### Verus Syntax Reference (Continued)

**Recursive functions with decreases:**
```rust
fn test_rec(x: u64, y: u64)
    decreases x,  // lexicographic if multiple
{ ... }

// with when clause
spec fn dec0(a: int) -> int
    decreases a when a > 0
    via dec0_decreases
{ ... }
```

**Variable modes:** exec, tracked, ghost

**exec code:** `let ghost x = ...` creates ghost variable  
**proof code:** variables are ghost by default

**Ghost/Tracked wrappers:**
```rust
let ghost u: int = my_spec_fun(x as int, y as int);
let Ghost(u): Ghost<int> = Ghost(expr);  // unwrap pattern
```

**Spec(checked):** enables recommends checking in spec functions

**forall/exists syntax:**
```rust
forall|x: int, y: int| 0 <= x < 100 ==> #[trigger] my_spec_fun(x, y) >= x
exists|x: int| #[trigger] my_spec_fun(x) == 10
```

**assert forall by:**
```rust
assert forall|x: int| x < 10 implies f1(x) < 11 by {
    assert(x < 10);
    reveal(f1);
    assert(f1(x) < 11);
}
```

**choose for exists witnesses:**
```rust
let x_witness = choose|x: int| f1(x) == 10;
```

---

## Sections 8501-9000

### Uninterpreted Spec Functions

```rust
uninterp spec fn my_uninterpreted_fun1(i: int, j: int) -> int;
```

### Traits with Specifications

```rust
trait T {
    proof fn my_function(&self, i: int) -> (r: int)
        requires 0 <= i < 10,
        ensures i <= r,
    ;

    fn with_default(&self, i: u32) -> (r: u32)
        requires 0 <= i < 10,
        ensures i <= r,
        default_ensures i == r || j == r,  // additional default
    { ... }
}
```

### Enum Patterns

```rust
// is operator
assert(t is This);
assert(t !is That);

// Arrow access
t->v  // access field

// matches syntax
t matches ThisOrThat::That { v } && v == 3
```

### Variable Modes Summary

| Code Mode | Default Var | ghost vars | tracked vars | exec vars |
|-----------|-------------|------------|--------------|-----------|
| spec | ghost | yes | no | no |
| proof | ghost | yes | yes | no |
| exec | exec | yes | yes | yes |

### Tracked and Ghost in Exec

```rust
fn example(Tracked(x): Tracked<X>, Ghost(y): Ghost<Y>) { ... }

fn test() {
    let tracked x = ...;
    let ghost y = ...;
    example(Tracked(x), Ghost(y));
}
```

---

## exec_spec_verified! / exec_spec_unverified!

Auto-generate exec code from spec:

```rust
exec_spec_verified! {
    struct Point { x: i64, y: i64 }
    
    spec fn on_line(points: Seq<Point>) -> bool {
        forall |i: usize| #![auto] 0 <= i < points.len()
            ==> points[i as int].y == points[i as int].x
    }
}
// Generates: ExecPoint, exec_on_line with verified equivalence
```

**exec_spec_unverified!** - same but without proof (for testing).

---

*Lines 8501-9000 covered: uninterp functions, traits, enum patterns, variable modes, Tracked/Ghost, exec_spec macros*

---

## Sections 9001-9500

### exec_spec Macros (Continued)

**Indexing rules:**
- `Seq[i as int]` - cast index to int
- Map keys must be primitive types; use `Map::get()` for complex keys

**Arithmetic in exec_spec:**
```rust
// x + y in spec is type int, not u64
pub open spec fn my_arith(x: u64, y: u64) -> u64 {
    (x + y) as u64  // cast required
}
```

---

## #[verus_spec] Attribute

Add specs to existing Rust code without rewriting APIs.

**Basic usage:**
```rust
#[verus_spec(sum => 
    requires x < 100, y < 100,
    ensures sum < 200,
)]
fn my_exec_fun(x: u32, y: u32) -> u32 { x + y }
```

**Proof blocks:**
```rust
proof! { ... }  // simple proof block
proof_decl! { let ghost mut i = 0int; ... }  // function-scoped ghost vars
```

**With tracked/ghost params:**
```rust
#[verus_spec(v => with Tracked(y): Tracked<&mut u32> -> z: Ghost<u32>
    requires *old(y) < 100,
    ensures *y == x, z@ == x,
)]
fn exec_tracked(x: u32) -> u32 {
    proof! { *y = x; }
    proof_with!(|= Ghost(x));
    (x + 1)
}
```

---

## Sections 9501-10000

This section contains more `#[verus_spec]` examples including:
- Traits with specs in verus_spec format
- `proof_decl!` for function-scoped ghost/tracked
- `proof_with!` for passing ghost/tracked to functions
- Loop invariants in verus_spec
- Various test macros and expected outputs

---

## Sections 10001-10500

More `#[verus_spec]` examples:
- `proof_with!` - pass ghost/tracked to function calls
- `dual_spec(spec_f)` - auto-generate spec from exec
- Closures with specs: `|y: u64| #[verus_spec(...)] { y }`
- `const fn` with ghost/tracked
- Item const with `#[verus_spec]`
- Trait impl methods with specs

**dual_spec example:**
```rust
#[verus_verify(dual_spec(spec_f))]
#[verus_spec(
    requires x < 100, y < 100,
    returns f(x, y)
)]
fn f(x: u32, y: u32) -> u32 { x + y }
// Auto-generates spec_f with equivalence proof
```

---

## Sections 10501-11000

(continuing...)

---

## Sections 11001-11500

### Box and References in Spec Mode

**References and Box:**
- Verus ignores `&` and `*` operations in spec mode (type-checking only)
- `Box<T>` can be used in spec mode with `Box::new(x)` and `*box`
- Useful for recursive types that need to satisfy Rust's sanity checks

### Operator Precedence Table

| Operators | Associativity |
|-----------|--------------|
| `. ->` | Binds tightest |
| `is matches` | Left |
| `* / %` | Left |
| `+ -` | Left |
| `<< >>` | Left |
| `&` | Left |
| `^` | Left |
| `\|` | Left |
| `!== == != <= < >= >` | Requires parens |
| `&&` | Left |
| `\|\|` | Left |
| `==>` | Right |
| `<==` | Left |
| `<==>` | Requires parens |
| `..` | Left |
| `=` | Right |
| `closures; forall, exists; choose` | Right |
| `&&&` | Left |
| `\|\|` | Left |

### Arithmetic in Spec Code

**Type Widening:**
| Operation | LHS | RHS | Result |
|-----------|-----|-----|--------|
| `+` | t1 | t2 | `int` (except nat+nat) |
| `+` | nat | nat | `nat` |
| `-` | t1 | t2 | `int` |
| `*` | t1 | t2 | `int` (except nat*nat) |
| `*` | nat | nat | `nat` |
| `/ %` | t | t | t |

**Euclidean Division:**
- `a / b` and `a % b` defined as unique q, r where `b*q + r == a` and `0 <= r < |b|`
- Remainder always non-negative
- Division-by-0 is "unspecified" (not hard error in spec code)

**Advanced Arithmetic Functions (vstd):**
- `pow` - exponentiation
- `pow2` - power of 2
- `log` - integer logarithm

### Bitwise Operators

**Operators:** `&`, `|`, `^` (bitwise AND, OR, XOR)
- Both operands must be same type
- Defined over integers ℤ x ℤ → ℤ (independent of bitwidth)

**Shift operators:** `>>` and `<<`
- Left and right sides can differ in type
- Result type matches left operand
- Right shift undefined for negative RHS

**Reasoning about bitwise ops:** Use `bit_vector` solver or `compute` solver

### Coercion with `as`

**Integer types:** i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize, int, nat, char

**Casting rules:**
- To `int`: always defined, no truncation
- To `nat`: unspecified if negative
- To `char`: unspecified if outside valid char values
- To finite integers: **truncation** (lower N bits)

### Trigger Annotations

**Trigger groups:**
- Each quantifier has trigger groups containing trigger expressions
- SMT instantiates quantifier when **any** trigger group fires
- A trigger group fires only when **all** expressions in it match

**Selecting triggers:**
1. `#[trigger]` annotations → trigger groups
2. `#[trigger(n)]` for same n → trigger group
3. `#![trigger EXPR1, ...]` at root → trigger group
4. If none: heuristics apply (`#![auto]` = conservative, `#![all_triggers]` = aggressive)

**Logging options:**
- `--triggers-mode silent` - hide auto triggers
- `--triggers-mode selective` - show when un-confident (default)
- `--triggers-mode verbose` - show all

### The `@` View Function

`expr@` is shorthand for `expr.view()`

### Spec Index Operator `[]`

`expr[i]` in spec code is shorthand for `expr.spec_index(i)`

### `decreases_to!`

`decreases_to!(e1, e2, ... => f1, f2, ...)` - checks lexicographic decrease

**Definition:** There exists k where:
- `ek decreases-to fk`
- For all i < k: `ei == fi`

**Decreases-to axioms:**
- Integers: `x > y >= 0` means `x decreases-to y`
- Datatypes decrease-to their recursive fields
- Seq decreases-to `s[i]` and `s.subrange(i, j)` if smaller

### `assert ... by` Statements

**Basic form:**
```rust
assert(P) by {
    // proof here
}
// Only P enters context, not proof internals
```

**`assert forall ... by`:**
```rust
assert forall |idents| P by {
    // prove P with idents in scope
}
// Only forall idents P enters context
```

**With implies:**
```rust
assert forall |idents| H implies P by {
    // H available in scope, prove P
}
```

### `assert ... by(bit_vector)`

Use Z3's bitvector solver for bitwise operations

**Requirements:**
- Variables must be `bool` or finite-width integers
- Symbolic `int`/`nat` NOT allowed (use concrete bitwidths)

### `assert ... by(nonlinear_arith)`

Use Z3's nonlinear solver for multiplication/division of symbolic values

### `assert ... by(compute)` / `by(compute_only)`

- `compute_only`: evaluate as far as possible, accept if evaluates to `true`
- `compute`: try compute_only first, fall back to normal solver

**No context inheritance** - treats local variables symbolically

### `#[verifier::memoize]`

Memoize function evaluation to avoid re-computation:
```rust
#[verifier::memoize]
spec fn fibonacci(n: nat) -> nat { ... }
```

### `reveal`, `reveal_with_fuel`, `hide`

- `reveal(f)` - unfold f's definition when encountered
- `hide(f)` - treat f as uninterpreted
- `reveal_with_fuel(f, n)` - unfold recursive f n times
- Default fuel is 1 (use more for deeper recursion)

### Function Signatures

**Exec fn:**
```
fn name generics?(args...) -> return_type
    where_clause?
    requires_clause?
    ensures_clause?
    returns_clause?
    invariants_clause?
    unwind_clause?
```

**Proof fn:**
```
proof fn name generics?(args...) -> return_type
    where_clause?
    requires_clause?
    ensures_clause?
    returns_clause?
    invariants_clause?
```

**Spec fn:**
```
spec fn name generics?(args...) -> return_type
    where_clause?
    recommends_clause?
    decreases_clause?
```

**`returns` clause** - syntactic sugar for ensures:
```rust
fn example() -> return_type
    returns $expr
// equivalent to:
fn example() -> (return_name: return_type)
    ensures return_name == $expr
```

**`#![verifier::allow_in_spec]`** - allow exec fn with returns clause in spec mode

---

*Lines 11001-11500 covered: Box/references, operator precedence, arithmetic widening, Euclidean division, bitwise ops, triggers, decreases_to!, assert by variants, memoize, reveal/hide, function signatures*

---

## Sections 11501-12000

### `opens_invariants` Clause

Control which tracked invariants a function can open:

```rust
fn example() opens_invariants any { }    // Any invariant
fn example() opens_invariants none { }   // No invariants
fn example() opens_invariants [inv1, inv2] { }  // Specific ones
```

**Defaults:**
- Exec functions: `opens_invariants any`
- Proof functions: `opens_invariants none`

### Unwinding Signature

```rust
fn get(&self, i: usize) -> T
    no_unwind when i < self.len()
```

- `no_unwind` - function cannot unwind
- `no_unwind when {condition}` - only guaranteed not to unwind if condition holds
- **Cannot unwind when invariant is open** (restriction for soundness)

### Drop and Unwinding

If you implement `Drop` for a type, you must give it `no_unwind` signature.

### Signature Inheritance

In trait implementations:
- `requires` clauses **inherited**, cannot add more
- `ensures` clauses **inherited**, can add more
- `opens_invariants` **inherited**, cannot modify
- `unwinding` **inherited**, cannot modify

### External Trait Specifications

**`#[verifier::external_trait_specification]`** - add specs to external traits:
```rust
#[verifier::external_trait_specification]
trait ExEncoder {
    type ExternalTraitSpecificationFor: Encoder;
    fn encode_value(&self, x: u64) -> (result: u64)
        ensures result >= x;
}
```

**`#[verifier::external_trait_extension]`** - add spec helper functions:
```rust
#[verifier::external_trait_extension(SummarizerSpec via SummarizerSpecImpl)]
trait ExSummarizer {
    spec fn spec_summary(&self) -> u64;
    fn summary(&self) -> (result: u64)
        ensures result == self.spec_summary();
}
```

**`obeys_*` pattern** (used by vstd):
```rust
spec fn obeys_eq_spec() -> bool;  // indicates if type follows spec
ensures Self::obeys_eq_spec() ==> r == self.eq_spec(other);
```

### `decreases ... when ... via ...`

**When clause:**
```rust
spec fn f(...) -> _
    decreases measure
    when condition
{
    // body only concretely specified when condition is true
}
```

**Via clause:**
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

### Type Invariants

**Declaration:**
```rust
#[verifier::type_invariant]
spec fn type_inv(self) -> bool { ... }
```

- Applied to structs/enums
- Must be spec function returning `bool`
- Type must have no public fields outside crate

**Enforcement:** Verus automatically checks invariant:
- On construction
- After field assignment
- After mutable borrow in function call

**Using the invariant:**
```rust
proof {
    use_type_invariant(&x);
}
assert(x.field <= x.other_field);  // succeeds
```

### Attributes Reference

| Attribute | Purpose |
|-----------|---------|
| `#![all_triggers]` | Aggressively select trigger groups |
| `#![auto]` | Use heuristics for triggers |
| `#![verifier::allow_complex_invariants]` | Allow invariant_except_break with loop_isolation(false) |
| `#![verifier::allow_in_spec]` | Allow exec fn with returns in spec mode |
| `#![verifier::atomic]` | Mark function as atomic for open_atomic_invariant |
| `#![verifier::external]` | Tell Verus to ignore item |
| `#![verifier::external_body]` | Trust body of function, only use signature |
| `#![verifier::ext_equal]` | Mark datatype for extensional equality |
| `#![verifier::inline]` | Auto-expand spec function definition |
| `#![verifier::loop_isolation]` | Control loop invariant inference |
| `#![verifier::memoize]` | Memoize compute/compute_only results |
| `#![verifier::opaque]` | Keep function body hidden by default |
| `#![verifier::reject_recursive_types]` | Reject recursive type definitions |
| `#![verifier::type_invariant]` | Declare type invariant |
| `#![verifier::when_used_as_spec]` | Use exec const as spec |
| `#![exec_allows_no_decreases_clause]` | Allow exec fn without decreases |
| `#![via_fn]` | Mark proof function for `via` clause |

---

*Lines 11501-12000 covered: opens_invariants, unwinding, Drop, signature inheritance, external trait specs, decreases when/via, type invariants, attributes reference*

---

## Sections 12001-12205 (Final)

### More Attributes

| Attribute | Purpose |
|-----------|---------|
| `#![verifier::rlimit(n)]` | Set solver rlimit for function (default 10 ≈ 2s) |
| `#![verifier::rlimit(infinity)]` | Remove solver rlimit |
| `#![via_fn]` | Mark proof function for `via` clause |
| `#![verifier::truncate]` | Silence recommends-check for out-of-range casts |
| `#![verifier::assume_termination]` | Assume exec function terminates |
| `#[trigger]` | Manually specify trigger groups (no verifier:: prefix) |

### `assume_specification`

Apply specs to existing external/unverified functions:
```rust
assume_specification<T>[core::mem::swap::<T>](a: &mut T, b: &mut T)
    ensures *a == *old(b), *b == *old(a);
```

**For associated functions:**
```rust
assume_specification<T>[Vec::<T>::new]() -> (v: Vec<T>)
    ensures v@ == Seq::<T>::empty();
```

### The `global` Directive

Provide layout information to Verus:
```rust
global layout T is size == n, align == m;
```

- Exports axioms `size_of::<T>() == n` and `align_of::<T>() == m`
- Creates static check that values are correct at compile time
- For usize/isize: influences integer range encoding

**Example:**
```rust
global layout usize is size == 4;

fn test(x: usize) {
    assert(x <= 0xffffffff);  // Passes - assumes 32-bit
    assert(usize::BITS == 32);
}
```

### Static Items

```rust
exec static x: u64 = 0;
```

- Similar to const but only exec mode (not spec)
- Cannot currently be referenced from spec expressions
- Must be explicitly marked `exec`

### The `char` Primitive

- Represents Unicode scalar values
- Valid range: `[0, 0xD7ff] ∪ [0xE000, 0x10FFFF]`
- In spec code: can cast to/from other integer types with `as`
- May be undefined if target range doesn't fit

### Unions

**Spec-mode operators:**
```rust
is_variant(u, "field_name")           // returns true if in variant
get_union_field::<U, T>(u, "field_name")  // get field value
```

**Example:**
```rust
union U { x: u8, y: bool }

let u = U { x: 3 };
assert(is_variant(u, "x"));
assert(get_union_field::<U, u8>(u, "x") == 3);
```

### Pointers and Cells (vstd)

- **PCell** - for cells
- **PPtr** - for pointers to fixed-size heap allocations
- **vstd::raw_ptr** - for `*mut T` and `*const T`

### Recording Executions

`--record` flag packages verification run for sharing/reproduction:
```bash
verus foo.rs --record  # Creates yyyy-mm-dd-hh-mm-ss.zip
```

---

## Summary Complete

**AGENTSf.md has 12205 lines total.** This summary covers:
- Lines 1-500: Verus overview, getting started
- Lines 501-1000: Basic specifications, requires/ensures
- Lines 1001-1500: Ghost code, const declarations, triangle example
- Lines 1501-2000: Recursion, loops, invariants
- Lines 2001-2500: Seq/Set/Map libraries
- Lines 2501-3000: Induction proofs, Fibonacci example
- Lines 3001-3500: forall/exists quantifiers, triggers
- Lines 3501-4000: choose, binary search, broadcast lemmas
- Lines 4001-4500: integer_ring, bit_vector, proof performance
- Lines 4501-5000: calc! macro, proof debugging
- Lines 5001-5500: Higher-order functions, closures, interior mutability
- Lines 5501-6000: TreeMap implementation, type invariants
- Lines 6001-6500: Generic TreeMap, TotalOrdered trait
- Lines 6501-7000: Full TreeMap source code
- Lines 7001-7500: External code integration
- Lines 7501-8000: Supported Rust features
- Lines 8001-8500: Verus syntax reference
- Lines 8501-9000: exec_spec macros, verus_spec attribute
- Lines 9001-9500: More verus_spec examples
- Lines 9501-10000: dual_spec, closures with specs
- Lines 10001-10500: verus_spec continued
- Lines 10501-11000: verus_verify examples
- Lines 11001-11500: Arithmetic, bitwise, triggers, function signatures
- Lines 11501-12000: opens_invariants, external traits, type invariants
- Lines 12001-12205: assume_specification, global directive, unions, char

---

*Summary generated from AGENTSf.md (12205 lines)*
