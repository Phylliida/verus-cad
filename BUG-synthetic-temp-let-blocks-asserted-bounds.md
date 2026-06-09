# Bug: synthetic temp let-bindings block asserted bounds from reaching overflow checks

## RESOLVED 2026-06-01 — closer reads through the `let` (`simp_all <;> omega`)

**Root cause confirmed exactly as described below.** For a self-assignment
`x = f(x)`, Verus's `ast_to_sst` snapshots the operand into a `VirTemp`
(`let tmp% := x`) and states the overflow obligation about `tmp% * k`, while
the user's asserted bound is about `x * k`. The default closer couldn't bridge
them: bare `omega` doesn't substitute a `let`-bound value (treats `tmp% * k` and
`x * k` as distinct opaque atoms — confirmed: even `intro`-ing the `let` then
`omega` fails), and bare `simp_all` zeta-reduces the `let` but isn't an
arithmetic decision procedure.

**Fix (the general one):** a single rung added to `tactus_auto` in
`TactusPrelude.lean` — `simp_all <;> first | omega | done`. `simp_all`
zeta-reduces the binding (unifying `tmp% * k` with `x * k`), then `omega` does
the arithmetic from the asserted `x * k ≤ B`. This combo already existed in the
ladder but only inside `tactus_case_split` (which throws when there's no
user-datatype local to split on, so an `Int`-typed let-guarded goal never
reached it); the fix lifts it to a standalone rung. It strictly subsumes the
bare `simp_all` rung it replaces. NOT a simp-set extension — it composes two
tactics already present (design principle #1 holds; it's the "layered
composition, not exclusive gates" shape). General over *any* let-guarded linear-
arithmetic goal, not just self-assignment.

**Rejected alternative — the suggested "B. inline the synthetic temp" (an
SST→SST pre-pass that removes `tmp%`).** Prototyped, then abandoned. Rationale
(Danielle's call): *keeping the `tmp%` consistently is more transparent than
special-casing its removal.* The pre-pass had to distinguish a genuine read-
before-write snapshot from look-alikes (branch-result merge temps like
`tmp%3 := tmp%1`, which escape their block and are read after an enclosing
`if`) — it shipped a soundness bug (18 regressions) on the first run, then
needed three guards (read-before-write, dead-after-reassign, escape-confinement)
plus a whole-function occurrence analysis to be sound. Worse, it was
*inconsistent* (removed bare-`Var` snapshots but kept complex-RHS temps) and
*incomplete* (complex-RHS temps still block `omega`, so the closer rung would
be needed anyway). The `tmp%` is what Verus actually emits; rendering it
faithfully and absorbing it uniformly in the closer is simpler, sound, general,
and predictable. See DESIGN.md § "Self-assignment snapshot temps".

**Pinned by** `test_self_assign_mul_overflow_bound` (475 e2e, 0 regressions).

Everything below is the original report, preserved.

---

## Summary

When an exec fn body writes `x = expr` (assigning to a variable that appears in `expr`), Tactus's WP generation introduces a synthetic `tmp__1 := x` let-binding in the obligation context, and the overflow check on the operation is stated in terms of `tmp__1 * (...)` rather than `x * (...)`. Inline `assert(P) by { ... }` bounds proved *about the source-name version* (`x * (i + 1) ≤ 10000`) sit in the hypothesis chain but **don't reach the obligation** — the default closer (`omega`/`simp_all`/etc.) doesn't substitute the let-binding to connect them.

The practical consequence: the natural pattern "prove a bound on the expression, then assign" doesn't close the overflow check, even though the bound is *exactly* what the check needs.

## Minimal reproducer

```rust
use verus_builtin::*;
use verus_builtin_macros::*;

verus! {

import Mathlib.Tactic.Linarith

#[verifier::tactus_auto]
fn f(n: u64) -> (r: u64)
    requires n <= 10
    ensures r == 0
{
    let mut x: u64 = 5;
    let mut i: u64 = 0;
    while i < n
        invariant i <= n, n <= 10, x <= 1000
        decreases n - i
    {
        // Prove bounds on the expression we're about to assign.
        assert(x * (i + 1) <= 10000) by { intros; nlinarith };
        assert(0 <= x * (i + 1)) by { intros; nlinarith };
        // Self-assignment — generates a `tmp__1 := x` let in the obligation.
        x = x * (i + 1);
        i = i + 1;
    }
    0
}

fn main() {}

} // verus!
```

Expected: verifies. The two `assert(P) by { … nlinarith }` lines prove *exactly* the upper and lower bounds the overflow check needs.

Actual: the overflow check on `x = x * (i + 1)` fails. The goal in the obligation:

```
x * (i + 1) ≤ 10000 →
  x * (i + 1) ≤ 10000 →
    0 ≤ x * (i + 1) →
      0 ≤ x * (i + 1) →
        let tmp__1 := x;
        0 ≤ i + 1 ∧ … →
          0 ≤ i + 1 ∧ … →
            0 ≤ tmp__1 * (i + 1) ∧ tmp__1 * (i + 1) < 18446744073709551616
```

The asserted bounds are right there (duplicated, even — init + maintain). The goal uses `tmp__1 * (i + 1)`. Since `tmp__1 := x` (let-binding), `tmp__1 * (i + 1)` and `x * (i + 1)` are definitionally equal. But omega doesn't see through the let, and simp_all doesn't auto-unfold the synthetic temp, so the conclusion-via-substitution doesn't fire.

## Workarounds tried, all unsatisfying

1. **Fn-level `#[verifier::tactus_tactic("first | tactus_auto | (intros; show … ; omega)")]`.** A `show` with the substituted goal works *for this obligation*, but the same tactic applies to *every* obligation in the fn — and the other obligations (loop invariant maintains, the postcondition, etc.) have different goal shapes that the `show` pattern doesn't match. Fails with `'show' tactic failed, pattern X is not definitionally equal to target Y`.

2. **`simp_all`-with-config or `unfold_let *`** in the override. `unfold_let` is "unknown tactic"; `simp_all` doesn't expand synthetic temps by default.

3. **Manually naming `tmp__1`** to rewrite it. Can't — the synthetic name has the `✝` suffix after `intros` and isn't reliably typeable.

4. **`nlinarith` in the override.** Same issue: doesn't substitute the let. Counterexample shows `g := result * (i + 1)` (the temp-substituted form) but no equation linking it to the asserted bound.

5. **Restructuring to avoid the self-assignment.** Tried `let next = x * (i + 1); x = next;` — Tactus still introduces a temp for the right-hand side at the assignment, same shape, same failure.

## Why this is the gating issue for "iterative impl verified against recursive spec"

After last week's fixes (as-nat-cast, exec-fn-imports, multi-var-loop names, helper proof fn calls), I expected the canonical factorial pattern to work cleanly:

```rust
proof fn fact_recurrence(n: nat) requires n >= 1 ensures fact(n) == n * fact((n - 1) as nat) by { ... }
proof fn fact_monotone(k: nat, m: nat) requires k <= m ensures fact(k) <= fact(m) by { ... }
proof fn fact_bound() ensures fact(10 as nat) <= 3628800 by { repeat (unfold fact; simp) }

#[verifier::tactus_auto]
fn factorial(n: u64) -> (r: u64)
    requires n <= 10
    ensures r as nat == fact(n as nat)
{
    let mut result: u64 = 1;
    let mut i: u64 = 0;
    // … initial assert that result = fact(0) …
    while i < n
        invariant i <= n, n <= 10, result as nat == fact(i as nat), result <= 3628800,
        decreases n - i
    {
        // Recurrence + bound, inline via helper proof fns.
        assert(fact((i + 1) as nat) == (i + 1) * fact(i as nat)) by { …fact_recurrence… };
        assert(result * (i + 1) <= 3628800) by { …fact_monotone + fact_bound… };
        assert(0 <= result * (i + 1)) by { intros; nlinarith };
        result = result * (i + 1);   // ← THIS OPERATION FAILS the overflow check
        i = i + 1;
    }
    …
}
```

Every individual piece verifies. The last step — using the proved bounds to discharge the overflow obligation — fails. With the synthetic-temp substitution working, this whole chain would close and we'd have a clean tutorial chapter for "exec verified against recursive multiplicative spec."

(For `sum_iter` in tutorial chapter 1 this works because the body is `result = result + i`, which doesn't need a bound override — `omega` handles the addition directly. The wall is specifically multiplicative operations.)

## Suggested fix directions

Two paths, both targeting the same root cause:

### A. Auto-unfold synthetic temps in the default closer (preferred)

Before running the `omega`/`simp_all` ladder in `tactus_auto`, add a normalization step that unfolds the synthetic `tmp__N` let-bindings. The `simp_all` already runs but doesn't expand these — adding `simp only [show tmp__1 = x from rfl]` (or the more general `simp_all (config := { etaStruct := .all })` etc.) for each synthetic temp in the goal would do it.

Even more targeted: emit synthetic temps as `unfold`-able by the closer, e.g., by tagging them with a `@[reducible]` attribute, or by having `tactus_auto` start with a fixed `intros; try repeat unfold_let` prelude.

### B. Inline the synthetic temp into the obligation directly

At WP generation time, when emitting the overflow check for `x = expr`, just write the obligation in terms of `expr` rather than introducing a `tmp__N := original_x` and writing `tmp__N`-vs-something. The synthetic temp seems to be there to track the *prior* value of `x` for some reason (maybe for a frame condition?), but the overflow check itself only cares about the RHS, not the prior value.

This is a deeper restructuring but eliminates the let entirely.

## Severity

High for the "iterative-impl-vs-recursive-spec with multiplication" use case. Specifically:

- **Factorial** — exact pattern.
- **Power-of-n / `pow_by_squaring`** — same shape.
- **Modular multiplication** (e.g., crypto routines) — same shape, just with `(x * y) % M`.
- Any algorithm where the loop body's multiplication needs a non-trivial bound to avoid overflow.

Lower severity for additive recurrences (sum_iter works) and for closed-form invariants (chapter 1's `2 * result == i * (i + 1)` shape is unblocked).

## Discovered while

Writing tutorial chapter 4 (iterative factorial verified against recursive `fact` spec) after fib_iter landed in chapter 2. fib_iter works because addition's overflow check is `omega`-friendly even with the synthetic temp; factorial doesn't because the multiplication needs the asserted bound, and that bound can't reach through the temp.
