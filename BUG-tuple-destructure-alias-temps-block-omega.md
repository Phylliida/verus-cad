# BUG: tuple-destructuring alias temps block omega/simp_all (lean-backend)

**Severity:** blocks any `--lean-backend` exec fn that destructures a
tuple-returning call (`let (a, b) = f(..)`) and then needs `omega`/`nlinarith`
to reason about `a`/`b` via the call's `ensures`. Concretely it blocks the
fast-doubling Fibonacci chapter (ch7), whose recursive `fast_fib` returns
`(F(n), F(n+1))`.

**Status:** ✅ RESOLVED 2026-06-07 (design decision **E**; gate `f301110`,
tests + docs to follow). Fully root-caused + minimized below (every claim run
against Lean 4.25.0 / the lean-project, and against the verus binary).

## Resolution

Refined root cause: the breakage is **specific to the `assert(P) by { tac }`
path**, not tuple temps in general. `emit_with_closer` injects `intro
<let-names>;` before the user tactic, converting the goal-position let-alias
chain into opaque **tuple-typed `ldecl`s** — and omega/simp_all can only zeta
*goal-position* lets, not ldecls, so the projection never reaches `ret.2`.

Two consequences worth recording:
- **The auto-generated tuple-return postconditions were NOT affected** (contra
  the "Why it can't be worked around" section's ch7 claim). Auto theorems go
  through `emit_split`, which does **not** intro — so `tactus_auto`'s
  `simp_all <;> omega` rung zeta-reduces the goal-position lets and closes. If a
  ch7 tuple-return postcondition still fails, it's a *different* issue (most
  likely spec-fn-in-goal-position needing an explicit `unfold`, the same gap the
  minimal repro's `h` actually hits — `p.0 as nat == f(m)` needs `f` unfolded,
  not a tuple-alias problem).
- **Neither proposed fix was taken.** Fix #1 (generation-side temp removal) is
  the escape-analysis-delicate pattern DESIGN § "Self-assignment snapshot temps"
  rejects (a bare-Var alias is shape-identical to a branch-merge temp). Fix #2
  (closer-side `simp only`/`subst`) was tried first (commit 4ed848e) but
  **rejected on transparency grounds** — injecting `simp only [<lets>]` before
  the user's tactic is hidden goal-rewriting the user didn't write ("and then a
  simp happened"), which design principle #1 forbids.

The landed fix is a **subtraction**, not an injection, and it resolves to a
single rule (design decision **E**): **`emit_with_closer` injects `intro
<names>;` ONLY when `remaining` carries a `Binder` frame** (a loop local blocked
behind a Let that would otherwise get an inaccessible `i✝` dagger name —
BUG-loop-local-names). `Let` frames (synthetic temps the user never names) and
`Hyp` frames (anonymous `→` antecedents) are NOT intro'd: omega's own zeta
reduces goal-position lets, and omega/simp_all intro `→` themselves. So `by {
omega }` runs on the real goal — generated Lean is literally `omega`.

**The clean contract: the user tactic owns its own intro.** Intro-aware tactics
(`omega`, `simp_all`) need nothing; non-intro-aware Mathlib tactics (`nlinarith`
/ `linarith` / `ring`) write `by { intros; nlinarith }` (already the documented
idiom). This was chosen over a type-aware "intro all *but* tuple-typed lets"
gate (option A): a general rule beats a special case, and the user's `intros` is
*visible in their tactic*, not a hidden Tactus step.

**Why not the obvious blanket gates** (the comprehensive battery forced this
out): "intro unless all-`Let`" (fd557a7) breaks a *second* `by { omega }` assert
— the first assert's result becomes a trailing `Hyp`, so the gate intros the
lets again. "Always intro" is the original bug. Only "intro for a `Binder`" is
consistent — at the cost of the user owning intro for non-intro-aware tactics.

**Honest consequences (both visible, not hidden):** `by { intros; omega }`
fails (the user's own `intros` makes the ldecls — the clean idiom is `by {
omega }`); and `by { nlinarith }` now needs `by { intros; nlinarith }`.

ch7's bound/overflow asserts can drop their brittle `simp only [<temp names>]`
crutches. Pinned by the `test_exec_tuple_destructure_*` battery — omega /
simp_all / default-closer / both-elements / triple / construction-postcondition
/ loop-interaction, plus wrong-bound and user-intros-fails negatives — and
`test_self_assign_mul_overflow_bound` (the `intros; nlinarith` idiom, the one
existing test updated for E). Clean repro `make_pair`/`use_pair` → **3/0**
(generated assert tactic = just `omega`). Full suite **498/0**, lean_verify
**269/0**, vstd **1530/0**. (Superseded the rejected simp-injection `4ed848e`;
gate landed `f301110`.)

Note also (validated by the battery): **the auto-generated tuple-*construction*
postconditions verify** (`test_exec_tuple_construction_postcondition`) — the
auto path (`emit_split`) never intros, confirming the ch7 postcondition concern,
if any, is a different issue (spec-fn-in-goal-position unfold), not this one.

## Minimal repro (`REPRO-tuple-let-alias.rs`, alongside this file)

```rust
spec fn f(x: nat) -> nat decreases x { if x == 0 { 0 } else { f((x - 1) as nat) + 1 } }

#[verifier::tactus_auto]
fn h(m: u64) -> (p: (u64, u64))
    requires f(m as nat) <= 100
    ensures p.0 as nat == f(m as nat), p.1 as nat == f((m + 1) as nat)
{ (m, m + 1) }

#[verifier::tactus_auto]
fn g(n: u64) -> (res: u64)
    requires f((n + 1) as nat) <= 100
    ensures true
{
    let (a, b) = h(n);                      // b.toNat = f(n+1)  (from h's ensures)
    assert(b <= 100) by { intros; omega };  // FAILS: omega can't prove b ≤ 100
    a
}
```

```
omega could not prove the goal:
  a possible counterexample may satisfy the constraints
    d ≥ 101
  where
   d := tmp___0.snd      ← b, behind the tuple-alias temps
```

`b.toNat = f(n+1)` is in scope (h's ensures) and `f(n+1) ≤ 100` is the precond,
so `b ≤ 100` — but omega can't see it.

## Root cause: redundant tuple-alias temps

`let (a, b) = h(n)` lowers to a chain of let-bound fvars:

```lean
let tmp__1  := _tactus_ret_8     -- _tactus_ret_8 : Int × Int (the call result)
let tmp___0 := tmp__1            -- redundant alias of a *tuple*
let a := tmp___0.1
let b := tmp___0.2
```

omega/`simp_all` **cannot reduce the tuple-typed intermediate lets**
(`tmp__1`, `tmp___0`) to push the projection down to `_tactus_ret_8.2`, so `b`
(= `tmp___0.2`) never connects to the `ensures` (which is stated over
`_tactus_ret_8.2`). They're stuck atoms.

## Evidence ladder (each run; OK = closes, FAIL = doesn't)

Goal: `(let tmp__1 := ret; let tmp___0 := tmp__1; let a := tmp___0.1; let b := tmp___0.2; b ≤ 100)`
with hyps `hens : … ∧ ret.2.toNat = f (Int.toNat (n+1))`, `hpre : f (Int.toNat (n+1)) ≤ 100`,
after `intro tmp__1 tmp___0 a b`:

| Tactic | Result |
|---|---|
| `omega` | **FAIL** |
| `simp_all <;> omega` | **FAIL** |
| `simp only [] (config := { zetaDelta := true }) [at *]` then omega | **FAIL** |
| `simp_all (config := { zetaDelta := true })` | **FAIL** |
| `extract_lets at *; omega` | **FAIL** |
| `simp only [a, b, tmp__1, tmp___0] at *; omega`  (name the lets) | **OK** |
| `subst a b tmp__1 tmp___0; omega` | **OK** |

And isolating *why* it's the tuple aliases specifically:

| Goal shape | omega |
|---|---|
| chained tuple aliases (`tmp___0 := tmp__1 := ret`, `a := tmp___0.1`) | **FAIL** |
| **single direct** projection let (`let a := ret.1; let b := ret.2`) | **OK** |
| direct projection *equality hyps* (`a = ret.1`, `b = ret.2`) | **OK** |
| tuple *equality hyps* (`tmp___0 = tmp__1`, `a = tmp___0.1`) | **FAIL** |

So: omega *does* zeta a single direct projection let and *does* use direct
projection equalities — it only chokes on the **redundant tuple-alias chain**.

## Why it can't be worked around author-side (the real blocker)

For an **assert**, I can prepend `simp only [a, b, tmp__1, tmp___0] at *` to name
and collapse the lets (this is how ch7's `b ≤ 2^31` / `a ≤ b` / overflow asserts
pass today — but it's brittle: it hard-codes Verus's generated temp names).

The **tuple-return postconditions are auto-generated** — there's no `by {}`
block to attach a `simp only` to. In ch7, the odd branch returns `(d, c + d)`,
which lowers to `tmp__4 := d; res := (tmp__4, c+d)`. The postcondition
`res.0 as nat == fib n` then can't bridge `res.0 → tmp__4 → d`, **even though an
assert one line up proves `d as nat == fib n`**. (Tell-tale asymmetry: the even
branch returns `(c, d)` with no temp for the 2nd element, so `res.1 = d`
directly and *that* postcondition closes; the odd branch's `tmp__4` temp breaks
the matching one.)

## Proposed fix (either; first is cleaner)

1. **Generation-side — don't emit the redundant alias temps.** Collapse
   `tmp__1 := ret; tmp___0 := tmp__1; a := tmp___0.1` to a direct
   `a := ret.1` (and likewise the tuple-construction temp `tmp__4 := d`).
   The evidence ladder shows a *single direct* projection let closes under
   omega with no help. This also removes pointless double-aliasing.

2. **Closer-side — collapse value-lets before omega/nlinarith.** Have the
   default closer `subst` (or `simp only [<them>]`) the let-bound fvars in the
   local context generically (enumerate the `let`-decls). `subst <names>`
   closes the repro; the closer would just need to gather the names rather than
   the author hard-coding them. (No name-free `simp` config works —
   `zetaDelta` doesn't reduce these, see table.)

## After the fix

ch7's bound/overflow asserts can drop their brittle `simp only [<temp names>]`
crutches, and the tuple-return postconditions (`res.0 → tmp__4 → d`) close — so
the even-`c` / odd-`cd` doubling-identity proofs can be written cleanly. The
`F(2k+1) = F(k)² + F(k+1)²` identity (even-`d`, odd-`d`) and everything else in
`fast_fib` already verify; this is the last blocker. (Current ch7 state is
committed as a WIP scaffold; `chapters/0–6` all verify `0 errors`.)
