# BUG: a call result's `let` binding is goal-position and unnameable inside `assert … by { }` (lean-backend)

**Severity:** blocks any `--lean-backend` exec fn that binds a function-call
result (`let x = f(..)`) and then needs a **multi-step** proof *about* `x` in an
`assert … by { }` — i.e. one that must reference `x` by name to apply a lemma to
it. Concretely it blocks the ch8 matrix-Fibonacci capstone (`fib_matrix`), whose
one-line wrapper `let q = qpow_exec(n); … q.a == F(n+1) …` cannot name `q`.

**Status:** ✅ CORE FIXED 2026-06-09 (tactus `3117200`, Approach A). The call
result is now nameable in `assert(..) by { }`. One *separate* gap remains for
the full ch8 path — a proof fn referenced ONLY inside an assert-by block isn't
emitted into the per-fn `.lean` (see "Remaining: assert-by proof-fn emission"
below). Found 2026-06-09; minimized + every claim run against the verus binary
(Lean 4.25.0).

## Resolution (Approach A)

`push_post_call_frames`'s ∀-path now names the ∀-bound result with the **dest's
source name** (when the dest is a simple var) and drops the alias `let`, so the
assert theorem reads `(x : S) (h : … x …) : … x …` — `x` is a real binder the
by-block can reference. omega and `assumption` both still close (no goal-`let`
to zeta). Guard: keep the gensym for the self-referential `let x = f(x)` case
(the arg `x` is free in the substituted ensures and a `∀ x` would capture it).

Validated: the minimal repro's exact proof (`have h : sview x = 0 := by
assumption; exact h`) verifies 3/0; multi-step derivation (`name → unfold the
ensures → omega`) verifies; the self-ref guard verifies; full suite 504/0.
Pinned by `test_exec_call_result_{nameable_in_assert, derive_in_assert,
self_ref_keeps_gensym}`.

> **Update 2026-06-09:** the full ch8 path now verifies end-to-end (`fib_matrix`
> + `qpow_exec`, 16/0). `qpow_topleft` — referenced *only* in `fib_matrix`'s
> assert-by — **is emitted** (declared in the generated `fib_matrix.lean`), so the
> gap below does not block ch8 in practice (either it was addressed, or
> `qpow_topleft` is reachable via the exec-fn over-approximation). Re-confirm
> whether the minimal isolated case below still reproduces.

## Remaining: assert-by proof-fn emission (separate, for the full ch8 path)

A proof fn referenced ONLY in an `assert(..) by { have := f args; … }` block
(not in any require/ensure) is **not emitted** into the exec fn's per-fn
`.lean` → "Unknown identifier `f`". Confirmed minimal: `lemma_view_pos q (by
assumption)` in an isolated assert-by appears only as a *reference* in the
generated file, never declared. Root: the exec-fn helper/dep walk seeds from
require/ensure refs, not from assert-by tactic-text proof-fn names. (This is the
real shape of the report's old "related finding 1"; the workaround it named —
"use assert-by `have := f a b`" — itself needs `f` emitted.) ch8 `fib_matrix`
needs `qpow_topleft (view q)`, so this must work for the capstone to close
unless the lemma is already reachable via other refs. Fix shape: scan assert-by
/ proof-block tactic text for proof-fn names when seeding the exec-fn helper
set (the proof-fn files already do a textual `ident_appears` scan — DESIGN
§ "Proof-fn helper emission").

This is the same family as the loop-local-names issue (a synthetic binder's
*source name* isn't accessible in the tactic block), now for **call results in
straight-line code**, not loop locals.

## Minimal repro (`REPRO-call-result-let-unnameable.rs`, alongside this file)

```rust
struct S { a: u64 }
spec fn sview(s: S) -> nat { s.a as nat }

#[verifier::tactus_auto]
fn mk() -> (r: S)
    ensures sview(r) == 0
{ S { a: 0 } }

#[verifier::tactus_auto]
fn use_it() {
    let x = mk();                            // x : S, ensures sview(x) == 0
    assert(sview(x) == 0) by {
        have h : sview x = 0 := by assumption // FAILS: Unknown identifier `x`
        exact h
    };
}
```

```
error: Lean tactus_auto failed for use_it:
       Unknown identifier `x`
```

## Root cause: the call result is a *goal-position* `let`, not a context local

The generated assert theorem (from `target/tactus-lean/<f>/use_it.lean`):

```lean
theorem _tactus_assert_use_it_at__cr_12_12_2
    (_tactus_ret_1 : S)
    (_h_ctx_0 : 0 ≤ _tactus_ret_1.a ∧ _tactus_ret_1.a < 18446744073709551616)
    (_h_ctx_1 : sview _tactus_ret_1 = 0) :
    let x := _tactus_ret_1;                       -- ← x is bound by the GOAL's `let`
    sview x = 0 := by
  …
```

The call result is `_tactus_ret_1` (a theorem parameter); the source name `x`
appears only as a **goal-position `let x := _tactus_ret_1`**. It is *not* in the
local context, so writing `x` in a tactic (`have h : … x …`, `rw`, or applying a
lemma to `x`) is an unbound identifier → "Unknown identifier `x`".

## Evidence ladder (each run; OK = closes, FAIL = doesn't)

| Proof of `assert(sview(x) == 0) by { … }` | Result |
|---|---|
| `have h : sview x = 0 := by assumption; exact h`  (names `x`) | **FAIL** — `Unknown identifier x` |
| `assumption`  (no naming; consumes the goal `let` via zeta) | **OK** (3 verified, 0 errors) |
| `intro x; have h : sview x = 0 := by assumption; exact h` | **FAIL** — `No goals` / `unsolved goals` |

So: a proof that **never names** the result (`assumption`/`omega`/`simp_all`,
which zeta-reduce the goal-position `let`) works; **naming** it fails; and
`intro x` to move the `let` into context does **not** cleanly help.

The catch: the no-naming workaround only covers goals that are *directly* a
hypothesis. A goal that must be **derived** — apply a lemma to the result, then
combine — has no `assumption`-only proof, and is therefore blocked.

## Where it bit (the real blocker)

ch8 `fib_matrix`:

```rust
let q = qpow_exec(n);   // ensures view(q) == Q^n   (q : an exec 2×2 matrix)
assert(q.a as nat == fib((n + 1) as nat)) by {
    // need: q.a == (Q^n).a == F(n+1), via `qpow_topleft (view q)`.
    // but `view q` / `q.a` reference q → Unknown identifier `q`.
};
```

The goal `q.a as nat == fib(n+1)` is **not** a hypothesis — it must be derived
from `view q == Q^n` (the ensures) plus the lemma `qpow_topleft : (Q^n).a ==
F(n+1)`. That derivation must name `q` (or `view q`), which is impossible. No
`assumption`-only proof exists. (Pushing `r.a == F(n+1)` into `qpow_exec`'s own
ensures sidesteps `fib_matrix` but then runs into the "multi-clause ensures
bundles into one conjunction hyp" friction below.)

## Proposed fix

Introduce the call-result `let` into the **local context with its source name
accessible** (the same shape the loop-local-names fix gave loop locals), so `x`
is a writable local in the `by { }` block. Equivalently: make `intro <name>`
reliably name it (today it errors with `No goals`). Then both the no-naming and
the lemma-applying proofs work.

## Related findings (same exec-proof cluster, surfaced building ch8 — lower priority)

These each have their own clean workaround; noting them together since they form
the friction wall for "prove something nontrivial about a call result":

1. **`proof { f(args); }` blocks emit Verus call syntax verbatim into Lean.**
   A `proof { entries_bounded(half, (n/2) as nat, n as nat); }` block lands in
   the generated Lean as literally `entries_bounded(half, (n / 2) as nat, …)` —
   Rust call syntax with `as nat`, which is invalid Lean → "unknown tactic".
   Workaround: never call a proof fn from a bare `proof { }`; use
   `assert(P) by { have := f a b (by …); … }` (the `by { }` block *is*
   Lean-translated, so `f a b` in Lean application syntax works there).

2. **A callee's multi-clause `ensures` bundles into a single conjunction hyp at
   the call site.** With `ensures view(r) == …, r.a as nat == …`, the caller sees
   one hypothesis `view r = … ∧ r.a.toNat = …`, so `by { assumption }` for just
   the `view` clause fails (it's not the whole conjunction). Workaround:
   destructure (`.1`) or `obtain` — but combined with finding (the unnameable
   result) and let-aliasing, this gets fragile fast.

3. **Nullary spec fns render with inconsistent arity across files.** A 0-arg
   `spec fn mat_q() -> Mat2` is `mat_q : Mat2` in the per-fn Lean file but
   `mat_q (no_param : Int) : Mat2` (called `mat_q 0`) in the aggregate
   `main.lean`, so a proof that writes bare `mat_q` typechecks against one file
   and not the other. Workaround: don't use nullary spec fns — inline the value
   as a literal (`Mat2 { a:1, b:1, c:1, d:0 }`), which renders identically
   everywhere. (Used throughout ch8.)

## After the fix

ch8's `fib_matrix` (and any exec fn proving a derived fact about a call result)
closes directly: `let q = qpow_exec(n); assert(q.a as nat == fib((n+1) as nat))
by { have hv : view q = … := by assumption; have ht := qpow_topleft n.toNat; … ;
omega }`. The whole matrix-Fibonacci capstone (the verified O(log n) `qpow_exec`
by-squaring + the trivial `F(n+1)` extractor) then verifies end to end.
