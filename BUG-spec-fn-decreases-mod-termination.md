# BUG: spec/proof fn `decreases` measure needing `%` (mod) fails termination

**Severity:** blocks any spec fn whose recursion terminates by a modular measure — most visibly **Euclidean gcd**, the natural next tutorial chapter.

**Status:** ✅ RESOLVED 2026-06-06 (tactus `9eebbbb` spec fns + `d33f3a9`
proof fns). Found while starting Chapter 6 (gcd).

## Resolution

Both the spec-fn path (the Chapter-6 blocker) and the symmetric proof-fn path
are fixed. Recursive spec/proof fns now emit an explicit `decreasing_by`:

```
all_goals (first | omega | (apply Nat.mod_lt <;> omega) | decreasing_tactic)
```

extracted as `DECREASING_BY_TACTIC` in `to_lean_fn.rs`, gated on a non-empty
`termination_by` (a bare `decreasing_by` on a non-recursive def/theorem is a
Lean error). The `decreasing_tactic` fallback preserves today's behaviour for
structural / `sizeOf` measures, so nothing regressed.

- **Spec fns** (`9eebbbb`): `spec_fn_to_ast` now passes the const instead of
  `None`. Pinned by `test_spec_fn_mod_decreases` (gcd) +
  `test_spec_fn_sub_decreases` (subtractive-Euclid regression guard).
- **Proof fns** (`d33f3a9`): the `Theorem` AST struct had **no**
  `decreasing_by` field at all — added it (mirroring `Def`), rendered in
  `write_theorem` after `termination_by`, populated in `proof_fn_to_ast` from
  the same const. Pinned by `test_proof_fn_recursive_mod_decreases` (e2e) +
  `theorem_with_decreasing_by` (pp render).

This is **termination-replay, not verification** — Verus's `decreases` checker
already certified termination; the clause only re-establishes it for Lean's
kernel to accept the recursive `def`/`theorem`. Visible in the generated
`.lean`, same substrate-class pattern as the datatype `height` fn's
`decreasing_by`. (The `Nat.mod_lt` branch was verified independently against
Lean 4.25.0, including the fallback case the proposed-fix examples below didn't
exercise.)

Validated: tactus e2e **488/0**, lean_verify lib **269/0**, vstd **1530/0**.
Chapter 6 (gcd) is unblocked.

## Symptom

This minimal spec fn fails to verify:

```rust
spec fn gcd(a: nat, b: nat) -> nat
    decreases b
{
    if b == 0 { a } else { gcd(b, (a % b) as nat) }
}
```

```
failed to prove termination, possible solutions:
    - Use `have`-expressions to prove the remaining goals
    - Use `termination_by` ...
    - Use `decreasing_by` ...
  a b : ℕ
  h✝ : ¬b = 0
  ⊢ a % b < b
```

Because `gcd` then fails to compile, *everything* downstream breaks too
(`unfold gcd` reports "failed to unfold `gcd`", etc.) — but the root cause is
this single termination goal.

## Scope: it's specifically `%`, not arithmetic measures in general

A **subtractive** Euclid with a `decreases a + b` measure verifies cleanly
(`2 verified, 0 errors`):

```rust
spec fn gcd_sub(a: nat, b: nat) -> nat
    decreases a + b
{
    if b == 0 { a }
    else if a == 0 { b }
    else if a >= b { gcd_sub((a - b) as nat, b) }   // obligation: (a-b)+b < a+b
    else { gcd_sub(a, (b - a) as nat) }             // obligation: a+(b-a) < a+b
}
```

So Lean's default `decreasing_by` tactic *does* handle Nat-subtraction
obligations (`(a - b) + b < a + b`), and it handles the simple `(n - 1) < n`
shape that `fact`/`pow`/`fib` rely on. It just can't discharge the **modular**
obligation `a % b < b`, which needs `Nat.mod_lt` + the `b ≠ 0` hypothesis.
(Note: `omega` *also* can't prove `a % b < b` here — it only handles `%` by
*literal* divisors, and `b` is a variable. See "Proposed fix" for the tested
tactic.)

## Root cause

`spec_fn_to_ast` emits spec-fn definitions with **no** `decreasing_by`,
falling back to Lean's default decreasing tactic:

`source/lean_verify/src/to_lean_fn.rs:213`
```rust
Command::Def(Def { attrs, name, binders, ret_ty, body, termination_by, decreasing_by: None })
                                                                        // ^^^^^^^^^^^^^^^^^^^^^
```

The generated Lean confirms it (`target/tactus-lean/.../gcd_step.lean`):
```lean
noncomputable def gcd (a : Nat) (b : Nat) : Nat :=
  if b = 0 then a else gcd b (a % b)
termination_by b          -- ← no `decreasing_by`, so Lean's default tactic runs
```

The **datatype-recursion** path already emits an omega-based clause and works
for its sizeOf obligations:

`source/lean_verify/src/to_lean_fn.rs:1049-1050`
```rust
termination_by: vec![termination],
decreasing_by: Some("all_goals (simp_all; omega)".to_string()),
```

(Proof fns have the same gap: `proof_fn_to_ast` builds a `Theorem` whose
renderer — `lean_pp.rs` ~336-347 — emits `termination_by` but never a
`decreasing_by`. Not needed for gcd's *spec* fn, but a recursive *proof* fn
with a modular measure would hit the identical wall. A complete fix covers
both; the spec-fn path is the immediate blocker.)

## Proposed fix

Give `spec_fn_to_ast` (line 213) an explicit `decreasing_by`:

```rust
decreasing_by: Some("all_goals (first | omega | (apply Nat.mod_lt <;> omega) | decreasing_tactic)".to_string()),
```

**This exact string is tested** against the Lean 4.25.0 toolchain (`lean` on
each `example` below, exit 0):

```lean
-- the gcd goal — variable divisor; omega CANNOT, Nat.mod_lt CAN:
example (a b : Nat) (h : ¬ b = 0) : a % b < b := by apply Nat.mod_lt; omega
-- the fact/pow/fib measure — omega closes it:
example (n : Nat) (h : ¬ n = 0) : n - 1 < n := by omega
-- the combined string closes both, and `decreasing_tactic` is callable:
example (a b : Nat) (h : ¬ b = 0) : a % b < b := by
  first | omega | (apply Nat.mod_lt <;> omega) | decreasing_tactic
example (n : Nat) (h : ¬ n = 0) : n - 1 < n := by
  first | omega | (apply Nat.mod_lt <;> omega) | decreasing_tactic
```

**Correction to my first take:** I initially proposed `first | omega |
(simp_all; omega)`, on the assumption `omega` handles `a % b < b`. It does
**not** — `omega` only reasons about `%`/`/` by *literal* divisors, and here the
divisor `b` is a variable. Direct test:

```
example (a b : Nat) (h : ¬ b = 0) : a % b < b := by omega
  ⊢ error: omega could not prove the goal; a possible counterexample …
```

So the modular branch genuinely needs `Nat.mod_lt` (or `Int.emod_lt_of_pos` on
the Int side). The three branches, in order:

- `omega` — closes the `(n − 1) < n` and Nat-subtraction measures (`fact`,
  `pow`, `fib`, subtractive Euclid). These currently pass via Lean's default, so
  no regression.
- `apply Nat.mod_lt <;> omega` — closes `a % b < b` (`apply` leaves the side
  goal `b > 0`, which `omega` gets from `¬ b = 0` in context). This is the fix.
- `decreasing_tactic` — Lean's **default** decreasing tactic, kept as a final
  fallback so any spec fn in vstd / other crates that recurses on a structural /
  `sizeOf` / height measure (which neither `omega` nor `Nat.mod_lt` handles)
  still terminates exactly as it does today. `first` backtracks cleanly on the
  failed earlier branches, so the fallback sees the untouched goal.

(Alternatively/additionally: honor a Verus `decreases b via gcd_term` /
`#[via_fn]` clause by threading it into `decreasing_by`. But the form above is
simpler and needs no surface-syntax work; `f.decrease` is the only field
currently consulted.)

## Regression to run after the fix

The 7 existing chapter `.rs` files all currently verify (`0 errors`) via the
*default* decreasing tactic. After switching spec fns to an explicit
`decreasing_by`, confirm none regressed:

```bash
cd tactus-tutorial
for f in chapters/*/*.rs; do
  printf "%s :: " "$f"
  PATH="$HOME/.elan/toolchains/leanprover--lean4---v4.25.0/bin:$PATH" \
    ../tactus/source/target-verus/release/verus "$f" 2>&1 | tail -1
done
# every line should still end in `0 errors`
```

Then the gcd spec above should verify, unblocking Chapter 6.

## Notes for the chapter

Once fixed, the mod-based `gcd` is the *right* spec for the chapter — its charm
is that `gcd(a,b) = gcd(b, a%b)` **is** the loop step, so the
iterative-vs-recursive gap is nearly zero. The exec loop's own `decreases y`
(needing `x % y < y`) goes through the *exec* closer (`tactus_auto`/`omega`),
which already handles it — only the **spec fn definition's** termination is
stuck on this bug.
