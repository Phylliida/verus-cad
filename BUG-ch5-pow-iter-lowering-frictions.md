# Bug: three lowering frictions block exec-fn verification with recurrence invariants

## RESOLVED — `pow_iter` verifies (frictions 1 & 2 fixed)

Frictions 1 and 2 are both **fixed**, and `chapters/05-fast-exponentiation/
pow_by_squaring.rs` now verifies end-to-end (`6 verified, 0 errors`), including
the iterative `pow_iter` against the recursive `pow` spec.

- **Friction 1** (unsplit invariant conjunction): fixed — the invariant arrives
  as individual hypotheses.
- **Friction 2** (ℤ-vs-ℕ rendering): fixed — `(x as nat)` lowers consistently.

Two minor residuals remained and were worked around author-side (candidates for
a future polish, would let the proof shrink — not blockers):

1. **Friction 3** (`e.toNat`-vs-`e` cast noise): unfolding `pow b.toNat e.toNat`
   yields a recursive index `(↑e.toNat - 1).toNat`, which differs syntactically
   from a hand-written `(e - 1)`. Worked around by writing each recurrence
   `have` in the matching `(e.toNat - 1)` form and converting with a
   `rw [show ((e.toNat : Int) - 1).toNat = e.toNat - 1 from by omega]`.

2. **Variable-range bounds are conjunctions.** The per-variable range facts
   arrive as `_h_ctx : 0 ≤ x ∧ x < 2^64` (a conjunction, unlike the now-split
   invariant). `nlinarith` can't reach the `0 ≤ x` conjunct, so the overflow
   checks' *lower* bound `0 ≤ result*b` / `0 ≤ b*b` (nonlinear, needs
   `0 ≤ result, 0 ≤ b`) fails. Worked around with explicit `assert(0 <= b * b)`
   etc., extracting the nonnegs via `omega` (which *does* split conjunctions)
   then `nlinarith`. Splitting these range conjunctions the way the invariant
   is now split would remove the need for those asserts.

The working closer is `first | tactus_auto | (intros; omega) | (intros;
nlinarith)` — `omega` bridges ℕ/ℤ for the linear obligations (it abstracts the
nonlinear products as atoms), `nlinarith` handles the genuinely nonlinear ones.

The original investigation follows.

---

## UPDATE — Friction 1 FIXED (confirmed)

Friction 1 (unsplit invariant conjunction) is **fixed**. The loop invariant now
arrives as individual hypotheses in assert/obligation contexts:

```
_h_ctx_3 : 1 ≤ b
_h_ctx_4 : 1 ≤ result
_h_ctx_5 : result * ↑(pow b.toNat e.toNat) = ↑(pow base.toNat exp.toNat)
_h_ctx_6 : pow base.toNat exp.toNat ≤ 2147483648
_h_ctx_7 : e > 0
```

With that, adding a `#[verifier::tactus_tactic("first | tactus_auto | (intros;
nlinarith)")]` closer cleared the `1 ≤ b` and `1 ≤ result` maintains, exactly as
this report predicted (15 → 12 errors).

The remaining 12 failures isolate to **Friction 2** and **Friction 3** below.
Of the two, **Friction 2 is now the key blocker**, with a sharper diagnosis:

> In the invariant product `(result as nat) * pow(b as nat, e as nat)`, the
> `(result as nat)` lowers to the **ℤ** exec var `result` (kept as-is, not
> `result.toNat`), and the nat-valued `pow` is coerced **up** to ℤ. So the whole
> invariant is ℤ. But spec-fn facts a proof naturally produces — `pow_ge_base`,
> `pow_square`, `pow_step` — are **ℕ** equations/inequalities. `nlinarith`/
> `linarith` won't combine a ℕ hypothesis (`pow b.toNat e.toNat ≥ b.toNat`) with
> a ℤ hypothesis (`result * ↑(pow b.toNat e.toNat) = …`) without the author
> inserting `exact_mod_cast`/`push_cast` at every step — pervasive enough to make
> the tutorial proof unacceptably noisy.
>
> If `(x as nat)` lowered to `x.toNat` (ℕ) consistently — so the whole invariant
> obligation is ℕ — the spec-fn facts would combine directly and the casts would
> vanish. That's the fix that makes this chapter's proof clean.

Friction 3 (`e.toNat` vs `e` in unfolded recursive indices) is real but
work-around-able author-side by packaging the recurrence in a `nat`-param lemma
(`pow_step`); it's lower priority than Friction 2.

The original full report follows.

---

## Summary

While writing the tutorial's Chapter 5 (exponentiation by squaring — a `u64`
`pow_iter` verified against a recursive `pow` spec), the two supporting lemmas
verify cleanly, but the exec fn cannot be discharged. The blockers are **not**
mathematical — the proof is complete in principle — they are three frictions in
how Tactus lowers loop invariants and asserts to Lean. Each makes the generated
goal unprovable by the tactics that *should* close it.

These are the same class of UX issue as the earlier reports (`as nat` casts,
exec-fn imports, loop-local alpha-renaming): the math is fine, the lowering gets
in the way. Chapter 4 (`factorial`) sidestepped all three by luck of shape —
its invariant bound was a literal (`result <= 3628800`, not a spec-fn term), its
recurrence assert happened to render uniformly, and its overflow facts didn't
need the invariant. A recurrence invariant of the form `acc * f(state) == answer`
hits all three at once.

The two lemmas that **do** verify (for context — these are the whole math
content of the chapter):

```rust
spec fn pow(base: nat, e: nat) -> nat
    decreases e
{ if e == 0 { 1 } else { base * pow(base, (e - 1) as nat) } }

proof fn pow_pos(base: nat, e: nat)
    requires base >= 1
    ensures pow(base, e) >= 1
    decreases e
by { /* self-recursive; verifies */ }

proof fn pow_square(base: nat, k: nat)      // the crux identity
    ensures pow(base * base, k) == pow(base, 2 * k)
    decreases k
by { /* self-recursive on k; verifies */ }
```

---

## Friction 1: the loop invariant arrives as one unsplit `∧` hypothesis

In assert and obligation contexts the four invariant clauses are glued into a
single conjunction hypothesis, `_h_ctx_3`:

```
_h_ctx_3 :
  1 ≤ b ∧
    1 ≤ result ∧ result * ↑(pow b.toNat e.toNat) = ↑(pow base.toNat exp.toNat) ∧ pow base.toNat exp.toNat ≤ 2147483648
```

Neither `omega` nor `nlinarith` looks inside a conjunction hypothesis, so facts
that are *right there* are unreachable:

- The **overflow check** for `result = result * b` reduces to
  `0 ≤ result*b ∧ result*b < 2^64`, with `result * b ≤ ↑(pow base.toNat exp.toNat)`
  available as an introduced hypothesis — but `pow base.toNat exp.toNat ≤ 2147483648`
  is buried inside `_h_ctx_3`, so omega can't chain `result*b ≤ pow ≤ 2^31 < 2^64`.
  Result: `tactus: auto-tactic failed — add explicit proof block`.
- The **`1 ≤ b` maintain** (after `b = b*b`) needs `1 ≤ b` from `_h_ctx_3` to get
  `1 ≤ b*b` (and even with it, that step is nonlinear — see "closer" note below).

The only ways through are fragile: project the conjunct by hand
(`_h_ctx_3.2.2.1`), relying on an internal autogenerated name, or `obtain
⟨…⟩ := _h_ctx_3` with a pattern that must track the exact clause shape. Both are
unfit for a tutorial (and brittle against any change in clause count/order).

**Desired:** the invariant clauses should be individually-named hypotheses in
assert/obligation contexts (or omega/nlinarith preprocessing should split `∧`
hypotheses), so `pow base exp ≤ 2^31`, `1 ≤ b`, etc. are reachable by name/type.

---

## Friction 2: invariant renders in ℤ, structurally-identical assert renders in ℕ

The invariant clause

```rust
(result as nat) * pow(b as nat, e as nat) == pow(base as nat, exp as nat)
```

lowers to **ℤ**:

```
result * ↑(pow b.toNat e.toNat) = ↑(pow base.toNat exp.toNat)
```

(`result` stays the ℤ exec var; the nat-valued `pow` is coerced up with `↑`).

But the structurally-identical *assert* used to feed the maintain step,

```rust
assert((result * b) as nat * pow((b * b) as nat, (e / 2) as nat) == pow(base as nat, exp as nat)) by { … }
```

lowers to **ℕ**:

```
(result * b).toNat * pow (b * b).toNat (e / 2).toNat = pow base.toNat exp.toNat
```

(here the leading `as nat` forces `.toNat` and the whole equation is in ℕ).

So the asserted fact (ℕ) does not unify with the maintain obligation (ℤ, derived
from the invariant clause), and proving the assert doesn't advance the maintain
step. The author has no reliable control over which side of the ℤ/ℕ boundary a
given `… as nat …` expression lands on — the same surface syntax renders
differently in an `invariant` clause vs. an `assert`.

**Desired:** consistent ℤ-vs-ℕ lowering for the same surface expression across
`invariant` and `assert` positions (or a documented rule for which wins), so an
asserted next-state fact unifies with the maintain obligation.

---

## Friction 3: `e.toNat` vs `e` cast noise in unfolded recursive indices

Inside the exec assert the loop var `e` is `ℤ`. Applying the spec fn as
`pow b.toNat e.toNat` and unfolding once yields a recursive index

```
pow b.toNat (↑e.toNat - 1).toNat
```

while a hand-written term naturally comes out `(↑e - 1).toNat` (using the ℤ var
`e` directly). These are equal in value (for `e ≥ 0`) but not syntactically, so
a `have hrec : pow b.toNat e.toNat = b.toNat * pow b.toNat ((↑e - 1).toNat) := by
unfold pow; rw [if_neg …]` leaves a residual goal:

```
⊢ b.toNat * pow b.toNat (↑e.toNat - 1).toNat = b.toNat * pow b.toNat (e - 1).toNat
```

i.e. the unfold produced `(↑e.toNat - 1)` but the stated RHS has `(e - 1)`. The
author must guess the exact `e.toNat`-vs-`e` form the unfolder will emit, or
insert extra cast-normalization lemmas. In proof fns (where the parameter is a
clean `nat`) this never arises — it's purely an exec-context artifact.

**Desired:** either normalize the cast so unfolded indices match the obvious
hand-written form, or expose a canonical form the author can target.

---

## Full reproducer

`chapters/05-fast-exponentiation/pow_by_squaring.rs`, with the exec fn restored.
The two lemmas verify; `pow_iter` produces 15 errors across the overflow checks,
the `1 ≤ b` / `1 ≤ result` / equality maintains, the recurrence asserts, and the
postcondition.

```rust
use verus_builtin::*;
use verus_builtin_macros::*;

verus! {

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

spec fn pow(base: nat, e: nat) -> nat
    decreases e
{ if e == 0 { 1 } else { base * pow(base, (e - 1) as nat) } }

proof fn pow_pos(base: nat, e: nat)
    requires base >= 1
    ensures pow(base, e) >= 1
    decreases e
by {
    if h : e = 0 then (
        subst h; unfold pow; simp
    ) else (
        have ih := pow_pos base (e - 1)
        have rec_app : pow base e = base * pow base ((↑e - 1 : Int).toNat) := by
            conv_lhs => unfold pow
            rw [if_neg (by omega : e ≠ 0)]
        have ee : ((↑e - 1 : Int).toNat) = e - 1 := by omega
        rw [ee] at rec_app
        have h_prod : 1 * 1 <= base * pow base (e - 1) := by
            apply Nat.mul_le_mul <;> omega
        omega
    )
}

proof fn pow_square(base: nat, k: nat)
    ensures pow(base * base, k) == pow(base, 2 * k)
    decreases k
by {
    if h : k = 0 then (
        subst h; unfold pow; simp
    ) else (
        have ih := pow_square base (k - 1)
        conv_lhs => unfold pow
        rw [if_neg (by omega : k ≠ 0)]
        rw [show ((↑k : Int) - 1).toNat = k - 1 from by omega]
        conv_rhs => unfold pow
        rw [if_neg (by omega : 2 * k ≠ 0)]
        rw [show ((↑(2 * k) : Int) - 1).toNat = 2 * k - 1 from by omega]
        conv_rhs => unfold pow
        rw [if_neg (by omega : 2 * k - 1 ≠ 0)]
        rw [show ((↑(2 * k - 1) : Int) - 1).toNat = 2 * (k - 1) from by omega]
        rw [ih]
        ring
    )
}

#[verifier::tactus_auto]
fn pow_iter(base: u64, exp: u64) -> (r: u64)
    requires
        base >= 1,
        pow(base as nat, exp as nat) <= 0x8000_0000,
    ensures r as nat == pow(base as nat, exp as nat)
{
    let mut result: u64 = 1;
    let mut b: u64 = base;
    let mut e: u64 = exp;
    while e > 0
        invariant
            1 <= b,
            1 <= result,
            (result as nat) * pow(b as nat, e as nat) == pow(base as nat, exp as nat),
            pow(base as nat, exp as nat) <= 0x8000_0000,
        decreases e
    {
        // (A) b <= pow(b,e) <= result*pow(b,e) = pow(base,exp) <= 2^31.
        assert(b as nat <= pow(base as nat, exp as nat)) by {
            intros
            have hpos := (pow_pos b.toNat ((↑e - 1 : Int).toNat)) (by omega)
            have hrec : pow b.toNat e.toNat = b.toNat * pow b.toNat ((↑e - 1 : Int).toNat) := by
                conv_lhs => unfold pow
                rw [if_neg (by omega : e.toNat ≠ 0)]
            nlinarith [hpos, hrec]
        };
        // (B) b*b fits in u64 (b <= 2^31 ==> b*b <= 2^62).
        assert((b as nat) * (b as nat) <= 0x4000_0000_0000_0000) by { intros; nlinarith };
        if e % 2 == 1 {
            assert((result * b) as nat * pow((b * b) as nat, (e / 2) as nat) == pow(base as nat, exp as nat)) by {
                intros
                have hbb : ((b * b : Int)).toNat = b.toNat * b.toNat := by
                    rw [Int.toNat_mul] <;> omega
                have hsq := pow_square b.toNat (e / 2).toNat
                have he : 2 * (e / 2).toNat = e.toNat - 1 := by omega
                rw [he] at hsq
                have hrec : pow b.toNat e.toNat = b.toNat * pow b.toNat ((↑e - 1 : Int).toNat) := by
                    conv_lhs => unfold pow
                    rw [if_neg (by omega : e.toNat ≠ 0)]
                have hee : ((↑e - 1 : Int).toNat) = e.toNat - 1 := by omega
                rw [hee] at hrec
                rw [hbb]
                nlinarith [hsq, hrec]
            };
            assert(result * b <= pow(base as nat, exp as nat)) by {
                intros
                have hbb : ((b * b : Int)).toNat = b.toNat * b.toNat := by
                    rw [Int.toNat_mul] <;> omega
                have hpos := (pow_pos (b.toNat * b.toNat) (e / 2).toNat) (by nlinarith)
                nlinarith [hpos]
            };
            result = result * b;
        } else {
            assert((result as nat) * pow((b * b) as nat, (e / 2) as nat) == pow(base as nat, exp as nat)) by {
                intros
                have hbb : ((b * b : Int)).toNat = b.toNat * b.toNat := by
                    rw [Int.toNat_mul] <;> omega
                have hsq := pow_square b.toNat (e / 2).toNat
                have he : 2 * (e / 2).toNat = e.toNat := by omega
                rw [he] at hsq
                rw [hbb, hsq]
            };
        }
        b = b * b;
        e = e / 2;
    }
    result
}

fn main() {}

} // verus!
```

## Notes

- `Int.toNat_mul` *does* work for the `(b*b).toNat = b.toNat * b.toNat` bridge —
  that hypothesis lands in context fine. The bridge isn't the problem; reaching
  the invariant facts and unifying ℤ/ℕ forms is.
- A `#[verifier::tactus_tactic("first | tactus_auto | (intros; nlinarith)")]`
  closer (as in Chapter 1's `sum_iter`) does not help here, because the auto
  obligations need the conjunction split *before* nlinarith, and nlinarith does
  not split `∧` hypotheses.
- Of the three, Friction 1 (unsplit invariant conjunction) is the highest-impact:
  fixing it alone would let the overflow checks and the `1 ≤ b`/`1 ≤ result`
  maintains close via a simple `(intros; nlinarith)` closer, leaving only the
  ℤ/ℕ unification (Friction 2) for the equality maintain.

## Discovered while

Writing tutorial Chapter 5 (`pow_by_squaring`), the planned capstone. The math
(both lemmas) verifies; the exec fn is paused pending these frictions.
```
