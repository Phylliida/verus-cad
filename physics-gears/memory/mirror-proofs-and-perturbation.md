# Mirror proofs, module perturbation, chain failure modes (2026-07-28)

Lessons from the signed-enclosure mirror (a0ae4c9, 7c73aed) and the
massprops eqv chains (26fc8c7).

## Structural mirrors beat eqv mirrors

The Rational raw ops are sign-blind in `den`: `neg_spec` flips only `num`
(`Rational { num: -self.num, den: self.den }`), and the `den` formulas of
`add_spec`/`mul_spec` depend only on the dens. Consequences, all
STRUCTURAL (`==`, not `≡`):

- `neg(a).add(neg(b)) == neg(a.add(b))` (library: `lemma_neg_add`)
- `neg(a).mul(b) == neg(a.mul(b))`, `a.mul(neg(b)) == neg(a.mul(b))`,
  `neg(a).mul(neg(b)) == a.mul(b)` (crate: `lemma_raw_neg_mul_*`)
- therefore any POLYNOMIAL spec fn built from add/sub/mul of odd powers
  mirrors for free: `arctan_term(-t) == -arctan_term(t)`,
  `arctan_sum(-t) == -arctan_sum(t)`, `tan_half_series_model(-h) ==
  -tan_half_series_model(h)` — the whole signed-enclosure debt fell out
  of `lemma_ipow_neg_odd` + induction + these rewrites, with NO eqv
  congruence chaining. When designing spec fns, prefer forms whose
  mirror/translation laws hold structurally; downstream proofs get much
  cheaper.

The only genuinely int-level step was `lemma_ipow_neg_odd`
((-x)^p == -(x^p) for odd p): induct by 2 via `lemma_ipow_add`, and
handle the `%` reasoning with
`vstd::arithmetic::div_mod::lemma_fundamental_div_mod(p as int, 2)`
(ensures only the equation; the `0 ≤ x%2 < 2` bound is native to Z3).
`lemma_small_mod` takes **nat** args — cast.

## Module perturbation is real

Adding new lemmas to `proofs/angle_ledger.rs` (and new spec fns to
`angle_ledger.rs`) broke the previously-green
`lemma_arctan_two_step_even` — same source text, new failure at a
`lemma_le_transitive` precondition. Verification is deterministic, so the
cause is the changed module SST shifting Z3's heuristics for that query
(spinoff isolation does not protect against this: each query embeds the
pruned krate). Fix, durable: make the fragile step explicit —
`lemma_le_add_monotone` yields `t2+a1 ≤ t1+a1` and the caller needed
`a1+t2 ≤ a1+t1`; bridging add-commutativity inside `le_spec`'s
cross-multiplied form was previously left to Z3. Restated with two
`lemma_add_commutative` + `lemma_eqv_implies_le` + two transitivity
steps. **If a previously-green lemma fails after you touch its module,
don't assume your new code is wrong — harden the old lemma's implicit
solver steps.**

## eqv-chain failure modes seen today (all in massprops)

Each of these was a "precondition not satisfied" at a congruence or
transitivity call:

- **Antisym in the wrong direction**: `lemma_vcross2_antisym(a, b)`
  yields `cross(a,b) ≡ -cross(b,a)`; if the chain needs
  `cross(c,a) ≡ -cross(a,c)` you must call it with `(c, a)`, not `(a, c)`.
  (Same shape as the `same_radicand_symmetric` pitfall in AGENTS.md.)
- **Missing right-congruence before assoc**: from `f + oj ≡ f + x` you
  cannot jump to `(f+oj) + v ≡ f + (x + v)` with one associativity call —
  you need `lemma_eqv_add_congruence(f+oj, f+x, v, v)` first, then
  `lemma_add_associative`.
- **`lemma_neg_sub` needed once per negated subterm**: structural
  `neg(c-d) == d-c`, but Z3 only uses it if the lemma was called on that
  exact pair.
- Every transitivity needs BOTH links established by name in the body;
  write the chain out term by term before calling `lemma_eqv_transitive`.

## Exec preconditions are forward-only

Facts for a call's `requires` must be asserted BEFORE the call in program
order — a `proof {}` block after `one.div(&d)` cannot discharge
`!d@.eqv_spec(0)`. Put the divisor-nonzero proof before the `div`.

## Misc type facts

- `Seq::len()` is `nat`; `%` wants `int` — `let n = vs.len() as int;`.
- `q_pos`/`q_nonneg` (types.rs) unfold to raw `lt_spec`/`le_spec` through
  the trait impls (`le = le_spec`, `lt = lt_spec`, `zero() =
  from_int_spec(0)`) — two or three open unfolds, no bridge lemma needed.
- `RuntimeRational` has `div` (requires `!rhs@.eqv_spec(0)`) but NO
  `reciprocal()` — use `from_int(1).div(&d)`.
- `lemma_m1_verts`-style empty-body proof fns with closed `==` ensures
  verify fine — Z3 does evaluate seq literals and single unfolds eagerly.
