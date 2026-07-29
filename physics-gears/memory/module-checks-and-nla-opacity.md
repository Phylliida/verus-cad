# Module-level checks trust dependency lemmas (2026-07-28)

Two related lessons from the phys-05c row-lemma session:

## 1. `verus_check(crate, module)` does NOT re-verify dependency proofs

A module-scoped check verifies only that module's functions; lemmas in
*other* modules of the same crate (e.g. `proofs/rational_raw.rs`) are
treated as trusted axioms. `lemma_raw_neg_sub` shipped broken through two
green module checks (`row`, `proofs::row`) and only failed in the
full-crate run. **Rule: the full-crate check is the only green that
counts for a commit.** Module checks are for iteration speed only.

## 2. `by(nonlinear_arith)` treats spec-fn applications as opaque

`assert(x.sub_spec(y).neg_spec().den == y.sub_spec(x).den) by
(nonlinear_arith);` FAILS even though the identity is just nat-mul
commutativity after unfolding — the NLA query does not unfold
`sub_spec`/`neg_spec` (R3 corollary: NLA ignores local definitions too).
Fix pattern: plain-assert the one-level unfolds first (Z3 handles those),
then run `by(nonlinear_arith)` only on fully-unfolded int/nat terms:

```rust
assert(lhs.den == x.den * y.den + x.den + y.den);          // plain
assert(rhs.den == y.den * x.den + y.den + x.den);          // plain
assert(x.den * y.den == y.den * x.den) by (nonlinear_arith);  // universal identity
assert(lhs.den == rhs.den);                                 // plain
```

Same for num identities hiding `(-a)*b == -(a*b)`: assert that micro-identity
on plain int terms with `by(nonlinear_arith)`, then close with plain asserts.

## 3. eqv-chain call order matters

`lemma_eqv_add_congruence` (and friends) can only use eqv facts established
by *earlier* calls in the same proof body — a congruence call placed before
the transitive chain that proves its premise fails with "precondition not
satisfied". Order: micro-rewrites → per-term chains → congruence → final
transitive. And every 3-node chain needs its own `lemma_eqv_transitive(a,
b, c)` call — skipping the middle link (having a≡b and b≡c from other
conclusions but never calling transitive) is the most common failure mode.
