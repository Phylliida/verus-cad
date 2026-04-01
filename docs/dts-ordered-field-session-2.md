# DTS Ordered Field — Session 2 Progress Report

## Overview

Building a fully verified ordered field theory for `DynTowerSpec` (DTS), the type-erased recursive quadratic extension tower. This session went from **90 verified, 2 errors → 103 verified, 2 errors** — massive infrastructure buildout.

**Crate:** `verus-quadratic-extension/src/dyn_tower_lemmas.rs`
**Constraint solver:** `verus-2d-constraint-satisfaction` — 517 verified, 0 errors

## Major Accomplishments

### 1. `le_antisymmetric_fuel` — FULLY VERIFIED
The hardest theorem: `nonneg(x) ∧ nonneg(neg(x)) ∧ norm_definite(x) → is_zero(x)`.

**Key insight:** The original `dts_eqv`-based le_antisymmetric is FALSE for DTS (degenerate towers like `Ext(1, -1, 1)` are semantically zero but not component-wise zero). Solution: add `dts_norm_definite` predicate.

**Proof structure:**
- Rat case: `Rational::lemma_le_antisymmetric` + `eqv_zero_iff_num_zero`
- Ext case: 9-case analysis on C1/C2/C3 × C1'/C2'/C3'. Three main cases:
  - CASE 1 (both_nonneg(a,b)): IH on both components
  - CASE 2/3 (one both_nonneg, other definite sign): IH + norm chain → `norm ≡ neg(d*b²)` → both_nonneg(d*b²) → is_zero → norm_definite
  - CASE 4 (both definite sign): `neg_norm_congruence` helper → both_nonneg(norm) → IH → is_zero(norm) → norm_definite

### 2. `dts_norm_definite` — Universal Quantifier Version
```rust
dts_norm_definite(Ext(re, im, d)) =
    dts_norm_definite(re) && dts_norm_definite(im) && dts_norm_definite(d)
    && (forall|a2, b2| is_zero(sub(a2², d*b2²)) ==> is_zero(a2) && is_zero(b2))
```
The universal quantifier makes norm_definite auto-propagate to ALL computed values with the same radicand. This was the breakthrough that made the proofs work for arbitrary tower depths.

### 3. Propagation Lemmas — All Verified
- `lemma_norm_definite_mul(x, y)`: norm_definite propagates through multiplication
- `lemma_norm_definite_add(x, y)`: through addition
- `lemma_norm_definite_neg(x)`: through negation

### 4. Algebraic Foundations — All Verified
- `lemma_rational_nonsquare_forces_zero`: α²=δ·β² ∧ δ nonsquare → β=0
- `lemma_dts_neg_norm_congruence`: transfers nonneg(neg_norm') from C3' to nonneg(neg(norm))
- `Rational::lemma_div_div`: (x/a)/b ≡ x/(a*b)
- `Rational::lemma_div_congruence`: a ≡ b → a/c ≡ b/c

### 5. DTS Solver Pipeline — 517 verified, 0 errors
- `lazy_verify_min_displacement_dyn`: tree-aware sign variant search using DTS
- `solve_min_displacement_dyn`: top-level with greedy mask from rational solver
- Abstract plan helpers: count_circle_steps, make_sign_variant, coupling components, component graph

### 6. nonneg_mul Remaining Cases — In Progress
Extracted into `lemma_dts_nonneg_mul_remaining` helper for rlimit. Handles C1×C2, C2×C1, A×B, B×A via:
- le_total on re, im → C1/C2/C3 dispatch
- conclude_re (re≥0, norm≥0) and conclude_im (im≥0, neg_norm≥0)
- Norm sign from factor norms via le_total(nx), le_total(ny) + neg_mul_left/right

## Key Technical Lessons

### `dts_eqv` vs semantic zero
`dts_eqv(x, zero())` is component-wise. Degenerate towers (d = perfect square) can have semantic zeros that aren't component-wise zero. `Ext(1, -1, 1)` represents 1-√1=0 but has nonzero components. This means le_antisymmetric needs the `norm_definite` precondition.

### Universal quantifier in norm_definite
The per-value version `is_zero(sub(re², d*im²)) → is_zero(re) ∧ is_zero(im)` doesn't propagate to computed values (products, sums). The universal version `forall|a2, b2| ...` propagates automatically since ANY Ext with the same radicand d satisfies the condition.

### same_radicand boilerplate is the #1 time sink
Every IH call needs ~5-10 lines of same_radicand chains (symmetric, transitive). Every new helper (norm_definite_mul, norm_definite_add) needs its own chains. Extract helpers aggressively.

### rlimit management
- `assert by { ... }` blocks scope Z3 context — essential for large functions
- Extract case handlers into separate functions (bb, cc, bb_norm, remaining)
- `#[verifier::rlimit(120)]` or `#[verifier::rlimit(200)]` for complex functions

### neg(neg(x)) structural equality
`dts_neg(dts_neg(x)) == x` is structurally true for DTS (Rat and Ext). Z3 can derive this but sometimes needs `assert(dts_neg(neg_b2) == b2)` as a hint.

### Conclude_re vs Conclude_im dispatch
- `conclude_re(re, im, d, f)`: re≥0 AND norm≥0 → nonneg
- `conclude_im(re, im, d, f)`: im≥0 AND !is_zero(im) AND neg_norm≥0 → nonneg
- Norm sign = nx*ny. Determine from factor classifications via le_total + neg_mul chains.

## What Remains (2 errors)

### Immediate: Fix `lemma_dts_nonneg_mul_remaining` postcondition

The helper has the right structure but 2-3 return points fail:

1. **is_zero(im_val) return**: Z3 can't derive that nonneg(re_val) follows from is_zero(im_val) + the factor nonneg conditions. Need: explicit nonneg(re_val) proof (le_total + one of conclude_re/conclude_im).

2. **is_zero(re_val) return**: Similar — need nonneg(im_val) proof.

3. **Else fallthrough (neg(re)≥0, neg(im)≥0)**: This case is unreachable (product of nonneg values can't have both components negative in a norm-definite tower). Z3 can't see this automatically. Need: show that neg(re)≥0 ∧ neg(im)≥0 ∧ both factors nonneg leads to a contradiction via norm analysis.

4. **Cauchy-Schwarz sub-case (nx≥0, ny≥0, neg(re)≥0)**: In the conclude_im branch, the else case where both norms are nonneg and re is neg-nonneg. This is unreachable because nx≥0 ∧ ny≥0 forces re≥0 via Cauchy-Schwarz inequality `(a1*a2)² ≥ (dd*b1*|b2|)²`. Need: le_mul_nonneg_monotone chain to show P*S ≥ 0, then le_antisymmetric on P*S to show is_zero(re_val).

### After nonneg_mul (cascading):
- `nonneg_add_closed_fuel` postcondition will automatically resolve once nonneg_mul is complete (the nonneg_add cases use nonneg_mul as IH).

### Approach for the remaining sub-cases:
Each unreachable sub-case can be closed by:
1. Deriving both_nonneg of some intermediate value (re, im, or norm)
2. Calling le_antisymmetric to get is_zero
3. Using is_zero shortcuts already in the code

The Cauchy-Schwarz sub-case specifically needs:
```
P*S = (a1*a2)² - (dd*b1*|b2|)²
le_mul_nonneg_monotone(dd*b1², a1², a2²) → a1²*a2² ≥ dd*b1²*a2²
le_mul_nonneg_monotone(dd*|b2|², a2², dd*b1²) → dd*b1²*a2² ≥ (dd*b1*|b2|)²
→ P*S ≥ 0
neg(P)*S ≥ 0 (nonneg_mul) → neg(P*S) ≥ 0
both_nonneg(P*S) → le_antisymmetric → is_zero(P*S) → is_zero(re)
```
~30 lines of le_mul_nonneg_monotone + square_mul + congruence.

## Architecture

### Proof Function Structure
```
nonneg_mul_closed_fuel(x, y, fuel)     decreases fuel, 0nat
├── C1×C1 case (inline)
├── B×B → lemma_dts_nonneg_mul_bb     decreases f, 2nat
│   └── bb_norm helper                 decreases f, 1nat
├── C2×C2 → lemma_dts_nonneg_mul_cc   decreases f, 2nat
└── Remaining → nonneg_mul_remaining   decreases f, 2nat
    ├── C1 dispatch (re≥0, im≥0)
    ├── is_zero shortcuts
    ├── conclude_re (re≥0, norm via nx*ny)
    ├── conclude_im (im≥0, neg_norm via neg(nx*ny))
    └── Cauchy-Schwarz (unreachable sub-case) ← TODO

nonneg_add_closed_fuel(x, y, fuel)     decreases fuel, 0nat
├── C1+C1 (inline)
├── C1+C2/C2+C1 + c1c2_norm_bound     decreases f, 1nat
└── TODO: remaining add cases

le_antisymmetric_fuel(x, fuel)         decreases fuel, 1nat  ← FULLY VERIFIED
square_nonneg(x, fuel)                                        ← FULLY VERIFIED
norm_definite_mul/add/neg                                      ← FULLY VERIFIED
neg_norm_congruence                                            ← FULLY VERIFIED
rational_nonsquare_forces_zero                                 ← FULLY VERIFIED
```

### Predicate Dependencies
```
dts_norm_definite(x) ← universal quantifier, auto-propagates
    ├── requires dts_well_formed(x), dts_nonneg_radicands(x)
    ├── used by: le_antisymmetric, nonneg_mul/add (via norm_definite precondition)
    └── propagated by: norm_definite_mul/add/neg

dts_nonsquare_radicands(x) ← each Rat radicand is not a perfect square
    ├── used by: rational_nonsquare_forces_zero
    └── implies norm_definite for depth-1 towers (Rat components)

dts_nonneg_radicands(x) ← each radicand is nonneg
    ├── used by: nonneg_fuel_stabilize, square_le_square, etc.
    └── propagated by: nonneg_radicands_mul/add/neg
```
