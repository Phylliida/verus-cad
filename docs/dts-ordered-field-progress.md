# DTS Ordered Field Infrastructure — Progress Report

## Overview

Building a formally verified ordered field theory for `DynTowerSpec` (DTS), the type-erased recursive quadratic extension tower used by the CAD constraint solver. This enables `square_nonneg` → `sum_squares_zero` → non-degeneracy transfer → exec completeness.

**Crate:** `verus-quadratic-extension/src/dyn_tower_lemmas.rs`
**Current state:** 86 verified, 4 errors (B×B norm helper preconditions + 2 expected TODOs)
**File size:** ~7500 lines

## Session Summary (March 2026)

### Major Accomplishments

1. **`mul_associative` fully verified** — the fundamental algebraic property. All 8 depth cases:
   - RRR/RRE/RER/ERR: simple IH calls (2-4 lines each)
   - REE/ERE/EER: vacuously true (`same_radicand(Rat, Ext) = false`)
   - EEE: ~400 lines, extracted into helper with `assert by` blocks for rlimit. Parent calls 8 IH assoc + d-involved assoc, passes results as preconditions to helper.

2. **`square_mul` verified** — `(ab)² ≡ a²·b²` using mul_associative + mul_commutative

3. **`four_commute` verified** — `(ac)(be) ≡ (ae)(bc)` swapping inner terms in product of products

4. **`norm_mul` fully verified** — `norm(xy) ≡ norm(x)·norm(y)`, the last major algebraic identity. Split into 6 sub-helpers:
   - `norm_mul_cross`: cross-term identity `ac·(d·be) ≡ d·(ae·bc)`
   - `norm_mul_re_sq`: re² expansion
   - `norm_mul_dim_sq`: d·im² expansion
   - `norm_mul_pr_sub`: first factor `(ac)² - d·(ae)² ≡ a²·ny`
   - `norm_mul_qs_sub`: second factor `(dbe)² - d·(bc)² ≡ -(db²·ny)`
   - Main `norm_mul`: combines via sub_pairs + cross-term cancellation + sub_mul_right

5. **`mul_distributes_over_sub` and `sub_mul_right` verified** — distributes over subtraction

6. **`sub_pairs` bound relaxed** in verus-algebra: `Ring` → `AdditiveGroup` (DTS can use it directly)

7. **`c1c2_norm_bound` fully verified** — fixed all 3 ghost variable precondition errors

8. **B×B nonneg_mul case ~95% complete** — re ≥ 0 via neg_mul_neg, is_zero shortcut, norm helper extracted. Just needs ~4 same_radicand precondition fixes.

### Key Technical Lessons

#### `mul_congruence_right(a, b, c)` argument order
The eqv pair `(a, b)` goes FIRST, context `c` goes LAST. `eqv(a,b) → eqv(mul(c,a), mul(c,b))`. Got this wrong multiple times causing phantom precondition failures.

#### REE/ERE/EER cases are vacuously true
`same_radicand(Rat, Ext) = false` by definition. So any function requiring `same_radicand(a, b)` where a=Rat, b=Ext has contradictory preconditions. These match arms just need `assert(!same_radicand(a, b))`.

#### Mutual recursion decreases priorities
For a chain `nonneg_mul_closed(fuel, 0) → bb(f, 2) → bb_norm(f, 1) → nonneg_mul_closed(f, 0)`:
- Each call must have strictly SMALLER decreases tuple
- `f = fuel - 1 < fuel` handles the first element
- Priorities 2 > 1 > 0 handle same-fuel calls between helpers

#### `assert by` blocks for rlimit management
Facts inside `by { ... }` are scoped — they DON'T pollute the outer function. Use to split large proofs into independent Z3 queries. BUT: if you need a result outside the block, the `assert(...)` target must capture it.

#### `nonneg_fuel_zero` requires `eqv(x, zero())` not `is_zero(x)`
Need `lemma_dts_is_zero_implies_eqv_zero(x)` first to bridge structural zero to semantic zero.

#### same_radicand boilerplate is the #1 time sink
Every `mul_closed`, `add_closed`, `nonneg_radicands_mul`, `nonneg_mul_closed_fuel` call needs its same_radicand precondition established first via `symmetric` + `transitive` chains. The pattern `a~X` via `a~b~X` requires: `symmetric(a, b)` then `transitive(b, a, X)` — but `mul_closed(a, b)` gives `a~mul(a,b)`, so need `symmetric(a, mul(a,b))` → `mul(a,b)~a` → `transitive(mul(a,b), a, ...)`. Order matters critically.

## Architecture

### The DTS Type
```
DynTowerSpec = Rat(Rational) | Ext(Box<DTS>, Box<DTS>, Box<DTS>)
                                     re       im       d (radicand)
```

### Nonneg Definition
`dts_nonneg_fuel(Ext(a, b, d), f+1)` is a 3-case disjunction:
- **C1:** `nonneg(a) && nonneg(b)` — both re,im nonneg
- **C2:** `nonneg(a) && neg(b) nonneg && !is_zero(b) && nonneg(a²-d*b²)` — re-dominant
- **C3:** `neg(a) nonneg && !is_zero(a) && nonneg(b) && !is_zero(b) && nonneg(d*b²-a²)` — im-dominant

## Completed Lemmas (All Fully Verified — 86 functions)

### Algebraic Toolkit (NEW this session)
- **`mul_associative`**: `mul(a, mul(b,c)) ≡ mul(mul(a,b), c)` — all 8 depth cases
- **`square_mul`**: `(ab)² ≡ a²·b²`
- **`four_commute`**: `(ac)(be) ≡ (ae)(bc)`
- **`mul_distributes_over_sub`**: `a·(b-c) ≡ a·b - a·c`
- **`sub_mul_right`**: `(a-b)·c ≡ a·c - b·c`
- **`norm_mul`**: `norm(xy) ≡ norm(x)·norm(y)` — 6 sub-helpers + main function

### Ring Algebra (previous sessions)
- **`mul_commutative`**, **`mul_distributes_left`** (all 8 depth cases)
- **`neg_mul_right`**, **`neg_mul_left`**, **`neg_add`**, **`add_exchange`**
- **`difference_of_squares`**: `sub(b²,a²) ≡ mul(sub(b,a), add(b,a))`
- **`neg_square`**, **`neg_mul_neg`**, **`neg_sub_swap`**, **`sub_congruence_both`**

### Ordering
- **`le_total`**: `nonneg(x) || nonneg(neg(x))`
- **`nonneg_conclude_re/im_fuel`**: dispatch helpers
- **`square_le_square_fuel`**, **`le_mul_nonneg_monotone_fuel`**

### Nonneg Closure (Mutually Recursive)
- **`nonneg_add_closed_fuel`**: C1+C1 ✓, C1+C2/C2+C1 ✓
- **`nonneg_mul_closed_fuel`**: C1×C1 ✓, B×B ~95% (norm helper needs precondition fixes)
- **`c1c2_norm_bound`**: fully verified (~450 lines, T1+T2+T3 chain)
- **`nonneg_mul_bb`**: re ≥ 0 via neg_mul_neg + is_zero shortcut
- **`nonneg_mul_bb_norm`**: norm ≥ 0 via norm_mul + neg_mul_neg (4 precondition fixes remaining)

### Closure / Preservation
- `add_closed`, `mul_closed`, `neg_well_formed`, `same_radicand_neg`
- `nonneg_radicands_add/neg/mul`, `nonneg_fuel_congruence/stabilize/monotone`

### verus-algebra changes
- `sub_pairs` bound relaxed: `Ring` → `AdditiveGroup` (DTS can use directly)

## What Remains

### Immediate: Fix B×B norm helper (~4 same_radicand fixes)
The `lemma_dts_nonneg_mul_bb_norm` has the right proof structure but 4 precondition errors:
1. `nonneg_mul_closed_fuel(neg_nx, neg_ny, f)` — needs depth bounds for neg_nx/neg_ny
2. `neg_mul_neg(nx, ny)` — needs well_formed(nx), well_formed(ny), same_radicand(nx, ny)
3-4. Related same_radicand chain gaps

All are mechanical fixes — the proof logic is correct.

### Short Term: Remaining nonneg_mul cases
After B×B, the A×A/A×B/B×A cases follow the same pattern:
- **A×A non-C1** (a1_nn, a2_nn, some b not nn): 4 sub-cases based on norm signs. Uses `dominant_product` + `cross_dominance` helpers. `conclude_re` or `conclude_im` based on norm sign.
- **A×B / B×A** (one re≥0, other re<0): Uses cross_dominance + conclude_im, or dominant_product_dual + conclude_re.

Each case is ~80-100 lines using the established toolkit (norm_mul, neg_mul_neg, conclude_re/im).

### After nonneg_mul complete: `square_nonneg` (SHORT!)
```
proof fn square_nonneg(x, fuel)
    ensures nonneg_fuel(mul(x, x), fuel)
{
    le_total(x, fuel);
    if nonneg(x) { nonneg_mul_closed(x, x, fuel); }
    else {
        // neg(x) nonneg → neg(x)*neg(x) nonneg → x*x nonneg by neg_mul_neg
        nonneg_mul_closed(neg(x), neg(x), fuel);
        neg_mul_neg(x, x);
        nonneg_fuel_congruence(mul(neg(x), neg(x)), mul(x, x), fuel);
    }
}
```

### After square_nonneg
1. **`sum_squares_zero`**: `a²+b²=0 → a=0 ∧ b=0` via square_nonneg + le_antisymmetric
2. **Non-degeneracy transfer**: spec nondeg → dyn nondeg for exec completeness
3. **Exec completeness theorem**: well_constrained + nondegenerate → dyn solver covers all entities

### `!is_zero` blocker for remaining nonneg_add cases
C1+C3, C2+C2, C2+C3, C3+C3 nonneg_add cases need `!is_zero(sum_component)` for C2/C3 dispatch. Options:
1. Prove `le_antisymmetric` in the mutual recursion (needs square_nonneg — circular?)
2. Prove `nonneg_add_positive` separately
3. Handle via is_zero case split: if is_zero → C1, else → C2/C3

The nonneg_mul cases DON'T have this blocker (they can case-split on is_zero for C1 vs conclude_re).

## Dependency Chain

```
mul_associative ✓
  → square_mul ✓ + four_commute ✓
    → norm_mul ✓
      → nonneg_mul B×B (95%) → A×A → A×B → B×A
        → nonneg_mul COMPLETE
          → square_nonneg (short!)
            → sum_squares_zero
              → non-degeneracy transfer
                → exec completeness
```
