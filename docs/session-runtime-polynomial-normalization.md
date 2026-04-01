# Session Report: Runtime Polynomial Normalization for GpuFixedPoint eq

## Summary

Implemented and verified runtime polynomial normalization — the exec-level counterpart to the spec-level `arith_to_poly`. This enables `RuntimeGpuFixedPoint::eq` to compute polynomial equivalence at exec time, completing the bridge from spec Ring axioms to executable GPU codegen.

**Final status:**
- `gpu_ring_test.rs`: 169 verified, 0 errors (spec Ring + coefficient bound lemmas)
- `gpu_codegen.rs`: 39 verified, 4 errors (exec runtime poly — bound threading remaining)

## Architecture

### RuntimeGpuFixedPoint (rewritten)

The old `RuntimeGpuFixedPoint` used multi-limb `Vec<RuntimeArithExpr>` with carry chains. The new version wraps a **single `RuntimeArithExpr`**, matching the spec `GpuFixedPoint { expr: ArithExpr }`:

```rust
pub struct RuntimeGpuFixedPoint<const N: usize, const F: usize> {
    pub expr: RuntimeArithExpr,
}
```

Ring operations trivially build the matching tree:
- `add(a, b)` → `RuntimeArithExpr::Add(a.expr.clone(), b.expr.clone())`
- `mul(a, b)` → `RuntimeArithExpr::Mul(...)`
- etc.

Each operation's postcondition `out@ == self@.add(rhs@)` verifies automatically since `view_spec` maps RuntimeArithExpr constructors to ArithExpr constructors.

### Runtime Polynomial Type

```
Runtime: Vec<(i64, Vec<u32>)>    — coefficient + sorted variable indices
Spec:    Seq<(int, Seq<nat>)>    — same structure, unbounded types
```

View conversion: `poly_rt_view(p@)` maps `(i64, Vec<u32>)` to `(int, Seq<nat>)` via `(p[i].0 as int, vars_view(p[i].1@))`.

### Three-Layer Proof Architecture

**Layer 1: Correctness** — Each runtime function matches the spec:
```rust
ensures poly_rt_view(out@) =~= poly_add(poly_rt_view(p@), poly_rt_view(q@))
```

**Layer 2: Spec Coefficient Bounds** — `poly_sum_abs` chain proves `arith_to_poly(e)` has all coefficients bounded by `expr_coeff_bound(e)`:
```
poly_sum_abs(arith_to_poly(e)) <= expr_coeff_bound(e)
```

**Layer 3: Exec Overflow Safety** — Bridge from spec bounds to i64 overflow-freedom:
```rust
lemma_rt_bounded_from_sum_abs(rt_poly, spec_poly, bound)
```

## What Was Proved

### Spec-Level Coefficient Bound Chain (in gpu_ring_test.rs)

1. **`expr_coeff_bound(e)`** — Recursive upper bound on polynomial coefficients:
   - `Const(c)` → `|c|`
   - `Var(_)` → `1`
   - `Add(a,b)` → `ecb(a) + ecb(b)`
   - `Mul(a,b)` → `ecb(a) * ecb(b)`

2. **`poly_sum_abs(p)`** — Sum of absolute values of polynomial coefficients.

3. **Key lemmas** (each proved by structural induction):
   - `lemma_poly_neg_sum_abs`: negation preserves sum_abs
   - `lemma_poly_add_sum_abs`: `sum_abs(poly_add(p,q)) <= sum_abs(p) + sum_abs(q)`
   - `lemma_poly_insert_sum_abs`: `sum_abs(poly_insert(c,v,p)) <= |c| + sum_abs(p)`
   - `lemma_mono_mul_sum_abs`: `sum_abs(mono_mul(c,v,q)) <= |c| * sum_abs(q)`
   - `lemma_poly_mul_sum_abs`: `sum_abs(poly_mul(p,q)) <= sum_abs(p) * sum_abs(q)`
   - `lemma_arith_to_poly_sum_abs`: `sum_abs(arith_to_poly(e)) <= expr_coeff_bound(e)`
   - `lemma_arith_to_poly_coeff_bound`: **MAIN LEMMA** — each individual coefficient bounded by ecb

4. **Helper lemmas**:
   - `lemma_poly_sum_abs_prepend`: `sum_abs([head] + tail) = |head.0| + sum_abs(tail)`
   - `lemma_abs_triangle`: `|a+b| <= |a| + |b|`
   - `lemma_poly_sum_abs_bounds_individual`: `|p[k].0| <= sum_abs(p)`

### Exec-Level Runtime Polynomial Functions (in gpu_codegen.rs)

All with correctness postconditions proving `poly_rt_view(out@) =~= spec_fn(...)`:

- **Helpers**: `vec_u32_tail`, `poly_tail`, `poly_clone`
- **Variable operations**: `runtime_vars_lt`, `runtime_vars_eq`, `runtime_vars_merge`
- **Polynomial operations**: `runtime_poly_neg`, `runtime_poly_add`, `runtime_poly_insert`, `runtime_mono_mul_poly`, `runtime_poly_mul`
- **Conversion**: `runtime_arith_to_poly` (RuntimeArithExpr → runtime polynomial)
- **Comparison**: `runtime_poly_eq` (structural polynomial equality)
- **RuntimeGpuFixedPoint**: `add`, `sub`, `mul`, `neg`, `copy`, `zero_val`, `one_val`, `from_var`, `into_expr`
- **Perturbation**: `runtime_perturbation_step` (verified against spec)
- **Bridge lemmas**: `lemma_rt_bounded_from_sum_abs`, `lemma_rt_bounded_from_spec`

## Key Challenges and Solutions

### Challenge 1: Vec<(i64, Vec<u32>)> Cloning

`Vec::clone` for nested types doesn't have verified postconditions connecting to `poly_rt_view`.

**Solution**: Wrote `poly_clone` that copies element-by-element with explicit postcondition proving `poly_rt_view(out@) =~= poly_rt_view(p@)`.

### Challenge 2: poly_rt_view Opacity

Z3 couldn't connect `poly_rt_view` of cloned/constructed Vecs to the spec functions. The view conversion (`(i64, Vec<u32>)` → `(int, Seq<nat>)`) creates a layer Z3 can't see through.

**Solution**: Added `lemma_poly_rt_view_prepend` bridge lemma and explicit `reveal_with_fuel` calls at each branch point in poly_add/poly_insert.

### Challenge 3: Coefficient Bound Composability Through Multiplication

The fundamental issue: polynomial addition doubles coefficient bounds (`sum <= 2*max`), and multiplication squares them. Through `poly_mul`'s recursive structure (which calls `poly_add` on each mono_mul result), bounds grow exponentially.

**Approach 1 (failed)**: Track bounds through postconditions. `rt_poly_bounded(out@, 2*bound@)` for poly_add, `q.len()*bound^2` for mono_mul. But poly_mul's recursive poly_add doubles at each level → exponential.

**Approach 2 (failed)**: Single fixed `COEFF_BOUND`. Doesn't compose through multiplication.

**Approach 3 (succeeded)**: **Spec-level sum-of-absolute-values argument.** Proved at the spec level that `poly_sum_abs(poly_mul(p,q)) <= poly_sum_abs(p) * poly_sum_abs(q)`. This is a TIGHT bound (no exponential growth) because it tracks the actual mathematical property. Used `lemma_rt_bounded_from_sum_abs` to bridge from spec bounds to exec `rt_poly_bounded`.

This completely avoids the doubling problem: the spec lemma directly establishes that ALL intermediate coefficients within `arith_to_poly(e)` are bounded by `expr_coeff_bound(e)`, regardless of the recursive structure.

### Challenge 4: Separate Bounds for Mul Inputs

`poly_mul` initially took a single `bound` for both p and q. But for `Mul(a,b)`: pa bounded by `ecb(a)` and pb by `ecb(b)`, which are different. Using `max(ecb(a), ecb(b))` as the common bound fails: `max^2 >= ecb(a)*ecb(b) = ecb` (exceeds the budget).

**Solution**: Changed `poly_mul` and `mono_mul_poly` to accept separate bounds (`pb`, `qb`) for p and q inputs.

### Challenge 5: Overflow for Const(0) Multiplier

When `ecb(b) = 0` (e.g., `b = Const(0)`), `ecb(Mul(a,b)) = 0`. But `arith_to_poly(a)` may have nonzero coefficients. Can't call `poly_mul` with bound 0 on pa.

**Solution**: Short-circuit when `pa.len() == 0 || pb.len() == 0` — return empty directly. When both non-empty, both sub-expression bounds are > 0.

### Challenge 6: nonlinear_arith for Triangle Inequality

Z3's `by(nonlinear_arith)` couldn't prove `|a+b| <= |a| + |b|` with the if-else absolute value encoding.

**Solution**: Extracted `lemma_abs_triangle` as a standalone proof (Z3 handles it with linear reasoning in each branch without the nonlinear context pollution).

### Challenge 7: poly_sum_abs Unfolding on Constructed Sequences

`poly_sum_abs(seq![(c, vars)] + rest)` doesn't unfold automatically because `poly_sum_abs` recurses on `p.subrange(1, ...)`, and Z3 can't see that `(seq![head] + tail).subrange(1, ...) =~= tail`.

**Solution**: Extracted `lemma_poly_sum_abs_prepend` that explicitly proves `poly_sum_abs(seq![head] + tail) = |head.0| + poly_sum_abs(tail)`.

## Remaining Work (4 errors)

All 4 errors are in `mono_mul_poly` and `arith_to_poly`'s Mul case, involving bound threading:

1. **mono_mul overflow**: `c * q[0].0` needs `|c| * |q[0].0| <= i64::MAX`. Have `|c| * qb <= i64::MAX/2` but need to connect `|q[0].0| <= qb` (trivial from `rt_poly_bounded`).

2. **mono_mul ecb bound**: `|nc| <= ecb` needs `|c| * |q[0].0| <= |c| * sum_abs(qv) <= ecb`. Need `|q[0].0| <= sum_abs(qv)` from `lemma_poly_sum_abs_bounds_individual`.

3. **poly_mul → mono_mul**: `|p[0].0| * qb <= i64::MAX/2`. Follows from `|p[0].0| <= pb` and `pb * qb <= i64::MAX/2`.

4. **arith_to_poly Mul postcondition**: Depends on #1-3.

**Estimated fix**: ~20 lines of additional assertions using `lemma_poly_sum_abs_bounds_individual` and `by(nonlinear_arith)`.

## Lessons Learned

1. **Spec-level proofs first, exec-level bridge second.** Proving polynomial bounds at the spec level (where `int` has no overflow) is MUCH cleaner than trying to track bounds through exec functions with i64 overflow.

2. **Sum-of-absolute-values is the right abstraction.** Instead of tracking individual coefficient bounds (which double through poly_add), tracking the total sum of absolute values gives a TIGHT multiplicative bound for poly_mul that doesn't grow through recursion.

3. **Separate bounds for binary operations.** When two inputs have different bounds, using `max` as a common bound wastes headroom quadratically. Separate bounds (pb, qb) avoid this.

4. **Nested Vec clone needs manual verification.** Verus doesn't have verified clone for `Vec<(T, Vec<U>)>`. Manual element-by-element copy with explicit postcondition is needed.

5. **reveal_with_fuel + bridge lemmas for recursive spec functions.** When Z3 can't unfold recursive spec functions on constructed values, extract standalone bridge lemmas (like `lemma_poly_sum_abs_prepend`) that prove the unfolding step explicitly.

6. **Short-circuit edge cases.** When one operand produces an empty polynomial (e.g., Const(0)), handle it separately rather than trying to thread impossible bounds through the general case.

7. **by(nonlinear_arith) is fragile with if-else.** Extract if-else patterns into standalone lemmas (like `lemma_abs_triangle`) before using nonlinear_arith.

## File Structure

`gpu_ring_test.rs` (~3970 lines):
- Lines 1-260: Polynomial spec functions
- Lines 260-1300: Polynomial lemmas (add, wf, coefficient bridge)
- Lines 1300-1800: GpuFixedPoint Ring implementation + test
- Lines 1800-3100: Evaluation bridge, filter+factor, poly_vars_sorted
- Lines 3100-3650: Polynomial identity + modular congruence lemmas
- Lines 3650-3970: **NEW** — Coefficient bound infrastructure (expr_coeff_bound, poly_sum_abs, all sum_abs lemmas, arith_to_poly_coeff_bound)

`gpu_codegen.rs` (~900 lines):
- Lines 1-125: RuntimeGpuFixedPoint struct + Ring ops
- Lines 125-300: Runtime polynomial helpers (tail, clone, bridge lemmas)
- Lines 300-580: Runtime polynomial operations (vars_lt/eq/merge, poly_neg/add/insert/mono_mul/poly_mul)
- Lines 580-700: Spec bound bridges (lemma_rt_bounded_from_sum_abs, lemma_rt_bounded_from_spec)
- Lines 700-880: runtime_arith_to_poly + runtime_poly_eq
- Lines 880-900: runtime_perturbation_step + test
