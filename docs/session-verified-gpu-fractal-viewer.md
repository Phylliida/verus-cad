# Session Report: Verified GPU Fractal Viewer

## Summary

This session built the foundations for a fully verified deep-zoom Mandelbrot fractal viewer using Verus-verified GPU kernels. Starting from field axioms and ending at a complete perturbation kernel architecture, the work spans 4 crates and ~300+ newly verified functions across number theory, GPU arithmetic, algebraic normalization, and shader code generation infrastructure.

The key architectural insight: separate **algebra** (Ring operations on simple ArithExpr trees) from **implementation** (carry chains, Karatsuba), connected by a verified **lowering** step. This lets us reuse the generic `perturbation_step<T: Ring>` formula with a GPU type that automatically generates shader code, while keeping Ring axioms provable via algebraic normalization.

## What We Built

### 1. ModularInt Field Axioms (verus-fixed-point)

**Files**: `src/fixed_point/number_theory.rs` (new), `src/fixed_point/modular.rs` (extended)

Built complete field axioms for Z/pZ via Bezout's identity — NOT Fermat's little theorem (much simpler path):
- GCD (Euclidean algorithm) + Extended Euclidean (Bezout coefficients)
- `lemma_bezout`: gcd(a,b) = s*a + t*b
- `lemma_prime_coprime`: prime p, 0 < a < p → gcd(a,p) = 1
- `lemma_bezout_inverse`: s*a ≡ 1 (mod p)
- `lemma_euclid`: p | ab, p prime → p | a or p | b
- `lemma_mod_inverse_unique`: uniqueness of modular inverse
- `inv_mod` spec + `inv_exec` (iterative extended GCD with cross-product invariant for overflow bounds)
- Full spec matching: `result@ == self@.inv_mod()`

**Key insight**: Bezout gives the inverse directly. No Fermat's little theorem, no binomial coefficients, no factorial — just GCD + linear combination.

### 2. Kernel Overflow Safety (verus-cutedsl)

**File**: `src/kernel.rs`

Added `kernel_wf_1d` / `kernel_wf_2d` predicates requiring overflow proof (via `eval_with_arrays_fits_i64`) before GPU codegen. Closes the soundness gap: no overflow proof = no shader emission.

### 3. Multi-Limb GPU Arithmetic (verus-fractals)

**File**: `src/gpu_fixed_point.rs`

Built a complete stack of verified multi-limb ArithExpr operations:

**Layer 1 — Primitives**:
- `limb_read`, `limb_scatter` (buffer access patterns)
- `gen_add_carry`, `gen_sub_borrow` (carry/borrow chains as ArithExpr)
- `gen_partial_products` (schoolbook accumulator)
- `lemma_eval_add/div/mod/const` — structural eval helpers that give Z3 intermediate steps for deeply nested ArithExpr evaluation

**Layer 2 — Multi-limb operations**:
- `add_limbs_seq`, `sub_limbs_seq` — n-limb add/subtract
- `schoolbook_result_limb` — schoolbook multiply with carry chain
- `mul_result_limbs` — Karatsuba O(n^1.585) via recursive split
- `karatsuba_combine` — the full recursive Karatsuba with sub-problem combination
- `mul_truncate` — fixed-point multiply with truncation

**Layer 3 — Complex arithmetic**:
- `complex_add/sub/mul/square/double`
- `magnitude_sq`, `escape_check`, `glitch_check`
- `multi_limb_gt` — cascading comparison
- `select_expr/select_limbs` — conditional blend (for masking escaped pixels)

**Layer 4 — Kernels**:
- `perturbation_kernel_full` — δ_{n+1} = 2Zδ + δ² + Δc with escape + glitch detection
- `orbit_kernel` — Z = Z² + c (reference orbit computation)

**Key proof technique**: The `lemma_eval_add/div/mod/const` helpers are trivially true by ArithExpr definition but give Z3 the intermediate steps it needs to decompose deeply nested evaluations. Without them, Z3 can't compose "construct ArithExpr tree" with "evaluate ArithExpr tree" across recursive function boundaries.

### 4. RuntimeArithExpr Infrastructure (verus-cutedsl)

**File**: `src/arith_expr.rs`

- `clone()` — verified structural copy with `ensures result.view_spec() == self.view_spec()`, `decreases self`
- `eq()` — verified structural equality with `ensures result == (self.view_spec() == other.view_spec())`
- `spec_size()` — for termination measures
- `variant_tag()` — for canonical ordering
- `lt()` — lexicographic less-than with `decreases spec_size(self) + spec_size(other)` (combined size measure for swapped recursive calls)
- `normalize()` — sort commutative operands, matching spec `arith_normalize`

### 5. Normalization Infrastructure (verus-cutedsl)

**File**: `src/arith_expr.rs`

Spec level:
- `arith_size` — tree size for termination
- `arith_variant_tag` — variant ordering
- `arith_lt` — total order on ArithExpr (combined size measure)
- `arith_normalize` — canonical form with flattening:
  - `is_const_val` — check for identity/zero constants
  - `collect_add_terms` / `collect_mul_factors` — flatten nested Add/Mul into Seq
  - `sorted_insert` / `sort_exprs` — insertion sort by arith_lt
  - `rebuild_add` / `rebuild_mul` — right-associated rebuild from sorted terms
  - `arith_add_normalized` — flatten + sort + zero identity
  - `arith_mul_normalized` — flatten + sort + zero annihilation + one identity
- `lemma_normalize_preserves_eval` — normalization doesn't change evaluation (for non-Reduce exprs)

### 6. GpuFixedPoint Ring Architecture

**Key architectural evolution** (went through several designs):

1. **Ghost value shortcut** (rejected): GpuFixedPoint had `ghost value: int`, Ring axioms proved trivially on ghost values. Problem: exec `eq` can't read ghost state.

2. **GpuExpr intermediate type** (rejected): Introduced separate GpuExpr enum for high-level algebra. Problem: unnecessary complexity — ArithExpr already has all needed variants.

3. **Final design**: GpuFixedPoint wraps a single `ArithExpr` representing the ALGEBRAIC expression (Add, Mul, Sub, Const — no carry chains). `eqv` = `arith_normalize(self.expr) == arith_normalize(other.expr)`. Ring operations just build ArithExpr trees. Carry chains added during LOWERING (separate step).

**Why this works**:
- Ring axioms follow from normalization properties (sort handles commutativity, flatten handles associativity, identity/zero rules handle identities)
- `eq` at exec uses `RuntimeArithExpr::normalize()` + `RuntimeArithExpr::eq()` — both already verified
- Lowering to carry chain ArithExpr is proved correct via the eval lemmas in gpu_fixed_point.rs
- `perturbation_step::<GpuFixedPoint<4,2>>` generates the ArithExpr tree directly

### 7. RuntimeGpuFixedPoint (partial, needs architecture update)

**File**: `src/gpu_codegen.rs` (currently disabled — needs rewrite for final architecture)

Built exec-level carry chain construction (RuntimeArithExpr trees) with verified `view_spec` proofs connecting exec to spec. These functions will be reorganized into the LOWERING step in the final architecture:
- `build_carry` / `build_add_limb` / `build_add` — runtime carry chain matching spec `gen_add_carry`
- `build_borrow` / `build_sub_limb` / `build_sub` — runtime borrow chain matching spec `gen_sub_borrow`
- `build_zeros` / `build_one` / `clone_limbs` / `from_buffer` — helpers

All proved: `view_spec()` of runtime trees == spec ArithExpr. Uses `reveal_with_fuel(RuntimeArithExpr::view_spec, 5)` for cross-crate unfolding.

**Needs rewrite**: In the final architecture, RuntimeGpuFixedPoint wraps a SINGLE RuntimeArithExpr (simple algebra, no carry chains). The carry chain code moves to a lowering function. eq uses RuntimeArithExpr::normalize + eq (already verified).

## Key Lessons Learned

### 1. Bezout > Fermat for Modular Inverse
Don't prove Fermat's little theorem when Bezout gives the inverse directly. Saved ~300 lines of binomial coefficient infrastructure.

### 2. ArithExpr Eval Helpers Pattern
When proving ArithExpr evaluation, Z3 can't compose "construct tree" with "evaluate tree" across recursive boundaries. Define trivial lemmas like `lemma_eval_add(a, b, env, arrays)` that unfold one level of evaluation. These are zero-cost at proof level but essential for Z3 to chain reasoning.

### 3. Combined Size Measure for Comparisons
For `arith_lt(a, b)` which recursively calls `arith_lt(b1, a1)` (swapped), lexicographic `decreases a, b` fails. Use combined `decreases arith_size(a) + arith_size(b)` instead.

### 4. Ghost Values Are Cheating for Symbolic Types
Putting a `ghost value: int` on GpuFixedPoint makes Ring axioms trivially provable but creates a ghost that exec can't access — breaking RuntimeRingOps::eq. The honest approach: eqv via normalization of the actual representation (ArithExpr), not via a disconnected ghost value.

### 5. Separate Algebra from Implementation
GpuFixedPoint should store SIMPLE ArithExpr (just Add/Mul/Sub/Const). Carry chains and Karatsuba are LOWERING details added during code generation. Mixing algebra and implementation in one type makes Ring axioms impossible to prove structurally.

### 6. reveal_with_fuel for Cross-Crate Unfolding
When a spec function from crate A is used in a proof in crate B, Z3 often can't unfold it automatically. `reveal_with_fuel(function, N)` forces unfolding. Essential for `RuntimeArithExpr::view_spec` and `arith_normalize`.

### 7. Normalization for Ring Axioms
Commutativity: sort operands. Associativity: FLATTEN nested ops then sort. Identity/zero: constant folding. Distribution: expand Mul-over-Add. Each Ring axiom maps to a normalization property.

### 8. Deep Zoom Architecture
For Mandelbrot deep zoom with perturbation theory:
- Reference orbits computed on GPU (same verified multi-limb complex ops)
- Per-pixel perturbation with escape + glitch detection
- Glitch resolution via workgroup-local stream compaction between rounds
- One thread per orbit for reference computation (multi-limb sequential per thread)
- One thread per pixel for perturbation (single-register or multi-limb depending on zoom)

## Why This Architecture (Design Journey)

### The Goal
Write `perturbation_step` once (generic over Ring), plug in a GPU type, and get a verified GPU shader. The mathematical formula is proved correct by Ring axioms. The GPU implementation is proved correct by ArithExpr evaluation lemmas. No duplication.

### Attempt 1: GpuFixedPoint with ghost value
We first tried `GpuFixedPoint<N, F>` with `limbs: Seq<ArithExpr>` (per-limb carry chain trees) and `ghost value: int`. Ring axioms were trivially proved on the ghost int (commutativity of int addition, etc.). This compiled and `perturbation_step::<GpuFixedPoint<4,2>>` type-checked.

**Problem**: RuntimeRingOps requires `eq(&self, rhs) -> bool` where `ensures out == self.model().eqv(rhs.model())`. Since `eqv` compared ghost `int` values and `Ghost<int>` can't be read from exec code, `eq` was impossible to implement. We explored:
- Returning `true` always → violates ensures when values differ
- `proof { return ghost_comparison }` → can't return exec bool from proof block
- `i64` value tag mirroring the ghost → user rejected as "sus"

**Root cause**: The ghost value was "cheating" — it made Ring axioms trivially provable by hiding the real complexity behind a value that nothing could actually inspect at exec level. For RuntimeRational this pattern works because the exec data (BigInt) IS the mathematical value. For GpuFixedPoint, the exec data (ArithExpr trees) is a COMPUTATION, not a VALUE.

### Attempt 2: Normalized structural equality on ArithExpr limbs
We tried `eqv` = normalized structural equality of per-limb ArithExpr trees. Each GpuFixedPoint stored `Seq<ArithExpr>` (carry chain trees per limb). Normalization sorted commutative Add/Mul operands.

**Problem**: Commutativity worked (sorting), but ASSOCIATIVITY failed. `add(add(a,b), c)` and `add(a, add(b,c))` produce fundamentally different carry chain tree structures. One has `gen_add_result_limb(add_limbs_seq(a,b), c, j)` — a carry chain whose inputs are themselves carry chain results. The other has `gen_add_result_limb(a, add_limbs_seq(b,c), j)` — different nesting. No amount of commutative sorting makes these structurally identical.

**Root cause**: Carry chains are an IMPLEMENTATION DETAIL baked into the type. The algebra (a+b+c) is the same regardless of association, but the carry chain encoding differs.

### Attempt 3: GpuExpr (separate high-level type)
We introduced `GpuExpr` — a simplified expression type (Input/Zero/One/Add/Sub/Mul/Neg) without carry chains. GpuFixedPoint stored `GpuExpr`. Ring operations built GpuExpr trees. Carry chains added during lowering.

**Problem**: GpuExpr was just a subset of ArithExpr. All the same variants existed in ArithExpr already. Having two parallel type hierarchies (GpuExpr + ArithExpr, RuntimeGpuExpr + RuntimeArithExpr) doubled the code with no benefit.

### Final Design: Simple ArithExpr with normalization
GpuFixedPoint stores a single `ArithExpr` in SIMPLE form — just Add/Mul/Sub/Const of inputs. No carry chains, no Karatsuba. Ring operations build simple trees:
```
add(a, b) = GpuFixedPoint { expr: Add(a.expr, b.expr) }
mul(a, b) = GpuFixedPoint { expr: Mul(a.expr, b.expr) }
zero() = GpuFixedPoint { expr: Const(0) }
```

`eqv` = `arith_normalize(self.expr) == arith_normalize(other.expr)` where normalization flattens, sorts, and simplifies. Ring axioms follow from normalization properties. `eq` at exec uses RuntimeArithExpr::normalize + eq (both already verified).

Carry chains and Karatsuba are added by a LOWERING function that converts the simple ArithExpr to per-limb ArithExpr with carry chains. The lowering is proved correct via the evaluation lemmas we already built.

**Why this works**:
- Associativity: flattening `Add(Add(a,b),c)` and `Add(a,Add(b,c))` both produce `[a,b,c]` sorted → same canonical tree
- No carry chains at the Ring level → no structural mismatch
- eq is just RuntimeArithExpr comparison on small simple trees (not deeply nested carry chains)
- Lowering is separate, proved correct via eval lemmas, reuses all the gpu_fixed_point.rs code

**Why not just use semantic eqv (evaluation equality)?**
We considered `eqv = forall env, arrays: eval(self) == eval(other)`. Ring axioms are trivially provable. But `eq` at exec can't determine evaluation equality (undecidable for arbitrary expressions). The user pointed out it IS decidable for our specific expressions (finite algebraic trees over buffer reads), leading to the normalization approach.

### The eq Problem (spec/exec boundary)
The fundamental tension throughout: Ring's `eq` must return a `bool` at exec level that EXACTLY matches the spec-level `eqv`. For symbolic types where the exec data (ArithExpr trees) represents computation rather than values:

- **Writing ghost state is easy**: `Ghost(self.value + other.value)` — exec can construct Ghost values freely
- **Reading ghost state is hard**: `self.model_value@ == rhs.model_value@` — exec can't dereference Ghost

Every other Ring operation (add, mul, sub, neg) only WRITES ghost state (constructs output). Only `eq` READS ghost state (inspects inputs). This asymmetry is why eq is uniquely difficult.

**Solution**: Don't use ghost state for eqv. Use the actual representation (ArithExpr) with normalization. Then eq compares the representation directly — no ghost access needed.

### Why Multi-Limb Arithmetic on GPU Uses Unrolled Carry Chains (Not Scans)
For reference orbit computation at deep zoom (2^500 ≈ 16 limbs), we considered:
- **Parallel scan for carry propagation**: O(log n) depth but requires workgroup barriers, shuffle instructions, and new ArithExpr nodes. Overkill for n=16.
- **One thread per orbit, sequential carry**: Each GPU thread processes all 16 limbs sequentially. The carry chain is unrolled into nested ArithExpr subexpressions. No sync needed — parallelism comes from running many orbits simultaneously.

The sequential approach maps DIRECTLY to verus-fixed-point's CPU algorithm (same carry chain, just unrolled into ArithExpr instead of a loop). The scan approach only wins for n > ~1024 limbs.

### Why Karatsuba Instead of NTT or Schoolbook
- **Schoolbook** O(n²): Simplest but too slow for n=16 (256 multiply-accumulates per thread per iteration)
- **NTT** O(n log n): Overkill for n < 64, requires complex multi-stage pipeline with barriers
- **Karatsuba** O(n^1.585): Sweet spot for n=8-64 (typical deep zoom range). Recursively splits into 3 sub-problems. Clean ArithExpr unrolling. For n=16: 9 schoolbook sub-multiplies instead of 256 — 4x improvement.

## What Remains

### Critical Path (in dependency order)

**1. Fix arith_normalize rlimit + Runtime normalize update**
- `lemma_normalize_preserves_eval` hits rlimit with flattening — split into per-case helpers
- `RuntimeArithExpr::normalize` needs updating to do flattening (collect + sort + rebuild)
- Need runtime versions of collect/sort/rebuild

**2. Add remaining normalization rules**
- Sub elimination: Sub(a,b) → Add(a, Neg(b)) where Neg = Sub(Const(0), _)
- Distribution: Mul(a, Add(b,c)) → Add(Mul(a,b), Mul(a,c)) — needs careful termination measure
- Cancellation: Add(x, Neg(x)) → Const(0) — requires detecting inverse pairs

**3. GpuFixedPoint Ring axioms (no admits)**
- GpuFixedPoint wraps single ArithExpr (already decided, delete GpuExpr leftovers)
- Prove ALL axioms via arith_normalize properties:
  - Commutativity: sort (should work now)
  - Associativity: flatten + sort (needs flatten working)
  - Identity: constant folding (should work now)
  - Zero annihilation: constant folding (should work now)
  - Inverse: needs cancellation rule
  - Sub = Add + Neg: needs Sub elimination rule
  - Distribution: needs distribution rule

**4. RuntimeGpuFixedPoint with full RuntimeRingOps**
- Wraps single RuntimeArithExpr (simple algebra, matching GpuFixedPoint)
- model() maps to GpuFixedPoint via view_spec()
- eq via RuntimeArithExpr::normalize() + RuntimeArithExpr::eq() (both already verified!)
- All Ring operations build RuntimeArithExpr matching spec
- No ghost values needed — eq works on the actual representation

**5. Lowering: simple ArithExpr → per-limb ArithExpr with carry chains**
- `lower(expr, n, frac) -> Seq<ArithExpr>` converts the simple algebraic ArithExpr from GpuFixedPoint into per-limb ArithExpr with carry chains, Karatsuba, etc.
- The existing gpu_fixed_point.rs code (add_limbs_seq, mul_result_limbs, etc.) IS the lowering — just needs organizing as a function from simple ArithExpr to limb ArithExpr
- Prove lowering preserves evaluation via the existing eval lemmas (lemma_add_carry_correct etc.)
- Runtime version: builds Vec<RuntimeArithExpr> limbs from RuntimeArithExpr (the build_add/build_sub code already does this)

**6. Shader generation**
- Call perturbation_step with RuntimeGpuFixedPoint → get single RuntimeArithExpr (algebraic)
- Lower → Vec<RuntimeArithExpr> per-limb (with carry chains)
- Each limb RuntimeArithExpr → WgslExpr (trivial structural mapping)
- WgslExpr.emit() → WGSL string
- Wrap in compute shader boilerplate → complete GPU shader

**7. Full pipeline**
- Orbit computation kernel (GPU)
- Perturbation kernel with iteration loop + escape/glitch
- Glitch resolution with workgroup compaction
- WebGPU viewer

### Estimated Remaining Work
- Normalization extensions + Ring axioms: 1-2 sessions
- RuntimeGpuFixedPoint + lowering: 1 session
- Shader generation + pipeline: 1-2 sessions
- Viewer integration: 1 session

## File Map

| File | What | Status |
|------|------|--------|
| `verus-fixed-point/src/fixed_point/number_theory.rs` | GCD, Bezout, Euclid, primality | ✅ 18 verified |
| `verus-fixed-point/src/fixed_point/modular.rs` | ModularInt field axioms + inv_exec | ✅ 85 verified |
| `verus-cutedsl/src/kernel.rs` | kernel_wf overflow safety | ✅ 34 verified |
| `verus-cutedsl/src/arith_expr.rs` | ArithExpr normalize/clone/eq/lt/size | ✅ 109 verified |
| `verus-fractals/src/gpu_fixed_point.rs` | Multi-limb ArithExpr ops + kernels | ✅ 23 verified |
| `verus-fractals/src/gpu_ring_test.rs` | GpuFixedPoint Ring (needs rewrite) | 🔧 in progress |
| `verus-fractals/src/gpu_codegen.rs` | RuntimeGpuFixedPoint (needs update) | 🔧 disabled |
| `verus-group-theory/src/knuth_bendix.rs` | KB ensures fix | ✅ 32 verified |
| `verus-group-theory/src/benign.rs` | Embedding lemma fixes | ✅ 10 verified |
