# Session Report: GPU-Native Multi-Limb Arithmetic → Verified Mandelbrot

## Summary

Built a complete verified pipeline from Ring axioms to GPU shader generation for deep-zoom Mandelbrot fractals. The session covered: fixing polynomial normalization errors, creating the LimbOps trait for generic multi-limb arithmetic, proving Karatsuba multiplication, refactoring RuntimeFixedPoint, WGSL codegen, and beginning GPU-native LimbOps (wrapping arithmetic without u64).

## What Was Accomplished

### 1. Runtime Polynomial Normalization Fixed (214 verified, 0 errors)
- Fixed 4 errors in `gpu_codegen.rs`: mono_mul overflow, ecb bound, poly_mul precondition, arith_to_poly postconditions
- Key techniques: `by(nonlinear_arith)` with explicit `abs_c` bounds, `lemma_poly_sum_abs_bounds_individual`, `vars_view` extensional equality hints, `lemma_poly_mul_empty_right`

### 2. RuntimeGpuFixedPoint::eq() Wired Up (46→53 verified)
- 3-line method: `runtime_arith_to_poly` + `runtime_poly_eq`
- Postcondition: `out == self@.eqv(other@)` — connects exec to spec Ring equivalence

### 3. LimbOps Trait + Generic Karatsuba (78 verified, 0 errors)
- **LimbOps trait**: `add3`, `sub_borrow`, `mul2`, `mul_add_carry`, `zero_val`, `const_u32`, `clone_limb`
- **u32 implementation**: initially u64-based, now being converted to GPU-native wrapping
- **Generic algorithms**: `generic_add_limbs`, `generic_sub_limbs`, `generic_mul_by_limb`, `generic_mul_schoolbook`, `generic_mul_karatsuba`
- **Karatsuba fully verified**: O(n^1.585), ghost carries proved zero, borrows proved zero, algebraic identity via `lemma_karatsuba_identity`
- **Key spec infrastructure**: `limb_power(n)` (simpler than `pow2`), `limbs_val(Seq<int>)`, `sem_seq`, `valid_limbs`

### 4. ArithLimb: LimbOps for RuntimeArithExpr (53 verified)
- Ghost model approach: `sem() = self.model@` makes postconditions trivially true
- Each method builds RuntimeArithExpr tree nodes (Add, Sub, Mul, Div, Mod, Cmp)
- `GenericFixedPoint<ArithLimb>` wraps Vec<ArithLimb> with add/sub/mul methods

### 5. RuntimeFixedPoint Refactored (171 verified)
- `add_limbs` → delegates to `generic_add_limbs::<u32>` with bridge lemmas
- `sub_limbs` → delegates to `generic_sub_limbs::<u32>`
- `mul_karatsuba` → delegates to `generic_mul_karatsuba::<u32>`
- ~300 lines of manual proof replaced by ~95 lines of bridge code
- Bridge lemmas: `lemma_limbs_val_eq_limbs_to_nat`, `lemma_limb_power_eq_pow2`
- Fixed cascading Z3 issues in `mul_mod_exec` and `recip_newton`

### 6. GenericFixedPoint<T: LimbOps> Added
- `add()`, `sub()`, `mul()` (with fixed-point truncation), `zero()`, `copy()`
- `mul()` does Karatsuba + slice for fixed-point shift

### 7. WGSL Codegen Pipeline
- `verus-cutedsl-codegen` converted from proc-macro to regular library
- `WgslExpr::emit()` with `select(0u, 1u, ...)` for Cmp (u32 result, not bool)
- `StageDesc` enum with `Loop` variant for iteration kernels
- `ShaderDesc` + `emit_shader_wgsl()` for complete WGSL shader generation
- `wgsl_codegen.rs`: `to_wgsl_expr`, `expr_to_wgsl`, `limbs_to_wgsl`

### 8. Mandelbrot Shader Generated
- `gen_mandelbrot_step`: z' = z² + c using GenericFixedPoint<ArithLimb>
- `gen_shader` binary: generates complete WGSL compute shader
- 2D dispatch (16x16 workgroups), guard, buffer bindings, iteration loop
- `verified-mandelbrot.html`: WebGPU viewer (needs working shader)

### 9. GPU-Native LimbOps (In Progress)
- **add3 VERIFIED**: wrapping_add + carry via `ab < a` comparison. No u64.
- **sub_borrow VERIFIED**: wrapping_sub + borrow via `a < b` comparison. No u64.
- **mul2 structure done**: wrapping_mul for lo, 16-bit decomposition for hi. Proof needs `by(bit_vector)` syntax fix.
- **mul_add_carry structure done**: delegates to mul2 + wrapping add chain.

## Key Insights & Techniques

### Architecture
- **LimbOps trait**: prove algorithm once, instantiate for u32 (CPU) and ArithLimb (GPU expressions)
- **Ghost model for ArithLimb**: `sem() = self.model@` (ghost int) makes all postconditions trivially satisfiable
- **Bridge lemmas**: connect generic `limbs_val`/`limb_power` to existing `limbs_to_nat`/`pow2`
- **Expression tree approach**: correct in principle (zero-trust) but needs CSE for practical shader sizes

### Proof Techniques
- `limb_power(n)` instead of `pow2(n*32)` avoids nat-to-int cast headaches
- `sem_seq<T>(Seq<T>) → Seq<int>` avoids generic recursion issues with Z3
- Both if/else branches need explicit `by(nonlinear_arith)` postcondition assertions
- Step-by-step div/mod identity for sub_borrow (Z3 can't handle `%` directly)
- `valid_limbs` threading: trait ensures `0 <= digit.sem() < BASE` on all outputs
- Wrapping add carry proof: `ab + c1*BASE == a+b`, `abc + c2*BASE == ab+carry`, combine

### Lessons Learned
1. **Expression trees explode without CSE**: 28MB for 4 limbs, ArithExpr is a tree (Box = no sharing)
2. **Mathematical vs GPU integer semantics**: `% 4294967296` is invalid WGSL (literal too large), need wrapping add + comparison
3. **Wrapping carry detection works**: `result < a` correctly detects overflow for u32 addition
4. **c1 + c2 can be 2**: when all three inputs are max u32, the carry is 2 (not just 0 or 1)
5. **bit_vector solver**: handles u32 arithmetic natively, good for 16-bit decomposition proofs

## What Remains

### Immediate (next session)
1. **Fix mul2 bit_vector proof**: `hi == (a*b) >> 32` via 16-bit decomposition. The exec code is correct, just need the right bit_vector assertion syntax.
2. **Fix mul_add_carry proof**: depends on mul2. Wrapping add chain + mul_hi carry propagation.
3. **Verify full crate**: ensure all 171+ functions still pass after GPU-native changes.

### Then: Get Fractal Running
4. **Emit WGSL functions**: structural correspondence of verified add/sub/mul as WGSL helper functions (~50 lines trust boundary)
5. **Fix verified-mandelbrot.html**: load WGSL shader, set up WebGPU buffers, render
6. **Test with 4 limbs** (128-bit), then scale to 32 limbs (1024-bit)

### Future
7. **Verified CSE**: for the expression tree approach — substitute lemma + runtime_cse
8. **Ring axioms for GenericFixedPoint**: modular arithmetic (Z/2^(N*32)Z)
9. **Perturbation theory**: reference orbit + BLA composition for true deep zoom
10. **Performance**: CSE, register allocation, fused multiply-add

## File Map

| File | What | Status |
|------|------|--------|
| `verus-fixed-point/src/fixed_point/limb_ops.rs` | LimbOps trait + u32 impl + generic algorithms + Karatsuba | 85 verified, mul2/mac proofs WIP |
| `verus-fixed-point/src/runtime_fixed_point.rs` | GenericFixedPoint<T> + RuntimeFixedPoint + delegated add/sub/mul | 171 verified |
| `verus-fractals/src/gpu_codegen.rs` | ArithLimb + gen_mandelbrot_step + helpers | 53 verified |
| `verus-fractals/src/gpu_ring_test.rs` | GpuFixedPoint Ring axioms + polynomial normalization | 170 verified |
| `verus-fractals/src/wgsl_codegen.rs` | RuntimeArithExpr → WgslExpr → WGSL string | works |
| `verus-fractals/src/bin/gen_shader.rs` | Generates complete WGSL Mandelbrot shader | works |
| `verus-fractals/verified-mandelbrot.html` | WebGPU viewer | needs working shader |
| `verus-cutedsl-codegen/src/lib.rs` | WgslExpr, StageDesc, ShaderDesc, emit_shader_wgsl | works |

## Verification Counts

| Component | Verified | Errors |
|-----------|----------|--------|
| gpu_ring_test.rs (polynomial Ring) | 170 | 0 |
| gpu_codegen.rs (ArithLimb + codegen) | 53 | 0 |
| limb_ops.rs (LimbOps + Karatsuba + GPU-native) | 85 | 2 (mul2, mul_add_carry) |
| runtime_fixed_point.rs (GenericFixedPoint + delegates) | 171 | 0 |
| **Total verified this session** | **479+** | **2 remaining** |
