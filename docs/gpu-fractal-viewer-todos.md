# GPU Deep Zoom Fractal Viewer — TODO List

## Completed This Session
- [x] Field axioms for ModularInt (Bezout + inverse, spec + exec)
- [x] kernel_wf overflow safety enforcement for ArithExpr codegen
- [x] Multi-limb ArithExpr add (carry chain, fully proved)
- [x] Schoolbook multiply ArithExpr (partial products, carry chain, proved)
- [x] Karatsuba multiply ArithExpr (O(n^1.585), recursive split/combine)
- [x] Complex arithmetic on ArithExpr (add, sub, mul, square, double)
- [x] GpuFixedPoint<N, F> implementing Ring (const generics, spec level)
- [x] Perturbation kernel spec (δ = 2Zδ + δ² + Δc with escape/glitch detection)
- [x] Orbit computation kernel spec (Z = Z² + c)
- [x] Multi-limb comparison, magnitude, select/blend
- [x] RuntimeArithExpr clone (fully verified, decreases self)
- [x] RuntimeArithExpr eq (structural equality, fully verified)
- [x] RuntimeGpuFixedPoint add/sub/neg (exec level, view_spec proved)
- [x] RuntimeGpuFixedPoint from_buffer, zeros, one, clone (exec level, proved)
- [x] Canonical ordering spec (arith_variant_tag, arith_lt)
- [x] Normalization spec (arith_normalize for commutative ops)

## In Progress

### ArithExpr Normalization (verus-cutedsl/src/arith_expr.rs)
- [ ] Fix arith_lt termination: needs combined size measure `decreases arith_size(a) + arith_size(b)` instead of `decreases a, b` (swapped recursive calls don't decrease lexicographically)
- [ ] Fix RuntimeArithExpr::lt termination: same issue
- [ ] Fix lemma_normalize_preserves_eval: Reduce case needs induction over reduce body; Add/Mul cases may need eval helpers
- [ ] Runtime normalize: ensures result.view_spec() == arith_normalize(&self.view_spec())

### GpuFixedPoint Ring Axioms — Honest Proofs (verus-fractals/src/gpu_ring_test.rs)
- [ ] Change eqv from ghost value comparison to normalized structural equality of ArithExpr limbs
- [ ] Re-prove all Ring axioms with the new eqv:
  - [ ] Commutativity (add, mul): follows from normalization sorting operands
  - [ ] Associativity (add, mul): requires proving evaluation equivalence of differently-nested carry chains (use lemma_add_carry_correct)
  - [ ] Distributivity: mul distributes over add at evaluation level
  - [ ] Identity (zero, one): normalized identity trees are canonical
  - [ ] Inverse (neg): neg produces correct normalized tree
- [ ] These are the REAL proofs — no ghost value shortcuts

### RuntimeGpuFixedPoint eq (verus-fractals/src/gpu_codegen.rs)
- [ ] Implement eq via: normalize both sides, then structural compare
- [ ] Prove: normalized structural equality ↔ spec-level eqv
- [ ] This makes RuntimeRingOps::eq fully verified

### RuntimeGpuFixedPoint mul (verus-fractals/src/gpu_codegen.rs)
- [ ] Build runtime Karatsuba that constructs RuntimeArithExpr matching spec mul_truncate
- [ ] Prove view_spec of runtime tree == spec ArithExpr (same pattern as build_add)

## Next Steps (After Above Complete)

### Shader Generation Pipeline
- [ ] RuntimeArithExpr → WgslExpr conversion (trivial structural mapping)
- [ ] perturbation_step_exec generic over SymbolicRingOps or RuntimeRingOps
- [ ] Call with RuntimeGpuFixedPoint<4, 2> to generate WGSL shader
- [ ] Test: emit shader, validate with naga

### Full Perturbation Kernel
- [ ] Iteration loop (Stage::Loop wrapping perturbation step)
- [ ] Escape detection in shader (magnitude check)
- [ ] Glitch detection in shader (|δ| > |Z| check)
- [ ] Orbit buffer indexing (read Z_n at current iteration)

### Reference Orbit Computation (GPU)
- [ ] Orbit kernel: Z = Z² + c using same multi-limb ops
- [ ] Multiple orbits in parallel (one thread per orbit)
- [ ] Upload/dispatch from host

### Glitch Resolution Pipeline
- [ ] Round 1: compute orbit + perturbation for all pixels
- [ ] Detect glitched pixels
- [ ] Round 2+: new orbit at glitch point, re-render subset
- [ ] Stream compaction between rounds (existing scan infrastructure)

### Viewer Application
- [ ] WebGPU HTML viewer with zoom/pan
- [ ] CPU reference orbit fallback for initial zoom
- [ ] Color mapping from escape times
- [ ] Adaptive iteration count

## Architecture Notes (UPDATED)

### Key Decision: GpuFixedPoint wraps ArithExpr directly (no GpuExpr)

GpuFixedPoint<N, F> stores a single ArithExpr in SIMPLE algebraic form
(just Add/Mul/Sub/Const — NO carry chains, NO Karatsuba). Ring operations
build simple ArithExpr trees. Carry chains are added during LOWERING to
the executable form.

- **Spec**: GpuFixedPoint<N, F> { expr: ArithExpr } implements Ring
- **eqv**: arith_normalize(self.expr) == arith_normalize(other.expr)
- **Ring axioms**: proved via arith_normalize properties (sort, flatten, identity, distribute)
- **Exec**: RuntimeGpuFixedPoint<N, F> { expr: RuntimeArithExpr } implements RuntimeRingOps
- **eq**: RuntimeArithExpr::normalize() then RuntimeArithExpr::eq() (both already verified!)
- **Lowering**: GpuFixedPoint.expr → per-limb ArithExpr with carry chains (gpu_fixed_point.rs)
- **Codegen**: RuntimeArithExpr → WgslExpr → WGSL string (auditable trust boundary)
- **Overflow**: kernel_wf_1d/2d enforces arith_eval_fits_i64 before emission

### What arith_normalize needs (extend in verus-cutedsl/src/arith_expr.rs)
Current: sort commutative operands (Add, Mul)
Need to add:
1. Identity: Add(x, Const(0)) → x, Mul(x, Const(1)) → x
2. Zero annihilation: Mul(x, Const(0)) → Const(0)
3. Flatten: Add(Add(a,b), c) → right-associated sorted form
4. Distribution: Mul(a, Add(b,c)) → Add(Mul(a,b), Mul(a,c))
5. Neg: Sub(Const(0), Sub(Const(0), x)) → x (double neg)
6. Sub elimination: Sub(a, b) → Add(a, Sub(Const(0), b))

### GpuExpr type is UNNECESSARY — delete it
The GpuExpr type in gpu_ring_test.rs should be removed. ArithExpr already
has all the variants needed. GpuExpr was just a subset of ArithExpr.
