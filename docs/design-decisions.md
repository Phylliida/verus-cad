# Design Decisions & Rationale

Reference for why the verified GPU kernel architecture is designed the way it is. Each decision documents the alternatives considered, the reasoning, and which systems from the literature informed the choice.

## 1. Multi-output kernels: part of the algorithm, not the schedule

**Decision:** KernelSpec has `outputs: Seq<OutputSpec>` where each output has its own `(scatter, compute)` pair.

**Rejected alternative:** Single-output KernelSpec, with multi-output handled by fusing separate single-output kernels via a schedule transformation.

**Reasoning:** Every system in the literature (Halide, Futhark, ATL, SPIRAL, Exo-GPU, CuTe) treats multi-output as part of the algorithm, not the schedule. A Mandelbrot step IS one operation producing `(z_re, z_im, escaped, iter)`. Splitting into 4 kernels and fusing back creates a problem (fusion) and then solves it — the original algorithm never had separate kernels.

Single-output kernels use `single_output_kernel(guard, scatter, compute)` — a one-liner convenience constructor. Existing proofs reference `k.outputs[0].compute` which is a minimal change from the old `k.compute`.

## 2. Runtime parameters: codegen concern, not spec concern

**Decision:** ArithExpr uses `Const(m as int)` where `m: nat` is a Verus parameter. The spec is already parametric — proofs work for ANY m. The codegen emitter maps constants to either inline literals or uniform buffer reads.

**Rejected alternative:** Add `Param(nat)` as a new ArithExpr node with a separate parameter environment.

**Reasoning:**
- The spec level doesn't need Param. `gemm_kernel(m: nat, k_size: nat, n: nat)` already takes dimensions as Verus nats and the proof is universally quantified over all valid dimensions.
- Adding Param would require changing `arith_eval`'s signature to `arith_eval(expr, env, params)`, breaking all existing proofs (1570 functions).
- In Halide, `Param<int>` is a compile/runtime binding mechanism. In Exo, parameters are procedure-level. Both are execution concerns, not specification concerns.
- The codegen crate can handle this: emit `Const` as either `42u` (current, one shader per size) or `params.m` (uniform buffer read, one shader for all sizes). This is a WgslExpr emitter convention, not an ArithExpr change.

**When this might change:** If we need to prove properties that depend on parameters being "the same value across all threads" (uniform), we might add a Param distinction at the spec level. But for correctness of individual kernel elements, universally-quantified Const suffices.

## 3. In-place update: snapshot semantics, already correct

**Decision:** `kernel_eval` reads from the pre-dispatch buffer snapshot. In-place update works by having the same buffer appear in both Index reads (input) and OutputSpec writes (output).

**Reasoning:**
- `arith_eval_with_arrays(expr, env, inputs)` takes `inputs: Seq<Seq<int>>` — a fixed snapshot of buffer state before dispatch. No thread sees another thread's writes.
- This matches Exo-GPU's model: sequential semantics where reads happen before writes. `par_eval == seq_eval` for well-synchronized programs.
- For in-place update: the kernel reads `z_re[i]` (from snapshot) and writes `z_re[i]` (new value). The next Pipeline dispatch sees the updated buffer.
- Futhark uses uniqueness types for the same purpose. Our approach is simpler — the spec naturally has snapshot semantics.

**Explicit statement for kernel_eval:**
```
inputs = buffer state BEFORE this dispatch.
All reads (Index) see the pre-dispatch snapshot.
All writes (scatter) are collected and applied AFTER all threads complete.
For in-place update: same buffer appears in both Index reads and OutputSpec writes.
No thread sees another thread's in-flight writes (requires barriers, Phase 6).
```

## 4. Unary negation: emitter pattern-match, not new node

**Decision:** `Neg(a)` is expressed as `Sub(Const(0), a)` or `Mul(Const(-1), a)` in ArithExpr. The WGSL emitter pattern-matches these and emits `-x`.

**Rejected alternative:** Add `Neg(Box<ArithExpr>)` as a new node.

**Reasoning:**
- At the spec level, `Sub(Const(0), a)` correctly computes `-a`. Proofs work.
- Adding a node means extending `arith_eval`, `arith_eval_with_arrays`, `arith_eval_fits_i64`, `RuntimeArithExpr`, `view_spec`, `WgslExpr`, `SpirVBuilder`, and all Box-unfolding helpers. Significant surface area for a pure convenience.
- The emitter can detect the pattern: `Sub(Const(0), x)` → emit `(-x)`, `Mul(Const(-1), x)` → emit `(-x)`. This produces clean WGSL without spec changes.
- If ArithExpr trees become too ugly to read, Neg can be added later as sugar with a trivial `arith_eval` case.

## 5. Variable output count: Pipeline, not kernel extension

**Decision:** Variable-output patterns (marching cubes, particle emission, stream compaction) use a Pipeline of standard kernels: count → prefix sum → scatter.

**Rejected alternative:** Add variable-length output support to KernelSpec (dynamic output count per thread).

**Reasoning:**
- The pattern across all systems (Futhark's `filter`/`partition`, CUDA stream compaction) is always:
  1. Map kernel: compute per-thread output count
  2. Scan kernel: prefix sum of counts → output offsets
  3. Scatter kernel: write outputs at the computed offsets
- Each step is a standard single-output Kernel.
- The scatter kernel's scatter index uses `Index(prefix_sum_buf, Var(0))` — it reads the prefix sum result and uses it as the write offset. This is already expressible in ArithExpr (Index into a buffer written by a previous pipeline step).
- Adding dynamic output count to KernelSpec would complicate the type (output size depends on input data) and make proofs much harder (need to reason about total output size).
- Pipeline composition is the right abstraction level for multi-step algorithms.

## 6. ArithExpr: single untyped IR, types at emission

**Decision:** ArithExpr operates over mathematical `int`. Types (i32, u32, f32, bool) are emission-level concerns. The machine-integer bridge theorem proves that if all intermediate values fit in machine types, the GPU execution matches the spec.

**Rejected alternative:** Typed ArithExpr with `ScalarTy {Bool, I32, U32, F32, Tuple(...)}` and typed Const/Var nodes.

**Reasoning:**
- The spec level benefits from simplicity. `int` arithmetic has no overflow, no NaN, no rounding. Proofs are cleaner.
- Adding types would require: typed evaluation, type checking predicates, type-directed emission, cast nodes, and changing every existing proof.
- The machine-integer bridge theorem (already partially implemented as `arith_eval_fits_i64`) handles the spec→machine gap: "if all intermediates fit in i64, then i64 execution matches int spec."
- GPU types are an emission concern: the emitter chooses `u32` for indices, `i32` for values, casts where needed. The WGSL type checker (naga) validates the emitted code.
- Float is replaced by verified fixed-point (integer-backed with proved error bounds), so f32 types are not needed in the spec.

**When this might change:** If we need to reason about type-specific behavior (u32 wrapping, f32 rounding) at the spec level, we'd add types. But for the current integer + fixed-point kernel scope, untyped `int` is correct and simpler.

## 7. Guard as ArithExpr (0/1), not separate BoolExpr

**Decision:** The kernel guard is an ArithExpr that evaluates to 0 (inactive) or non-zero (active). Boolean AND is `Mul(Cmp, Cmp)`.

**Rejected alternative:** Separate `PredExpr` type for boolean expressions with `And`, `Or`, `Not` nodes.

**Reasoning:**
- Keeping one expression type (ArithExpr) means one `arith_eval`, one set of Box-unfolding helpers, one emitter. Adding a separate boolean type doubles the infrastructure.
- `Cmp(Lt, a, b)` returns 0 or 1 as `int`. `Mul(Cmp(..), Cmp(..))` correctly computes AND (since both are 0/1). The WGSL emitter pattern-matches `Mul(Cmp, Cmp)` and emits `(a < M && b < N)` — clean output.
- The guard only needs to be non-zero, not specifically 1. Any non-zero value means "active." This is robust.
- In the Exo-GPU model, guards are just expressions in the sequential program — no separate boolean language.

**Emitter pattern-matching:** `Mul(Cmp(..), Cmp(..))` → `(a && b)`. Verified in codegen tests, produces valid WGSL.

## 8. Reduce as ArithExpr node, not statement

**Decision:** `Reduce(var, bound, body)` is an ArithExpr node with spec `Σ_{i=0}^{bound-1} eval(body, env[var:=i])`. The emitter hoists it to a for-loop with accumulator via `emit_stmt`.

**Rejected alternative:** Separate statement-level Reduce (KernelStmt with ForLoop).

**Reasoning:**
- Keeping Reduce in ArithExpr means GEMM's compute is a single expression: `Reduce(Sum, k, K, A[i*K+k] * B[k*N+j])`. The proof is about ArithExpr evaluation, not imperative statement semantics.
- The `arith_eval` spec for Reduce is a simple recursive sum — easy to prove properties about (induction, splitting, commutativity).
- The emitter handles the expression→statement gap: `emit_stmt` hoists Reduce to `var acc = 0; for (...) { acc += body; }`. This is purely a rendering concern.
- Mutual recursion between `arith_eval` and `reduce_sum` is handled cleanly with 2-element decreases tuples.
- Statement-level Reduce would require a separate `stmt_eval` interpreter with mutable state semantics — much more complex to prove correct.

## 9. Separate KernelSpec (Verus) and KernelDesc (codegen)

**Decision:** The verified spec (`KernelSpec` in Verus) and the emission target (`KernelDesc` in the codegen crate) are separate types that mirror each other structurally.

**Reasoning:**
- Verus crates use the Verus toolchain and can't be imported as regular Rust library dependencies by proc-macro crates.
- The structural correspondence is auditable: `KernelSpec.outputs[i].scatter ↔ KernelDesc.outputs[i].scatter`, etc.
- KernelDesc has additional emission metadata (buffer names, workgroup size, dispatch dims, variable names) that the spec doesn't need.
- This is the same pattern as ArithExpr ↔ WgslExpr — proved correct in Verus, mirrored in codegen.

## 10. Schedule transformations: three families, not one

**Decision:** Distinguish schedule transformations (same algorithm, different execution), algebraic refinements (mathematical identities), and data-structure refinements (change representation).

**Reasoning from literature:**
- **Halide/Exo** treat tiling, fusion, thread mapping as schedule transformations. These don't change what's computed.
- **Online softmax** (flash attention) uses the identity that `Σ exp(x_i) / Σ exp(x_i)` can be computed incrementally with running max rescaling. This is an algebraic identity, not just reordering.
- **SPH spatial hashing** replaces O(N²) all-pairs with O(N·k) neighbor lists. This introduces an auxiliary data structure and changes the algorithm. The proof must show the hash query is complete (all neighbors within support are found).
- **Blelloch scan** restructures a sequential prefix sum into a tree — this uses monoid associativity, not just loop reordering.

These have different proof obligations:
- Schedule: `kernel_eval(transformed) == kernel_eval(original)` (direct equality)
- Algebraic: mathematical identity proof (e.g., monoid associativity)
- Data-structure: representation invariant proof (e.g., spatial hash completeness)

Treating them as one "schedule" concept conflates different proof patterns and makes the system harder to reason about.

## 11. Fixed-point instead of f32

**Decision:** All "float" computation uses verified fixed-point arithmetic with integer backing. Transcendentals (exp, sqrt, sin) are verified polynomial approximations with proved error bounds. No f32, no GPU intrinsic axioms.

**Rejected alternative:** Add f32 as a scalar type with axiomatized intrinsics.

**Reasoning:**
- Floating-point verification in SMT is notoriously hard. Z3's fp theory is slow and incomplete.
- GPU `exp()` is a hardware approximation anyway — axiomatizing it as "exact exp" is wrong, and axiomatizing it with error bounds is equivalent to what we do with fixed-point polynomials.
- Fixed-point arithmetic is pure integer math. Proofs are in the integer theory, which Z3 handles well.
- Error bounds are explicit and proved: `|fp_exp(x) - exact_exp(x)| < bound(N)`.
- For applications that genuinely need IEEE f32 (ML training), f32 can be added later as a clearly-axiomatized extension. But for rendering, simulation, and inference, fixed-point is sufficient and fully verifiable.

**The verus-fixed-point and verus-interval-arithmetic libraries** (176 and 220 verified functions respectively) already provide the infrastructure.

## 12. Pipeline for multi-kernel algorithms

**Decision:** A `Pipeline` type (`Dispatch | Seq | Repeat | RepeatUntil`) handles multi-kernel orchestration at the host level.

**Reasoning:**
- 20/27 analyzed applications need multiple kernel launches per timestep/frame.
- Iterative algorithms (Mandelbrot, physics, conjugate gradient) are `Repeat` or `RepeatUntil` over a step kernel.
- Multi-pass algorithms (radix sort, hierarchical reduction, stream compaction) are `Seq` of kernel dispatches.
- Each individual dispatch is a standard `KernelSpec` — the Pipeline composes them.
- Buffer state flows between dispatches: kernel B reads what kernel A wrote.
- Pipeline semantics: `pipeline_eval(Seq([k1, k2]), bufs) = kernel_eval(k2, kernel_eval(k1, bufs))`.
- This keeps KernelSpec simple (single dispatch) while supporting arbitrary multi-kernel algorithms.
