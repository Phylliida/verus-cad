# Session Report: Verified GPU Kernel Foundation

## Summary

This session built a complete verified foundation for GPU compute kernels, from extending the ArithExpr IR through architecture design informed by 10+ research systems, to proving 6 kernel constructors correct with 30+ foundational lemmas. The work spans verus-cutedsl (1630 verified functions), verus-cutedsl-codegen (20 tests), verus-gpu-examples (4 GPU kernels), verus-fractals (8 verified functions), and comprehensive architecture documentation.

---

## 1. ArithExpr Extensions

### What was built

Extended the verified ArithExpr IR from 7 nodes to 11:

| Node | Spec | Session addition |
|------|------|-----------------|
| `Sub(a, b)` | `eval(a) - eval(b)` | New |
| `Cmp(op, a, b)` | `if a op b then 1 else 0` (Lt/Le/Gt/Ge/Eq/Ne) | New |
| `Reduce(var, bound, body)` | `Σ_{i=0}^{bound-1} eval(body, env[var:=i])` | New |
| `Shr(a, b)` | `a / 2^b` (arithmetic right shift) | New |

### Key technical challenges solved

**Mutual recursion for Reduce**: `arith_eval` calls `reduce_sum`, which calls `arith_eval` on the body. Verus requires compatible decreases clauses across mutually recursive functions. Solution: 2-element tuple decreases `(expr, 0int)` for `arith_eval` and `(body, n)` for `reduce_sum`, ensuring the first element (ArithExpr) decreases when crossing from reduce back to eval, and the second element (iteration count) decreases within the reduction loop.

**Box unfolding**: Z3 consistently struggles to unfold `arith_eval` through `Box<ArithExpr>` wrappers in enum variants. Every new node required a corresponding Box-unfolding helper lemma (e.g., `lemma_arith_eval_shr`, `lemma_arith_eval_cmp`). These are trivially provable (empty bodies) but essential — without them, Z3 cannot connect `arith_eval(&ArithExpr::Add(Box::new(*a), Box::new(*b)), env)` to `arith_eval(a, env) + arith_eval(b, env)`.

**`return` per branch**: For functions with multiple match arms or if-else branches, Z3 performs better when each branch has an explicit `return` statement. This isolates postcondition checking per exit point, avoiding cross-branch context pollution. Discovered during the `runtime_arith_eval` proof for the exec evaluator.

**Euclidean vs truncating division**: Verus `int` division is Euclidean (rounds toward -∞), while Rust `i64` division is truncating (rounds toward 0). These agree only for non-negative operands. The exec evaluator's Div/Mod cases required non-negative preconditions (`arith_eval_fits_i64` checks `arith_eval(a, env) >= 0 && arith_eval(b, env) > 0` for Div/Mod). The `nonneg_i64_div` and `nonneg_i64_mod` helper functions encapsulate this.

---

## 2. Kernel Framework

### KernelSpec type

```rust
struct KernelSpec {
    guard: ArithExpr,           // thread active iff eval != 0
    outputs: Seq<OutputSpec>,   // multiple (scatter, compute) pairs
}
struct OutputSpec {
    scatter: ArithExpr,         // WHERE to write
    compute: ArithExpr,         // WHAT to write
}
```

### Design evolution

**Single-output → multi-output**: Initially designed as `(guard, scatter, compute)`. Changed to `(guard, outputs: Seq<OutputSpec>)` after recognizing that multi-output is fundamental to GPU kernels (Mandelbrot step writes z_re, z_im, escaped, iter). Every system in the literature (Halide, Futhark, ATL, SPIRAL, Exo-GPU, CuTe) treats multi-output as part of the algorithm, not the schedule. Splitting into 4 single-output kernels and fusing back is artificial.

**Convenience**: `single_output_kernel(guard, scatter, compute)` wraps the common single-output case.

### Proved kernel constructors (6)

| Kernel | Pattern | Key proof technique |
|--------|---------|-------------------|
| GEMM | 2D dispatch, Reduce(Sum), row-major gather | Induction on K, Box-unfolding via `lemma_eval_with_arrays_linear_index` |
| Vector add | 1D dispatch, element-wise | Direct Box unfolding for Add(Index, Index) |
| Dot product | Single-thread, Reduce(Sum) | Induction on N with Index Box unfolding |
| Layout offset | 1D dispatch, CuTe offset_expr | Delegates to existing `lemma_offset_expr_correct` |
| 1D convolution | 1D dispatch, sliding-window Reduce | Induction on W, `lemma_eval_with_arrays_add` for offset index |
| Scan (prefix sum) | 1D dispatch, variable-bound Reduce | Induction on kk, bound = `Add(Var(0), Const(1))` |

### Proved foundational properties (30+)

**env_with**: `lemma_env_with_at` (sets target), `lemma_env_with_other` (preserves others), `lemma_env_with_len` (length bound), `lemma_env_with_commutes` (distinct vars commute).

**Cmp**: `lemma_cmp_returns_01` (always 0 or 1), `lemma_cmp_mul_is_and` (Mul(Cmp, Cmp) = boolean AND).

**Reduce base cases**: `lemma_reduce_sum_zero` (bound 0 = 0), `lemma_reduce_sum_one` (bound 1 = single eval).

**Reduce splitting** (THE key schedule lemma): `lemma_reduce_sum_split` — `Σ_{i=0}^{a+b-1} f(i) == Σ_{i=0}^{a-1} f(i) + Σ_{i=0}^{b-1} f(a+i)`. Proved by induction on b using `reduce_sum_shifted`. This single lemma enables all tiled schedule transformations.

**Reduce algebraic**: `lemma_reduce_sum_const` (Σc = n*c), `lemma_reduce_sum_linear` (Σ(f+g) = Σf + Σg), `lemma_reduce_sum_scalar` (Σ c*f = c*Σf).

**Reduce interchange**: `lemma_reduce_sum_interchange` — `Σ_i Σ_j f(i,j) == Σ_j Σ_i f(i,j)`. The hardest proof in the session. Required: env_with commutativity, peeling inner reduce last term (`reduce_sum_peeled`), connecting peeled terms back to standard reduce, and a zero-bound base case. All without `assume(false)`.

**Free variables**: `free_of_var` predicate, `lemma_eval_independent_of_unused_var` — changing an unused variable doesn't affect evaluation. Critical for parallelism proofs.

**Index-free equivalence**: `index_free` predicate, `lemma_eval_equiv_no_index` — `arith_eval` and `arith_eval_with_arrays` agree for expressions without Index nodes.

**Scatter injectivity**: `scatter_injective` predicate, `lemma_injective_scatter_unique_writer`, `lemma_gemm_scatter_injective` (i*N+j is injective), `lemma_identity_scatter_injective`.

**Guard correctness**: Proved for vector_add, dot_product, conv1d, scan.

**Output bounds**: `lemma_identity_scatter_bounds`, `lemma_gemm_scatter_bounds` (i*N+j < M*N).

**Contraction bridge**: `lemma_gemm_partial_sum_bridge` — connects kernel's `gemm_partial_sum_int` (Seq<int>) to contraction's `gemm_partial_sum` (Seq<i64>).

**Multi-output example**: `swap_kernel` with both outputs proved correct.

**kernel_eval spec**: `kernel_eval_1d` + `kernel_find_writer_1d` — full kernel output semantics for 1D dispatch.

---

## 3. Literature Review & Architecture

### Systems studied

#### SPIRAL (IEEE '05, '18)
- **Key idea adopted**: Gather/Scatter with composable index functions. Every kernel = gather input via index function, compute, scatter output via index function. Each index function is an ArithExpr.
- **What they lack**: No proof assistant. Correctness relies on mathematical identities being correct, not mechanically verified.
- **Citation**: Püschel et al., "SPIRAL: Code Generation for DSP Transforms", Proceedings of the IEEE 2005; Franchetti et al., "SPIRAL: Extreme Performance Portability", IEEE 2018.

#### Halide (PLDI '13, CACM '18)
- **Key idea adopted**: Algorithm/schedule separation. The algorithm (what to compute) never changes; all optimization is schedule (how to compute). Schedules are semantics-preserving by construction.
- **What they lack**: Schedule correctness is compiler-trusted, not proved. The ATL work later verified a Halide-like lowering algorithm in Coq.
- **Citation**: Ragan-Kelley et al., "Halide: A Language and Compiler for Optimizing Parallelism, Locality, and Recomputation in Image Processing Pipelines", PLDI 2013; Ragan-Kelley et al., "Halide: Decoupling Algorithms from Schedules for High-Performance Image Processing", CACM 2018.

#### ATL — A Verified Compiler for a Functional Tensor Language (PLDI '24)
- **Key idea adopted**: Verified tensor lowering in Coq. Their verification process found a real bug in the truncation reshape operator — the same class of bug we independently found in `compose_single` (case 2 truncation when `b_shape % q != 0`). This validates that formal verification catches bugs testing misses.
- **What they lack**: No GPU backend, no schedule transformations.
- **Citation**: Gilboa et al., "A Verified Compiler for a Functional Tensor Language", PLDI 2024.

#### RISE / LIFT (CGO '17)
- **Key idea adopted**: Verified rewrite rules for parallel patterns. Programs are compositions of `map`, `reduce`, `scan`, `split`, `join`, `slide`. Lowering via semantics-preserving rewrite rules that transform high-level patterns to hardware-specific variants (`map` → `mapGlobal`/`mapWorkgroup`/`mapSeq`).
- **Architecture insight**: Three-level IR (RISE functional → DPIA imperative → OpenCL). Barrier insertion automatic at the imperative level.
- **What they lack**: No fine-grained async/split barriers. Cannot express Hopper-era GPU features.
- **Citation**: Steuwer et al., "LIFT: A Functional Data-Parallel IR for High-Performance GPU Code Generation", CGO 2017; Hagedorn et al., "Achieving High-Performance the Functional Way", ICFP 2020.

#### Exo / Exo 2 (PLDI '22, ASPLOS '25)
- **Key idea adopted**: User-definable scheduling with verified rewrites. Each primitive rewrite is independently proved correct via an effect system.
- **What they lack**: Effect system provides checking, not full proofs in a proof assistant.
- **Citation**: Ikarashi et al., "Exocompilation for Productive Programming of Hardware Accelerators", PLDI 2022; Ikarashi et al., "Exo 2: Growing a Scheduling Language", ASPLOS 2025.

#### Exo-GPU (PLDI '26)
- **Key idea adopted**: Parallelism and barriers are ANNOTATIONS on sequential code. The sequential interpretation `seq[p]` defines the spec. Two separate verification checks: (1) algorithmic correctness — each schedule rewrite preserves sequential semantics, (2) synchronization correctness — parallel execution with barriers matches sequential execution via abstract machine interpretation.
- **Architecture insight**: The scheduled kernel is the same program as the spec, just with annotations. No separate "scheduled IR" is needed — the annotations are overlaid. Barriers are first-class statements with timeline parameters, not intrinsic function calls.
- **What they lack**: Abstract machine checking, not full proof assistant verification.
- **Citation**: Described in session research; PLDI 2026 paper.

#### Futhark (PLDI '17)
- **Key idea adopted**: Segmented parallel patterns (SegMap, SegRed, SegScan, SegHist). Aggressive fusion of element-wise operations. Automatic flattening of nested parallelism.
- **What they lack**: No formal verification.
- **Citation**: Henriksen et al., "Futhark: Purely Functional GPU-Programming with Nested Parallelism and In-Place Array Updates", PLDI 2017.

#### Dex (Google)
- **Key idea noted**: Typed indices — array dimensions are types, preventing dimension-mismatch bugs statically. `Fin n` type represents indices {0,...,n-1}.
- **What they lack**: No formal verification, no GPU performance tuning.
- **Citation**: Paszke et al., "Getting to the Point: Index Sets and Parallelism-Preserving Autodiff for Pointful Array Programming", arXiv 2021.

#### CuTe / CUTLASS (NVIDIA)
- **Key idea adopted**: Layout algebra — compose, divide, complement. Thread-value (TV) decomposition maps tile dimensions to GPU blocks/threads. Pipeline abstraction for async copy with circular buffer stages.
- **What they lack**: No formal verification. We verified the layout algebra in Verus (1553+ functions).
- **Citation**: NVIDIA CUTLASS documentation; Thakkar et al., "CUTLASS: Principled Abstractions for Handling Multidimensional Data through Tensors and Spatial Microkernels", NVIDIA 2023.

#### AnyDSL / Thorin (OOPSLA '18, CGO '15)
- **Key idea noted**: GPU codegen = partial evaluation. Write unified host+device code, partially evaluate with concrete thread IDs to extract kernel bodies. Elegant but no formal verification.
- **Citation**: Leißa et al., "AnyDSL: A Partial Evaluation Framework for Programming High-Performance Libraries", OOPSLA 2018.

#### Descend (PLDI '24)
- **Key idea noted**: Rust-like ownership/borrow checking for GPU programs. `sync()` releases borrows of shared memory — if you forget a sync, the borrow checker flags it.
- **What they lack**: No tensor cores, no split barriers, limited scope.
- **Citation**: Steuwe et al., "Descend: A Safe GPU Systems Programming Language", PLDI 2024.

#### GPUVerify (Imperial College)
- **Key idea noted**: Verifies existing CUDA/OpenCL kernels for data races and barrier divergence. Not a code generator — verifies hand-written GPU code.
- **Relevance**: Barrier divergence and race-freedom need clear legality conditions. Our ScheduledKernel design incorporates this: barrier control flow must be uniform (no early return before barrier).
- **Citation**: Betts et al., GPUVerify project, Imperial College London.

### Architecture decisions informed by reading

1. **Gather → Compute → Scatter** (from SPIRAL): Every kernel is three index functions. All are ArithExpr trees.

2. **Algorithm/schedule separation** (from Halide/Exo): Spec Kernel = what to compute. Schedule transformations = how. Proved in Verus, not compiler-trusted.

3. **Two-level verification** (from Exo-GPU): (a) schedule rewrites preserve sequential semantics, (b) synchronization checker proves parallel = sequential. Independent proof obligations.

4. **Three transformation families** (synthesized from all): Schedule (tiling, fusion, thread mapping — same algorithm), Algebraic (online softmax, Blelloch scan — mathematical identities), Data-structure (spatial hashing, sparse formats — representation change). Different proof patterns.

5. **Fixed-point instead of f32** (our innovation): All computation over integers. Transcendentals as verified polynomial approximations. No GPU intrinsic axioms. Zero trust in compute path beyond proof checker + GPU integer arithmetic + driver.

6. **Monoid generalization** (from Futhark/RISE, deferred to Phase 4): FlashAttention's online softmax as an associative monoid over `(max, sum_exp, acc)` tuples. Tiling, parallel reduction, scan all follow from one generic `reduce_split` lemma. Sum/Max/Min are instances.

7. **Pipeline for multi-kernel** (from Futhark/CuTe): `Dispatch | Seq | Repeat | RepeatUntil` for host orchestration. Mandelbrot = `RepeatUntil(step_kernel, max_iter)`. Radix sort = `Repeat(4, Seq([histogram, scan, scatter]))`.

---

## 4. Codegen Pipeline

### WgslExpr emission

`WgslExpr` mirrors `ArithExpr` structurally. The `emit()` method is the auditable trust boundary (~50 lines). Key emission rules:

- `Mul(Cmp(..), Cmp(..))` → `(a < M && b < N)` (pattern-matched to boolean AND)
- `Reduce(var, bound, body)` → `var acc = 0; for (var v = 0u; v < bound; v++) { acc += body; }` (hoisted to statements via `emit_stmt`)
- `Select` → structured `if` (NOT WGSL `select()` which evaluates both branches eagerly — safety issue identified during architecture review)

### KernelDesc → WGSL

`emit_kernel_wgsl(k: &KernelDesc)` generates complete, naga-validated WGSL compute shaders from the kernel description. Handles multi-output (emits a store per output), guard (emits `if (!guard) { return; }`), thread variable extraction (gid.x, gid.y, gid.z).

### SPIR-V backend (WIP)

Direct binary emission from WgslExpr, bypassing naga/tint. Currently emits arithmetic instruction trees (OpIAdd, OpIMul, OpSDiv, OpSMod, OpAccessChain, OpLoad). Missing: entry point, execution mode, buffer decorations, structured control flow for loops.

### Generated shaders (naga-validated)

- Vector add (256 workgroup)
- Naive GEMM (16×16 workgroup, verified index expressions)
- Dot product (single workgroup, Reduce loop)
- Layout offset (CuTe offset_expr)
- Mandelbrot (fixed-point 20.12, iterative)

---

## 5. GPU Cross-Validation

### verus-gpu-examples

wgpu-based GPU dispatch with CPU cross-validation. Graceful fallback when no GPU available. Tests:
- Vector add: 1024 elements, GPU == CPU
- GEMM: 32×32, GPU == CPU
- Dot product: 64 elements, GPU == CPU
- Mandelbrot: 256×256 fixed-point, GPU == CPU

### Mandelbrot fixed-point overflow fix

Original 16.16 format overflowed i32 on GPU (`z_re * z_re` where `|z_re|` up to ~6×65536 = 393216, squared > i32::MAX). Fixed by reducing to 20.12 format. Overflow analysis: after a non-escaping iteration |z| ≤ 2, so |z_new| ≤ |z|²+|c| ≤ 6, giving max raw product (6×4096)² = 604M < 2³¹.

---

## 6. verus-fractals: Complex Fixed-Point

### ComplexFP type

Wraps two `FixedPoint` components (re, im) from verus-fixed-point. Operations:
- `add`, `sub`, `neg` — component-wise, exact
- `square` — `z² = (re²-im², 2·re·im)`, widens to 2N limbs
- `norm_sq` — `|z|² = re² + im²`, widens
- `mandelbrot_step` — `z² + c`, widens
- `promote_to`, `reduce_down` — precision management

### Mandelbrot iteration spec

- `escape_time(z, c, threshold, max_iter)` — iterate z=z²+c until |z|²>threshold
- `lemma_escape_time_bounded` — escape time ≤ max_iter
- `lemma_escaped_returns_count` — escaped z returns immediately
- `lemma_step_is_square_plus_c` — mandelbrot step = z² + c (component-wise)

---

## 7. Proof Gap Audit & Fixes

### Audit findings (10 items, all fixed)

| # | Issue | Fix |
|---|-------|-----|
| 1 | Missing `lemma_arith_eval_cmp` | Added + arrays variant |
| 2 | Missing `lemma_eval_with_arrays_sub` | Added |
| 3 | No `arith_eval` ↔ `arith_eval_with_arrays` equivalence | Added `index_free` + `lemma_eval_equiv_no_index` |
| 4 | `arith_eval_fits_i64` Reduce = `true` | Strengthened to check bound expression |
| 5 | No `kernel_eval` spec | Added `kernel_eval_1d` + `kernel_find_writer_1d` |
| 6 | Missing guard correctness | Proved for 4 kernels |
| 7 | Missing scatter injectivity | Proved identity + GEMM i*N+j |
| 8 | Missing output bounds | Proved identity + GEMM |
| 9 | No GEMM contraction bridge | Added `lemma_gemm_partial_sum_bridge` |
| 10 | No multi-output example | Added `swap_kernel` with both outputs proved |

---

## 8. Design Decisions (documented in docs/design-decisions.md)

1. **Multi-output as algorithm** — not schedule. Every system agrees.
2. **Runtime params as codegen concern** — spec already parametric via Verus nats.
3. **In-place update via snapshot semantics** — reads see pre-dispatch state.
4. **Unary minus as emitter pattern-match** — Sub(Const(0), x) → emit `-x`.
5. **Variable output via Pipeline** — count → scan → scatter, each a standard Kernel.
6. **Untyped `int` IR** — types at emission level, machine-int bridge theorem.
7. **Guard as ArithExpr 0/1** — not separate BoolExpr. Mul(Cmp, Cmp) = AND.
8. **Reduce as expression node** — not statement. Enables algebraic proofs.
9. **Separate KernelSpec/KernelDesc** — Verus/codegen split, structural correspondence.
10. **Three transformation families** — schedule/algebraic/data-structure.
11. **Fixed-point instead of f32** — zero axioms in compute path.
12. **Pipeline for multi-kernel** — Dispatch | Seq | Repeat | RepeatUntil.

---

## 9. Application Coverage Analysis

27 GPU applications analyzed (docs/gpu-compute-application-analysis.md). Pattern frequency:
- Map: 25/27, Gather: 20/27, Reduce: 17/27, Scatter: 10/27, Scan: 7/27, Stencil: 6/27, Sort: 5/27

Current 11-node ArithExpr covers ~20 applications directly. Remaining need: Select (8 apps), Reduce(Max/Min) (5 apps), BitXor (swizzle, sort), shared memory (10 apps), atomics (5 apps).

---

## 10. Final Numbers

| Component | Count |
|-----------|-------|
| verus-cutedsl verified functions | 1630 |
| verus-fractals verified functions | 8 |
| verus-fixed-point verified functions | 381 |
| Codegen tests (naga-validated) | 20 |
| GPU cross-validation kernels | 4 |
| Proved kernel constructors | 6 |
| Foundational lemmas | 30+ |
| Architecture docs | 4 |
| Design decisions documented | 12 |
| Applications analyzed | 27 |
| Axioms in compute path | 0 |
