# Verified GPU Kernel Architecture: Gather → Compute → Scatter

## Overview

A verified foundation for dense data-parallel GPU compute kernels, built on CuTe layout algebra. Every kernel is `guard + scatter + compute` where all three are `ArithExpr` trees — the same verified arithmetic IR that already proves CuTe layout operations correct. Schedule transformations are separate, semantics-preserving rewrites proved in Verus.

All computation is over integers. "Float" operations use verified fixed-point arithmetic with proved error bounds — no f32, no GPU hardware intrinsic axioms, no floating-point verification complexity.

Inspired by: SPIRAL (gather/scatter), Halide/Exo (algorithm/schedule separation), ATL (verified tensor lowering), RISE/LIFT (verified rewrite rules), Exo-GPU (sequential-semantics-with-annotations).

## Architecture

```
                         VERIFIED (Verus)
┌──────────────────────────────────────────────────────────┐
│                                                          │
│  Mathematical Spec                                       │
│    gemm_contraction_value, scan_spec, attention_spec     │
│         ↕  correctness proof                             │
│  Kernel = (guard, scatter, compute)                      │
│    all ArithExpr — verified by arith_eval proofs         │
│         ↕  schedule transformation (proved)              │
│  Scheduled Kernel                                        │
│    still ArithExpr — schedule preserves semantics        │
│                                                          │
│  Fixed-point arithmetic (FixedPoint<N>)                  │
│    integer-backed, error bounds proved, no f32 needed    │
│                                                          │
└──────────────────────────────────────────────────────────┘
                         │
              AUDITABLE (~300 lines)
┌──────────────────────────────────────────────────────────┐
│  Kernel → WGSL text     (emit_kernel_wgsl)               │
│  Kernel → SPIR-V binary (emit_kernel_spirv)              │
│  Structural rendering only — no computational decisions   │
└──────────────────────────────────────────────────────────┘
                         │
              MACHINE-CHECKED
┌──────────────────────────────────────────────────────────┐
│  naga validates WGSL     spirv-val validates SPIR-V      │
└──────────────────────────────────────────────────────────┘
                         │
              TRUSTED (irreducible)
┌──────────────────────────────────────────────────────────┐
│  Verus + Z3  │  GPU driver  │  Silicon                   │
└──────────────────────────────────────────────────────────┘
```

**Key property: NO axioms in the compute path.** Unlike systems that axiomatize GPU intrinsics (exp, sqrt), we implement transcendentals as verified fixed-point polynomial approximations. The only trusted components are the proof checker, GPU driver, and silicon.

## ArithExpr

The existing verified ArithExpr (7 nodes, 1553 functions proved) is the foundation. New nodes are added incrementally as specific kernels demand them.

### Current (verified)

| Node | Spec | Proved by |
|------|------|-----------|
| `Const(c)` | `c` | trivial |
| `Var(i)` | `env[i]` | trivial |
| `Add(a, b)` | `eval(a) + eval(b)` | trivial |
| `Mul(a, b)` | `eval(a) * eval(b)` | trivial |
| `Div(a, b)` | `eval(a) / eval(b)` | trivial |
| `Mod(a, b)` | `eval(a) % eval(b)` | trivial |
| `Index(buf, ix)` | `arrays[buf][eval(ix)]` | trivial |

### Phase 1 additions (3 nodes)

| Node | Spec | Needed for |
|------|------|-----------|
| `Sub(a, b)` | `eval(a) - eval(b)` | Too common to encode as Add+Mul(-1) |
| `Reduce(Sum, var, bound, body)` | `Σ_{i=0}^{bound-1} eval(body, env[var:=i])` | GEMM, convolution, reduction, scan |
| `Cmp(op, a, b)` | `if a op b then 1 else 0` | Guards (Lt, Le, Gt, Ge, Eq, Ne) |

### Later additions (when specific kernels demand them)

| Node | Trigger | Needed for |
|------|---------|-----------|
| `Select(c, a, b)` | Softmax | Lazy conditional (emits structured `if`, not WGSL `select`) |
| `Let(var, rhs, body)` | Softmax | Avoids duplicating expensive sub-expressions |
| `Reduce(Max, ...)` / `Reduce(Min, ...)` | Softmax, SDF | Additional reduce ops |
| `Reduce(Monoid, ...)` | Flash attention, Welford | User-defined associative combine over tuples |
| `Tuple(vec)` / `Proj(e, i)` | Flash attention, argmax | Multi-value reductions |
| `BitXor/BitAnd/Shl/Shr` | Swizzle, radix sort | Bitwise index transforms |
| `Cast(e, ty)` | Mixed fixed-point precisions | Convert between bit widths |

Each addition is: define spec → prove properties → extend emitter → test. No big-bang redesign.

## Kernel

```rust
struct Kernel {
    /// Guard: thread i executes only if eval(guard, [i]) != 0.
    guard: ArithExpr,

    /// Scatter: maps thread id → output buffer index.
    /// Must be injective under guard (each thread writes unique location).
    scatter: ArithExpr,

    /// Compute: the value to store.
    compute: ArithExpr,

    /// Buffer bindings
    buffers: Vec<BufferBinding>,

    /// Workgroup size
    workgroup_size: (nat, nat, nat),
}
```

### Kernel semantics

```rust
spec fn kernel_eval(k: &Kernel, inputs: Seq<Seq<int>>, n_threads: nat) -> Seq<int> {
    // For each thread i in 0..n_threads where eval(guard, [i]) != 0:
    //   output[eval(scatter, [i])] = eval(compute, [i])
    // Scatter injective under guard → deterministic, order-independent.
}
```

Scatter injectivity makes `kernel_eval` deterministic — the result doesn't depend on thread execution order. This is the key correctness property. (ReduceStore with commutative monoids for histogram-like patterns can be added later when needed.)

### Well-formedness

```rust
spec fn well_formed(k: &Kernel, inputs, n_threads) -> bool {
    // scatter injective under guard
    // all Index reads in bounds under guard
    // no division/mod by zero under guard
    // scatter indices in bounds under guard
    // all intermediate values fit in machine integers
}
```

## Fixed-Point Arithmetic (replaces f32)

All "float" computation uses verified fixed-point with integer backing. This keeps the entire proof in integer arithmetic — no f32 types, no SMT float theories, no GPU intrinsic axioms.

### Design

```rust
/// Fixed-point number with N fractional bits.
/// Real value = raw / 2^N. Backed by i32 on GPU.
///
/// Example: N=12 → range ±1048576, precision ~0.000244
struct FixedPoint<const N: u32> { raw: i32 }

// In ArithExpr: fixed-point values are just integers.
// fp_mul(a, b, N) = Shr(Mul(a, b), Const(N))     — 1 ULP error, proved
// fp_div(a, b, N) = Div(Shl(a, Const(N)), b)      — 1 ULP error, proved
```

### Verified transcendentals (no axioms!)

Instead of `Intrinsic("exp", [x])` (axiomatized, trusted), implement as verified fixed-point polynomial approximations:

```rust
/// Fixed-point exp(x) via polynomial approximation.
/// Proved: |fp_exp(x) - exact_exp(x)| < error_bound(N)
pub proof fn lemma_fp_exp_correct(x: int, n: nat)
    requires /* x in valid range for N fractional bits */
    ensures
        abs(fp_exp_poly(x, n) - exact_exp_spec(x, n)) <= fp_exp_error_bound(n)
```

- `exp(x)` — Padé or minimax polynomial, ~6 terms for 12-bit precision
- `sqrt(x)` — Newton iteration with proved convergence
- `sin(x)/cos(x)` — Chebyshev polynomial
- `log(x)` — from exp inverse or direct polynomial

Each is a pure ArithExpr tree (Mul, Add, Shr for fixed-point) with a verified error bound. No axioms, no trusted hardware functions.

### Why this works

- **GEMM**: Pure integer arithmetic. No fixed-point needed.
- **Mandelbrot**: Already uses fixed-point (12-bit, working today in our codegen).
- **Softmax**: `exp(x)` via fixed-point polynomial. Error bound proved.
- **Attention**: Same as softmax — fixed-point exp with proved precision.
- **N-body/SPH**: `sqrt` via Newton iteration in fixed-point. Distance computations are integer-exact.
- **Raymarching SDF**: Fixed-point distance functions. `sqrt` for normalization.
- **Noise/terrain**: `sin/cos` via Chebyshev polynomials in fixed-point.

For applications that genuinely need IEEE f32 precision (ML training, scientific HPC), we can add f32 support later as a separate, clearly-axiomatized extension. But for rendering, simulation, and inference, fixed-point with proved error bounds is both sufficient and much more verifiable.

### Interval arithmetic for error propagation

```rust
/// Interval: [lo, hi] bounds the true value.
struct Interval { lo: int, hi: int }

/// Every fixed-point operation returns an interval.
/// fp_mul([a_lo, a_hi], [b_lo, b_hi], N) = [lo, hi] where
///   lo <= true_product <= hi, and hi - lo <= rounding_error
proof fn lemma_fp_mul_interval(a: Interval, b: Interval, n: nat)
    ensures /* output interval contains the true product */
```

This lets us prove end-to-end error bounds for entire kernels: "the GPU output differs from the mathematical result by at most ε."

## Kernel Examples

### Vector Add: `out[i] = a[i] + b[i]`

```rust
Kernel {
    guard:   Cmp(Lt, Var(0), Const(N)),
    scatter: Var(0),
    compute: Add(Index(0, Var(0)), Index(1, Var(0))),
}
```

### GEMM: `C[i,j] = Σ_k A[i*K+k] * B[k*N+j]`

```rust
Kernel {
    guard:   Mul(Cmp(Lt, Var(0), Const(M)), Cmp(Lt, Var(1), Const(N))),
    scatter: Add(Mul(Var(0), Const(N)), Var(1)),
    compute: Reduce(Sum, 2, Const(K),
        Mul(Index(0, Add(Mul(Var(0), Const(K)), Var(2))),
            Index(1, Add(Mul(Var(2), Const(N)), Var(1))))),
}
```

### Layout Offset: `out[x] = layout.offset(x)`

```rust
Kernel {
    guard:   Cmp(Lt, Var(0), Const(shape_size)),
    scatter: Var(0),
    compute: offset_expr(0, shape, stride),  // from verified CuTe
}
```

### Reduction: `out[0] = Σ_i input[i]`

```rust
Kernel {
    guard:   Cmp(Eq, Var(0), Const(0)),
    scatter: Const(0),
    compute: Reduce(Sum, 1, Const(N), Index(0, Var(1))),
}
// Efficient tree reduction = schedule transformation.
```

### Scan (prefix sum): `out[i] = Σ_{j≤i} input[j]`

```rust
Kernel {
    guard:   Cmp(Lt, Var(0), Const(N)),
    scatter: Var(0),
    compute: Reduce(Sum, 1, Add(Var(0), Const(1)), Index(0, Var(1))),
}
// Efficient Blelloch = algebraic refinement.
```

### Stencil (1D blur): `out[i] = Σ_d input[i+d-R] * weight[d]`

```rust
Kernel {
    guard:   Mul(Cmp(Lt, Const(R), Var(0)), Cmp(Lt, Var(0), Const(N-R))),
    scatter: Var(0),
    compute: Reduce(Sum, 1, Const(2*R+1),
        Mul(Index(0, Add(Var(0), Sub(Var(1), Const(R)))),
            Index(1, Var(1)))),
}
```

### Mandelbrot (one iteration step, fixed-point 20.12)

```rust
// Buffers: 0=z_re, 1=z_im, 2=c_re, 3=c_im, 4=escaped
Kernel {
    guard:   Mul(Cmp(Lt, Var(0), Const(N_PIXELS)),
                 Cmp(Eq, Index(4, Var(0)), Const(0))),
    scatter: Var(0),
    compute: Sub(Shr(Mul(Index(0, Var(0)), Index(0, Var(0))), Const(12)),  // re²
                 Shr(Mul(Index(1, Var(0)), Index(1, Var(0))), Const(12)),  // im²
                 Add(_, Index(2, Var(0)))),                                 // + c_re
}
// Host dispatches max_iter times. State lives in GPU buffers.
```

## CuTe Primitive Coverage

Every index function is built from verified CuTe primitives:

| Primitive | ArithExpr form | GPU use |
|-----------|---------------|---------|
| `delinearize_coord_expr` | `Mod(Div(Var(x), Const(pp)), Const(s))` | Thread → coordinate |
| `offset_expr` | Sum of `Mul(delinearize, stride)` | Coordinate → memory address |
| `compose` | Composition of two offset_exprs | Tiled layout indexing |
| `divide` | Split shape → (tile, rest) | Tile decomposition |
| `complement` | Stride-product complement | Remaining elements after tiling |
| `gemm_a/b_index_expr` | `Add(Mul(Var(i), Const(K)), Var(k))` | Matrix element access |
| `swizzle` | XOR-based index transform | Bank-conflict-free shared mem (needs BitXor, added later) |

All verified in Verus (1553 functions).

## Transformations (three families)

### A. Schedule transformations (same algorithm, different execution order)

Tiling, fusion, thread mapping, loop interchange, shared memory staging. Each is a Verus-proved rewrite: `kernel_eval(transformed) == kernel_eval(original)`. Tiling IS CuTe's `divide`. Thread mapping IS CuTe's TV decomposition.

### B. Algebraic refinements (use mathematical identities)

Reduction tiling (from monoid associativity), Blelloch scan (tree recursion), online softmax (from log-sum-exp identity), reassociation. Each proved via algebraic properties of the combining operation.

### C. Data-structure refinements (change representation)

SPH spatial hashing, sparse matrix formats (CSR/COO), compaction structures. These have different (harder) proof obligations — must show the refined representation preserves the relevant information.

## Scheduled Kernel (Phase 5+ — Exo-GPU-inspired)

For optimized kernels with shared memory and barriers, the spec Kernel is lowered to a **sequential loop nest with GPU annotations**. Key insight from Exo-GPU: parallelism and barriers are annotations on sequential code. `seq_eval` ignores them (= spec). `par_eval` respects them (= GPU execution). Two independent proof obligations.

```rust
enum ScheduledStmt {
    SeqLoop { var, bound, body },
    ParLoop { var, bound, body, mapping },  // sequential semantics = SeqLoop
    Store { buffer, index, value },
    Alloc { buffer, size, space },          // Global | Shared | Register
    Barrier,                                 // seq_eval ignores; par_eval synchronizes
}
```

**Barrier legality**: `if (!guard) { return; }` before a barrier is ILLEGAL (non-uniform control flow). Scheduled kernels predicate stores/loads instead of early-returning. The guard lowers to conditional execution, not control flow divergence.

## Pipeline (multi-kernel orchestration)

```rust
enum Pipeline {
    Dispatch(Kernel, GridSize),
    Seq(Vec<Pipeline>),
    Repeat { steps: nat, body: Box<Pipeline> },
    RepeatUntil { max_steps: nat, body: Box<Pipeline>, done: Kernel },
}
```

Covers: iterative simulations (Mandelbrot, physics), hierarchical reduction, multi-pass sort, SPH timestep. Each step is a verified Kernel; the pipeline composes them.

## Implementation Phases

### Phase 1: Reduce(Sum) + Kernel + GEMM proof + WGSL emission

**The minimal proof-of-concept.** Add 3 nodes to ArithExpr, define Kernel, prove GEMM correct, emit to WGSL, run on GPU.

1. Add `Sub`, `Reduce(Sum)`, `Cmp` to ArithExpr in Verus (~80 lines)
2. Extend `arith_eval` with specs, prove basic properties (~50 lines)
3. Define `Kernel` struct + `kernel_eval` spec (~30 lines)
4. Prove `gemm_kernel_eval == gemm_element_spec` (reuses existing lemmas) (~50 lines)
5. Prove `vector_add_kernel_eval` and `offset_kernel_eval` (~30 lines)
6. Extend WgslExpr emitter for new nodes + Kernel emission (~100 lines)
7. naga-validate, cross-validate on GPU (~50 lines tests)

**Estimated:** ~400 lines total. Ships a working verified GEMM kernel.

### Phase 2: Fixed-point + Mandelbrot

1. Define `FixedPoint<N>` operations as ArithExpr helpers (fp_mul = Shr(Mul, N))
2. Prove fp_mul error bound (~30 lines)
3. Mandelbrot kernel constructor using fixed-point (~40 lines)
4. Host-side iteration pipeline (~20 lines)

### Phase 3: Softmax / attention (triggers Let, Select, Reduce(Max))

When softmax demands it:
1. Add `Let`, `Select`, `Reduce(Max)` to ArithExpr
2. Prove softmax kernel correct
3. Extend emitter (Select → structured `if`, Let → ANF)

### Phase 4: Flash attention (triggers monoid generalization + Tuple)

When flash attention demands it:
1. Generalize `Reduce` to verified monoids
2. Add `Tuple`/`Proj` for multi-value reductions
3. Define flash attention summary monoid, prove associativity
4. Flash attention = tiled monoid reduction (generic theorem)

### Phase 5: Schedule transformations

1. Tiling (= CuTe divide), thread mapping (= CuTe TV decomposition)
2. Reduction tiling (monoid associativity)
3. Tiled GEMM as scheduled naive GEMM

### Phase 6: Shared memory + barriers (ScheduledKernel)

1. ScheduledStmt IR with Exo-GPU-inspired annotations
2. seq_eval = kernel_eval proof
3. Barrier legality (uniform control flow)
4. Add BitXor for swizzle
5. Bank-conflict-free tiled GEMM

### Phase 7: SPIR-V backend

Complete SPIR-V module emission targeting Vulkan via ash.

### Phase 8: Advanced kernels

- Blelloch scan (algebraic refinement of prefix sum spec)
- Radix sort (histogram + scan + scatter pipeline)
- SPH water sim (multi-kernel pipeline + spatial hash refinement)
- Raymarching SDF (iterative pipeline + fixed-point sqrt)

## Benchmark Kernels (design stress tests)

| Kernel | What it tests | Phase |
|--------|-------------|-------|
| Vector add | Basic map, injective scatter | 1 |
| GEMM | Reduce(Sum), verified index exprs | 1 |
| Layout offset | CuTe offset_expr integration | 1 |
| Mandelbrot (fixed-point) | FixedPoint, iterative pipeline | 2 |
| Softmax | Let, Select, Reduce(Max), shared subexpr | 3 |
| Flash attention | Monoid, Tuple, tiled reduction | 4 |
| Tiled GEMM | Schedule transformation, shared memory | 5-6 |
| Transpose + swizzle | BitXor, bank-conflict-free | 6 |
| Blelloch scan | Algebraic refinement, tree reduction | 8 |
| Histogram | ReduceStore (if added), atomics | 8+ |
| CSR SpMV | Indirect indexing, variable-length reduce | 8+ |
| SPH water | Data-structure refinement, multi-pipeline | 8+ |

## Scope

This architecture covers **dense data-parallel tensor kernels**: element-wise maps, reductions, scans, stencils, contractions (GEMM, convolution), ML inference (attention, softmax, normalization), iterative simulations (fractals, physics), and rendering (raymarching, terrain).

It does NOT (yet) cover: histogram with duplicate scatter, graph algorithms, dynamic work queues, tensor-core instructions, warp-level collectives. These can be added as extensions when needed.

## Trust Boundary

| Component | Verification |
|-----------|-------------|
| ArithExpr specs + proofs | Verus-proved |
| Kernel type + kernel_eval | Verus-proved |
| Kernel constructors | Verus-proved (ensures matches math spec) |
| Fixed-point operations + error bounds | Verus-proved |
| Fixed-point transcendentals (exp, sqrt, sin) | Verus-proved (polynomial approx with error bound) |
| Schedule/algebraic rewrites | Verus-proved (preserves kernel_eval) |
| CuTe layout algebra | Verus-proved (1553 functions) |
| WGSL emitter | Auditable (~200 lines) + naga-validated |
| SPIR-V emitter | Auditable (~300 lines) + spirv-val-validated |
| GPU driver + silicon | Trusted (irreducible) |
| Verus + Z3 | Trusted (proof checker) |

**NO axioms in the compute path.** Transcendentals are verified polynomial approximations, not axiomatized hardware intrinsics. The only trust is: proof checker + GPU correctly executes integer arithmetic + driver correctly dispatches shaders.

## Related Work

| System | Key idea we use | What they lack |
|--------|----------------|----------------|
| **SPIRAL** | Gather/scatter with composable index functions | No proof assistant |
| **Halide** | Algorithm/schedule separation | Schedule correctness is compiler-trusted |
| **Exo / Exo 2** | User-definable verified schedule rewrites | Effect system, not full proofs |
| **Exo-GPU** | Sequential-semantics-with-annotations, split verification | Abstract machine checking, not proof assistant |
| **ATL (PLDI '24)** | Verified tensor lowering (Coq), found truncation bug | No GPU backend, no schedules |
| **RISE/LIFT** | Verified rewrite rules for parallel patterns | No end-to-end GPU pipeline |
| **Futhark** | Segmented parallel patterns, automatic flattening | No formal verification |
| **CuTe/CUTLASS** | Layout algebra, thread-value decomposition | No formal verification |
| **Descend** | Ownership-based GPU race freedom | No tensor cores, limited scope |

We combine: CuTe's layout algebra (verified) + SPIRAL's gather/scatter + Halide's algorithm/schedule separation (with Verus proofs) + Exo-GPU's sequential-annotation model + ATL's verified lowering + fixed-point arithmetic (no f32 axioms).
