# Verified GPU Codegen Pipeline

## Goal

Build a **verified foundation for GPU compute kernels** — from tensor algebra (GEMM, convolution) to graphics (marching cubes, raymarching, water simulation). All index computation, data layout, and kernel logic are verified in Verus; only the proof checker, hardware axioms, GPU driver, and silicon are trusted.

## Architecture Overview

```
                    VERIFIED (in Verus)
┌─────────────────────────────────────────────────┐
│                                                 │
│  Mathematical Spec (contraction, SDF, PDE)      │
│       ↕ bridge lemma                            │
│  Exec Spec (element-level computation)          │
│       ↕ loop invariant proof                    │
│  Runtime Exec — value-correct                   │
│       ↕ verified arithmetic translator          │
│  ArithExpr IR — proven faithful to spec         │
│       ↕ verified emission                       │
│  SPIR-V / WGSL — semantics-preserving           │
│                                                 │
│  Kernel Logic (CTA coordination)                │
│  • Thread-to-element mapping (divide)           │
│  • Shared memory bounds (swizzle)               │
│  • Accumulation / iteration correctness         │
│  • Bank conflict freedom                        │
│                                                 │
└─────────────────────────────────────────────────┘
                         │
              ╔══════════╧══════════╗
              ║   TRUST BOUNDARY    ║
              ║                     ║
              ║  • Verus + Z3       ║
              ║  • GPU axioms       ║
              ║  • GPU driver       ║
              ║  • Silicon          ║
              ╚═════════════════════╝
```

---

## What Exists (verified, 1553 functions)

### Layout Algebra
- `compose_single` / `compose` — recursive composition with straddle handling
- `logical_divide` — tiled layout decomposition via complement
- `complement` — stride-product complement construction
- All with verified offset correctness (`compose(A,B).offset(x) == A.offset(B.offset(x))`)

### Column-Major Identity (no admissibility)
- `lemma_compose_column_major_identity` — `compose(cm_A, B).offset(x) == B.offset(x)`
- `lemma_divide_identity_column_major_no_admissibility` — `logical_divide.offset(x) == x`
- Works for any rank, any valid tile that divides the shape

### Row-Major GEMM
- Row-major A[M,K] = column-major (K,M):(1,K) via transposition
- `lemma_row_major_gemm_divide_identity` — divide identity for transposed layout

### Contraction Framework
- `gemm_contraction_value` / `matvec_contraction_value` / `dot_product_contraction_value`
- `gemm_element_spec` — concrete i64 spec for exec verification
- `lemma_gemm_element_spec_matches_contraction` — bridge from exec to abstract

### Value-Correct GEMM Exec
- `gemm_naive_exec` — ensures `result[i*n+j] == sum_k A[i*K+k] * B[k*N+j]`
- Overflow-safe via i128 intermediates with value bound
- Ghost snapshot for push-preservation of completed rows

### ArithExpr IR (verified arithmetic translator)
- `ArithExpr` enum: Const, Var, Add, Mul, Div, Mod, Index
- `arith_eval` / `arith_eval_with_arrays` — spec evaluation
- `delinearize_coord_expr` — builds expr for `(x / prefix_product) % shape[i]`
- `offset_expr` / `offset_expr_skip` — builds expr for layout offset
- **`lemma_delinearize_coord_expr_correct`** — ArithExpr matches delinearize (all ranks)
- **`lemma_offset_expr_correct`** — ArithExpr matches layout.offset (all ranks)
- **`lemma_gemm_mac_correct`** — A[i*K+k] * B[k*N+j] fully verified through ArithExpr
- Bridge lemmas: `shape_prefix_product ↔ shape_size ↔ shape_prefix_products ↔ column_major_strides`
- `RuntimeArithExpr` — exec type with `view_spec()` mapping to spec ArithExpr
- `runtime_arith_eval` — verified exec evaluator (`result as int == arith_eval(expr.view_spec(), env)`)
- `arith_eval_fits_i64` — overflow-safety predicate (Div/Mod require non-negative for GPU truncating semantics)

### Bank Conflict Analysis
- `lemma_sm80_smem_bank_conflict_free` — swizzled SMEM is bank-conflict-free

### Supporting Infrastructure
- `lemma_sorted_tractable_mode_bound` — general per-mode stride bound
- `lemma_complement_sorted_tractable` — complement inherits sorted+tractable
- `lemma_cm_sorted_tractable` / `lemma_cm_divide_admissible` — general-rank column-major
- `lemma_shape_divisibility` — product of divisors divides product
- Concrete spec validation properties (offset identity, size preservation, etc.)

### Runtime Exec Functions
- `compose_single_exec` / `compose_exec` — iterative, zero intermediate allocations
- `complement_exec`, `logical_product_exec`, `coalesce_exec`, etc.
- All with `wf_spec()` ensuring ghost model matches concrete Vecs

---

## Phase 1: Verified Codegen (ArithExpr → WGSL/SPIR-V)

**Status: ArithExpr IR complete, emission TODO**

### What's done
- `ArithExpr` type with full correctness proofs
- `RuntimeArithExpr` exec type with verified evaluator
- Proof that ArithExpr faithfully represents all CuTe index computations
- GEMM MAC expression correctness

### What's needed
Prove that the generated WGSL/SPIR-V computes the same arithmetic as the Verus spec.

#### WGSL emission
```rust
// Exec function: emit ArithExpr as WGSL string
fn arith_to_wgsl(expr: &RuntimeArithExpr) -> String
    ensures /* output parses to equivalent computation */;
```

The ArithExpr → WGSL mapping is direct:
- `Const(c)` → `"42"` (integer literal)
- `Var(i)` → variable name from environment
- `Add(a, b)` → `"(a + b)"`
- `Mul(a, b)` → `"(a * b)"`
- `Div(a, b)` → `"(a / b)"`
- `Mod(a, b)` → `"(a % b)"`
- `Index(arr, idx)` → `"arr[idx]"`

#### SPIR-V emission
Direct binary emission (skips naga from trust boundary):
- `ArithExpr::Add` → `OpIAdd`
- `ArithExpr::Mul` → `OpIMul`
- `ArithExpr::Div` → `OpSDiv`
- `ArithExpr::Mod` → `OpSMod`
- `ArithExpr::Index` → `OpAccessChain` + `OpLoad`

#### Correctness theorem
The core property: emitted code computes what `arith_eval` says.

For WGSL, this is proved by structural induction on ArithExpr — each node emits a WGSL expression whose evaluation matches `arith_eval`. Since WGSL integer arithmetic has the same semantics as our non-negative ArithExpr (truncating div/mod), the proof is straightforward.

For SPIR-V, same approach: each ArithExpr node maps to specific SPIR-V ops whose semantics match.

### Files
- `verus-cutedsl-codegen/src/wgsl_emit.rs` — verified WGSL string emission
- `verus-cutedsl-codegen/src/spirv_emit.rs` — verified SPIR-V binary emission
- `verus-cutedsl-codegen/src/lib.rs` — `#[kernel]` attribute macro

---

## Phase 2: GPU Intrinsics & Memory Model

### The irreducible axioms

```rust
/// Read a value from GPU global memory.
#[verifier::external_body]
fn gpu_read(buffer: &GpuBuffer, offset: u64) -> (val: i64)
    requires offset < buffer@.len(),
    ensures val == buffer@[offset as int];

/// Write a value to GPU global memory.
#[verifier::external_body]
fn gpu_write(buffer: &mut GpuBuffer, offset: u64, val: i64)
    requires offset < buffer@.len(),
    ensures buffer@[offset as int] == val,
            forall|j: int| j != offset as int && 0 <= j < buffer@.len() ==>
                buffer@[j] == old(buffer)@[j];

/// Workgroup barrier: all threads' prior memory ops complete before any proceeds.
#[verifier::external_body]
fn gpu_barrier(smem: &SharedMem)
    ensures /* all threads' shared memory writes are visible */;
```

### Shared memory model
```rust
spec struct SharedMemModel {
    data: Seq<i64>,
    // Per-thread write history for race detection
}
// Race freedom from divide bijectivity (already proved)
```

### Thread execution model
```rust
spec struct ThreadContext {
    global_id: (nat, nat, nat),
    local_id: (nat, nat, nat),
    workgroup_id: (nat, nat, nat),
    workgroup_size: (nat, nat, nat),
}
```

---

## Phase 3: Verified CTA Kernel (GEMM)

### Goal
Write a verified GEMM kernel proving each CTA computes the correct output tile.

### Key proofs (mostly exist!)

| Property | Status | Lemma |
|----------|--------|-------|
| Thread-to-element bijection | Done | `lemma_divide_identity_column_major_no_admissibility` |
| Bank conflict freedom | Done | `lemma_sm80_smem_bank_conflict_free` |
| Accumulation = contraction | Done | `lemma_gemm_accumulation_correct` |
| Output shape correct | Done | `lemma_gemm_contraction_matches_spec` |
| Shared memory bounds | Done | `lemma_sorted_tractable_mode_bound` |
| Global memory bounds | Partial | Need predication proof for boundary tiles |
| Value correctness | Done | `gemm_naive_exec` value correctness |

---

## Phase 4: WGSL/SPIR-V Backend

The `#[kernel]` proc macro:
1. Parses the verified Verus kernel function
2. Strips proof blocks, ghost code, requires/ensures
3. Lowers CuTe operations to `ArithExpr` (Phase 1)
4. Emits WGSL/SPIR-V via verified emission
5. Generates `const KERNEL_WGSL: &str` or SPIR-V bytes

---

## Phase 5: Runtime Integration

### Vulkan path (via verus-vulkan)
`verus-vulkan` already has buffer management, descriptor sets, command buffers, compute pipelines, queue submission. Remaining: shader module creation, dispatch dimensions, buffer readback.

### WebGPU path
Thin `wgpu` wrapper: device setup, buffer management, compute pipeline from WGSL, dispatch + readback.

### Validation harness
Cross-validate CPU (verified `gemm_naive_exec`) against GPU output for random inputs.

---

## Beyond GEMM: General Verified GPU Kernels

The infrastructure above (ArithExpr IR, verified emission, GPU intrinsics, CTA coordination) is **reusable for all kernel types**. Below is the roadmap for extending to general GPU compute.

### Kernel Difficulty Spectrum

| Kernel | Category | Key Challenge | FP Needed? |
|--------|----------|---------------|------------|
| Mandelbrot / Julia set | Fractal | Iteration count, escape radius | No (fixed-point works) |
| Parallel reduction / scan | Data-parallel | Tree-structured accumulation | No |
| Radix sort | Data-parallel | Permutation correctness | No |
| Raymarching SDF | Graphics | Sphere-trace convergence | Yes (or fixed-point) |
| Marching cubes | Graphics | Topological correctness (manifold mesh) | Partial |
| Convolution / pooling | ML | Sliding window bounds | No |
| Water simulation (SPH) | Physics | PDE discretization, stability (CFL) | Yes |
| Cloth simulation | Physics | Constraint solving, convergence | Yes |

### What each kernel type needs

#### Integer-only kernels (no FP gap)

**Fractal renderers (Mandelbrot, Julia):**
- Spec: `mandelbrot_escape(c_re, c_im, max_iter) -> nat` — pure integer iteration
- ArithExpr: pixel-to-complex mapping (fixed-point), iteration loop, escape check
- Proof: iteration terminates, escape radius correct, pixel mapping bijective
- New infrastructure: fixed-point arithmetic type, iteration loop ArithExpr
- **Path from current state:** Extend ArithExpr with loop/conditional nodes, add `FixedPoint<N>` verified type

**Parallel reduction / prefix sum:**
- Spec: `reduce(data, op) == fold(data, op, identity)`
- ArithExpr: tree-structured index computation
- Proof: each level halves the problem, final value is the fold
- New infrastructure: verified tree-reduction pattern
- **Path from current state:** Already have `scan` infrastructure in verus-cutedsl; extend to GPU dispatch

**Radix sort:**
- Spec: `output == permutation(input) && is_sorted(output)`
- ArithExpr: histogram, scatter indices
- Proof: permutation preservation (each element appears exactly once), sortedness
- New infrastructure: histogram correctness, scatter bijectivity
- **Path from current state:** Already have `radix_sort` in verus-cutedsl; extend to GPU

#### Kernels needing fixed-point arithmetic

**Raymarching SDF:**
- Spec: `sdf(point) -> distance` — signed distance function
- ArithExpr: ray origin + t*direction, SDF evaluation, sphere-trace step
- Proof: sphere-tracing converges (distance decreases by SDF value each step), intersection within epsilon
- New infrastructure: `FixedPoint<N>`, verified SDF primitives (sphere, box, torus), CSG operations
- **Path:** FixedPoint type + SDF library + convergence proof

**Marching cubes:**
- Spec: isosurface extraction is topologically correct
- ArithExpr: 3D grid indexing (layout algebra handles this), lookup table, vertex interpolation
- Proof: 256-entry lookup table verified by `by(compute_only)`, each cube produces valid mesh patch, output mesh is manifold
- New infrastructure: mesh data structure spec, manifold predicate, lookup table verification
- **Path:** Lookup table verification (finite case analysis) + grid indexing (existing layout algebra) + manifold proof

#### Kernels needing floating-point verification

**Water simulation (Eulerian / SPH):**
- Spec: Navier-Stokes discretization, conservation laws
- Proof: CFL stability condition, mass/momentum conservation, divergence-free velocity
- New infrastructure: verified PDE discretization, FP interval arithmetic, stability proofs
- **Path:** This is the hardest target. Requires either (a) verified interval FP arithmetic or (b) fixed-point with proven error bounds

**Cloth simulation:**
- Spec: constraint satisfaction (distance, bending, collision)
- Proof: Gauss-Seidel / PBD convergence, energy dissipation
- New infrastructure: constraint solver verification, FP convergence bounds

### Key Infrastructure Gaps

#### 1. Control flow in ArithExpr
Current ArithExpr is expression-only (no loops, no conditionals). Need:
```rust
// Proposed extensions
ArithExpr::IfThenElse(Box<ArithExpr>, Box<ArithExpr>, Box<ArithExpr>),
ArithExpr::Loop { init: Box<ArithExpr>, cond: Box<ArithExpr>,
                  body: Box<ArithExpr>, max_iter: nat },
```
- `IfThenElse` maps to WGSL `select()` or ternary
- `Loop` maps to WGSL `for` loop with bounded iteration
- Correctness: `arith_eval` extended with loop semantics, termination from `max_iter` bound

#### 2. Verified fixed-point arithmetic
```rust
/// Fixed-point number with N fractional bits.
/// Backed by i64: value = raw / 2^N.
struct FixedPoint<const N: u32> { raw: i64 }

spec fn fp_value<const N: u32>(fp: FixedPoint<N>) -> int {
    fp.raw as int  // exact integer representation; real value = raw / 2^N
}

// Verified operations with proven error bounds:
fn fp_add(a: FixedPoint<N>, b: FixedPoint<N>) -> FixedPoint<N>
    ensures fp_value(result) == fp_value(a) + fp_value(b);  // exact

fn fp_mul(a: FixedPoint<N>, b: FixedPoint<N>) -> FixedPoint<N>
    ensures |fp_value(result) - fp_value(a) * fp_value(b) / 2^N| <= 1;  // 1-ULP error
```
This sidesteps the FP verification problem entirely — all proofs use exact integer arithmetic on the `raw` field, with known precision loss from rounding.

#### 3. Vector/matrix types
GPU kernels operate on vec2/vec3/vec4 and mat2/mat3/mat4. Need:
```rust
spec struct Vec3 { x: int, y: int, z: int }
fn vec3_dot(a: Vec3, b: Vec3) -> int
    ensures result == a.x * b.x + a.y * b.y + a.z * b.z;
```
These are straightforward to verify — just named tuples with arithmetic.

#### 4. SDF primitives library
For raymarching kernels:
```rust
spec fn sdf_sphere(p: Vec3, center: Vec3, radius: int) -> int;
spec fn sdf_box(p: Vec3, half_extents: Vec3) -> int;
spec fn sdf_union(d1: int, d2: int) -> int { min(d1, d2) }
spec fn sdf_intersect(d1: int, d2: int) -> int { max(d1, d2) }
spec fn sdf_subtract(d1: int, d2: int) -> int { max(d1, -d2) }

// Key property: Lipschitz-1 (|sdf(a) - sdf(b)| <= |a - b|)
proof fn lemma_sphere_lipschitz(p1: Vec3, p2: Vec3, center: Vec3, r: int)
    ensures |sdf_sphere(p1, center, r) - sdf_sphere(p2, center, r)| <= vec3_dist(p1, p2);
```
The Lipschitz property guarantees sphere-tracing convergence.

---

## Suggested Build Order

```
Phase 1: Codegen (ArithExpr → WGSL)                    ← CURRENT FOCUS
    │
    ├── Phase 1a: WGSL string emission + correctness proof
    ├── Phase 1b: SPIR-V binary emission
    └── Phase 1c: #[kernel] proc macro
    │
Phase 2: GPU intrinsics + memory model                  ← parallel with Phase 1
    │
Phase 3: First verified kernel (GEMM)                   ← depends on 1 + 2
    │
Phase 4: FixedPoint<N> type + arithmetic                ← independent
    │
Phase 5: ArithExpr extensions (IfThenElse, Loop)        ← independent
    │
Phase 6: Verified Mandelbrot renderer                   ← depends on 1 + 2 + 4 + 5
    │   (first complete verified GPU kernel!)
    │
Phase 7: SDF primitives + raymarching                   ← depends on 4 + 5
    │
Phase 8: Marching cubes                                 ← depends on 1 + 2 + vec3
    │
Phase 9: Water simulation                               ← depends on all above
```

### Milestone targets

1. **First shader**: ArithExpr → WGSL that actually runs on GPU (Phase 1)
2. **First verified kernel**: GEMM with end-to-end proof chain (Phase 3)
3. **First graphics kernel**: Mandelbrot fixed-point renderer (Phase 6)
4. **First 3D kernel**: Raymarching SDF with convergence proof (Phase 7)
5. **First mesh kernel**: Marching cubes with manifold proof (Phase 8)
6. **First physics kernel**: Water sim with stability proof (Phase 9)

---

## Trust Boundary Summary

| Component | Status | Trust Level |
|-----------|--------|-------------|
| Layout algebra (compose, divide, complement) | Verified (1553 fns) | None |
| ArithExpr IR + correctness proofs | Verified | None |
| ArithExpr exec evaluator | Verified | None |
| GEMM value correctness | Verified | None |
| Bank conflict freedom | Verified | None |
| ArithExpr → WGSL/SPIR-V emission | **Phase 1 (next)** | None (once proved) |
| CTA kernel coordination | Phase 3 | None (once proved) |
| FixedPoint arithmetic | Phase 4 | None (once proved) |
| gpu_read / gpu_write / gpu_barrier | Axioms (Phase 2) | **Axioms** |
| SPIR-V → GPU machine code | Driver | **Trusted** |
| GPU hardware | Silicon | **Trusted** |
| Verus + Z3 | Proof checker | **Trusted** |

**Irreducible trust: proof checker + GPU axioms + driver + silicon.**

---

## What Makes This Tractable

1. **Narrow arithmetic subset**: GPU compute shaders use only integer arithmetic, array indexing, and bounded loops. No pointers, no dynamic dispatch, no heap allocation.

2. **Building blocks exist**: The hard proofs (compose identity, divide correctness, accumulation, bank conflicts) are done. ArithExpr correctness is done.

3. **Fixed-point sidesteps FP**: By using `FixedPoint<N>` backed by integers, all proofs remain in exact integer arithmetic. Known precision loss is bounded, not unbounded.

4. **Simple trust boundary**: A handful of GPU memory axioms. Everything else is verified.

5. **Incremental validation**: Cross-validation (CPU vs GPU) catches trust boundary bugs immediately.

6. **Reusable infrastructure**: Each new kernel type reuses the same ArithExpr IR, emission pipeline, and GPU intrinsics. The per-kernel work is just the domain-specific spec + proof.
