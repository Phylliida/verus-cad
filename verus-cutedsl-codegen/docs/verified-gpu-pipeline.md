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
//  Exec function: emit ArithExpr as WGSL string
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
///  Read a value from GPU global memory.
#[verifier::external_body]
fn gpu_read(buffer: &GpuBuffer, offset: u64) -> (val: i64)
    requires offset < buffer@.len(),
    ensures val == buffer@[offset as int];

///  Write a value to GPU global memory.
#[verifier::external_body]
fn gpu_write(buffer: &mut GpuBuffer, offset: u64, val: i64)
    requires offset < buffer@.len(),
    ensures buffer@[offset as int] == val,
            forall|j: int| j != offset as int && 0 <= j < buffer@.len() ==>
                buffer@[j] == old(buffer)@[j];

///  Workgroup barrier: all threads' prior memory ops complete before any proceeds.
#[verifier::external_body]
fn gpu_barrier(smem: &SharedMem)
    ensures /* all threads' shared memory writes are visible */;
```

### Shared memory model
```rust
spec struct SharedMemModel {
    data: Seq<i64>,
    //  Per-thread write history for race detection
}
//  Race freedom from divide bijectivity (already proved)
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

### Key Infrastructure: Stage-Based Kernel Composition

#### The Problem

`ArithExpr` + `KernelSpec` model a **single parallel map** — one pass where each thread
computes one output. Real GPU kernels are multi-phase: load data, barrier, compute, barrier,
scan, barrier, scatter. Production kernels (Flash Attention, tiled GEMM, Mandelbrot with
work compaction) need **temporal composition** of parallel phases within a single dispatch.

The original plan proposed extending ArithExpr with `IfThenElse` and `Loop` nodes. After
extensive literature review (see citations below), we determined a better approach:
**don't extend ArithExpr — compose KernelSpecs with explicit barriers.**

#### The Abstraction: Hoare Logic over Parallel Primitives

The `Stage` type models a GPU kernel as a tree of barrier-separated parallel operations.
This is **phase-based verification** — a well-established paradigm in GPU verification
research (see Literature section below).

```rust
///  A predicate on shared state at a barrier point.
pub struct StatePredicate {
    pub pred: spec_fn(SharedState) -> bool,
}

///  Shared state model: named buffers of integers.
pub struct SharedState {
    pub buffers: Seq<Seq<int>>,
    pub workgroup_size: nat,
}

///  Barrier scope — workgroup-level by default.
pub enum BarrierScope {
    Workgroup,   //  __syncthreads() / workgroupBarrier() — cheap, ~20 cycles
    Grid,        //  cooperative groups grid_group::sync() — rare, expensive
}

///  A GPU kernel as a tree of composable stages.
pub enum Stage {
    ///  Parallel map: each thread computes outputs (existing KernelSpec).
    ///  No barrier before or after — fuses with adjacent Maps.
    Map(KernelSpec),

    ///  Parallel prefix sum on a buffer (existing verified scan specs).
    Scan { buffer: nat, op: ScanOp },

    ///  Explicit barrier with invariant. Only sync point in the model.
    ///  Developer places these where cross-thread communication occurs.
    Barrier { scope: BarrierScope, post: StatePredicate },

    ///  Sequential composition — NO implicit barriers between stages.
    ///  Adjacent Maps without a Barrier between them are fused.
    Seq(Seq<Stage>),

    ///  Bounded loop with inductive invariant (checked at Barriers inside body).
    Loop { bound: ArithExpr, body: Box<Stage>, invariant: StatePredicate },
}
```

#### Design Principles

1. **Barriers are explicit, not implicit.** The developer places `Barrier` stages where
   cross-thread synchronization is needed. Adjacent `Map` stages without a `Barrier` between
   them fuse — data flows thread-locally with no sync overhead.

2. **Barriers are workgroup-scoped by default.** `Workgroup` barriers map to
   `__syncthreads()` / `workgroupBarrier()` and are cheap. `Grid` barriers (cooperative
   groups) are expensive and rarely needed. Cross-workgroup communication normally happens
   through global memory between separate dispatches.

3. **Verification is compositional.** Each barrier interval (code between two `Barrier`
   stages) is verified independently:
   - **Race-freedom**: no two threads write the same location; no thread reads what another
     writes. This follows from `KernelSpec`'s scatter injectivity (already proved).
   - **Barrier invariants**: the `StatePredicate` holds at each barrier point. This is
     standard Hoare logic — {pre} stage {post} — where barriers are the assertion points.
   - **Loop invariants**: inductive over iterations, checked at barriers inside the body.

4. **The abstraction is extensible.** New `Stage` variants can be added without breaking
   existing proofs:

   | Future need | Add variant | When |
   |---|---|---|
   | Pipeline verification | `Pipeline { stages, depth }` | Prove sequential ≡ pipelined |
   | Data-dependent early exit | `LoopWhile { body, cond, max }` | Break when active set empty |
   | Conditional stages | `Cond { pred, then, else }` | Adaptive algorithms |
   | Warp specialization | Already works | `Map` guard branches on warp ID |
   | Async copy | Model as sequential Map | Codegen overlaps; spec is sequential |

   **Note on Loop bounds:** `Loop.bound` is an `ArithExpr` evaluated once before the loop
   starts — no data-dependent early exit. If all Mandelbrot pixels escape at epoch 50 of
   100, epochs 51-100 still execute as no-ops (Map guard filters inactive threads, Scan on
   empty set is identity). Correct but not optimal. `LoopWhile` can be added later without
   breaking existing proofs.

#### Kernel Examples

**Mandelbrot with work compaction** (3 barriers per epoch, not 6):
```
Loop(max_epochs, Seq([
    Map(mandelbrot_step),    //  thread-local, no barrier
    Map(escape_check),       //  thread-local, no barrier
    Barrier(Workgroup, "escape flags written to shared memory"),
    Scan(compact),           //  reads all threads' flags — needs prior barrier
    Barrier(Workgroup, "scan results visible"),
    Map(scatter),            //  reads scan output — needs prior barrier
    Barrier(Workgroup, "compaction done, active set updated"),
]), inv: "active ∪ escaped = all pixels")
```

**Flash Attention** (developer controls double-buffering):
```
Seq([
    Map(load_Q),
    Barrier(Workgroup, "Q in shared memory"),
    Loop(num_kv_blocks, Seq([
        Map(async_load_K_next),      //  start loading NEXT tile
        Map(compute_on_current_K),   //  compute on CURRENT — no barrier needed
        Barrier(Workgroup, "next tile load complete"),
        Map(swap_buffers),           //  no barrier after — thread-local
    ]), inv: "O_partial / l = correct attention through block k"),
    Map(normalize_store),
])
```

**Water simulation (SPH):**
```
Loop(timesteps, Seq([
    Map(hash_particles),
    Barrier(Workgroup, "grid built"),
    Scan(sort_by_cell),
    Barrier(Workgroup, "sorted"),
    Map(compute_density),        //  reads neighbors — needs prior barrier
    Barrier(Workgroup, "densities ready"),
    Map(compute_forces),         //  reads neighbor densities
    Map(integrate),              //  thread-local — no barrier needed
]), inv: "CFL holds ∧ conservation laws")
```

**Tiled GEMM:**
```
Seq([
    Loop(k_tiles, Seq([
        Map(load_A_B_to_shared),
        Barrier(Workgroup, "tiles in shared memory"),
        Map(accumulate_C_tile),
    ]), inv: "C_partial = sum of first k tile products"),
    Map(store_epilogue),
])
```

#### Verification Obligations

For a `Stage` tree, the verifier checks:

1. **Per barrier-interval race-freedom:** Between consecutive `Barrier` stages, the `Map`
   operations have injective scatter indices (already proved by `KernelSpec`). No two threads
   touch the same shared memory location without an intervening barrier.

2. **Barrier invariant validity:** Each `Barrier`'s `StatePredicate` follows from the
   prior barrier's predicate + the intervening `Map`/`Scan` operations' postconditions.

3. **Loop invariant inductiveness:** The `invariant` holds initially and is preserved by
   each iteration of the loop body (checked at `Barrier` stages within the body).

4. **Scan correctness:** `Scan` stages use existing verified scan proofs (Hillis-Steele,
   Blelloch, Brent-Kung). The scan's postcondition is established by the scan lemmas.

5. **Top-level correctness:** The final shared state satisfies the kernel's functional
   specification (e.g., `output[pixel] == escape_time(c[pixel], max_iter)`).

#### Codegen

The `Stage` tree maps mechanically to WGSL/SPIR-V:
- `Map(spec)` → parallel for-each (existing ArithExpr → WGSL emission)
- `Scan { buffer, op }` → Hillis-Steele in shared memory (fixed template)
- `Barrier(Workgroup, _)` → `workgroupBarrier()`
- `Barrier(Grid, _)` → cooperative groups `grid_sync()` (requires special launch)
- `Seq(stages)` → concatenate generated code
- `Loop { bound, body, _ }` → `for (var i = 0u; i < bound; i++) { body }`

The trust boundary is the same as for ArithExpr → WGSL: structural correspondence
between spec-level `Stage` and generated code. Each variant has a fixed, auditable
template.

#### Literature & Citations

This design follows the **barrier-interval / phase-based verification** paradigm,
which is the dominant approach in GPU kernel verification since 2012:

**Foundational:**
- Betts, Chong, Donaldson, Qadeer, Thomson. "GPUVerify: A Verifier for GPU Kernels."
  OOPSLA 2012. (SIGPLAN Most Influential Paper 2022.)
  Divides execution into barrier intervals, verifies race-freedom per-interval via
  two-thread reduction. Barriers are explicit, developer-placed.

- Chong, Donaldson, Kelly, Ketema, Qadeer. "Barrier Invariants: A Shared State
  Abstraction for the Analysis of Data-Dependent GPU Kernels." OOPSLA 2013.
  Adds Hoare-style predicates at barrier points for compositional functional correctness.
  Directly validates our "StatePredicate at each Barrier" approach.

**Hoare Logic for GPU:**
- Kojima, Igarashi. "A Hoare Logic for GPU Kernels." ACM TOCL 2017.
  Full Hoare logic for SIMT programs with explicit barrier rule. Proved sound and
  relatively complete. Most direct precedent for our proof methodology.

- Kojima, Igarashi. "A Hoare Logic for SIMT Programs." APLAS 2013.
  Earlier conference version with automated verification condition generation.

**Compositional Analysis:**
- Cogumbreiro et al. "Checking Data-Race Freedom of GPU Kernels, Compositionally."
  CAV 2021. "Memory Access Protocols." FMSD 2023.
  Treats barrier intervals as independent "protocols" — linear scaling vs exponential.
  Verified 1.42x more real kernels than competitors. Validates our per-interval
  independence property.

**Separation Logic:**
- Blom, Huisman, Mihelcic. "Specification and Verification of GPGPU Programs" (VerCors).
  Permission-based separation logic with barrier pre/postconditions. Covers race-freedom
  AND functional correctness for OpenCL kernels.

- Hobor, Gherghina. "Barriers in Concurrent Separation Logic." ESOP 2011, LMCS 2012.
  CSL for barriers with simultaneous resource redistribution. Machine-checked in Coq.

**Type-System Approaches:**
- Steffen, Giarrusso, Rompf. "Descend: A Safe GPU Systems Programming Language."
  PLDI 2024. Rust-style borrow checker enforces correct barrier placement statically.

**Automatic Barrier Placement:**
- Anand, Polikarpova. "Automatic Synchronization for GPU Kernels (AUTOSYNC)." FMCAD 2018.
  Synthesizes optimal barrier placement via MaxSAT, using GPUVerify as oracle.

**Production Systems:**
- NVIDIA CUTLASS 3.x `sm90_pipeline.hpp` — Producer-consumer pipeline with paired
  barriers per stage, circular buffer phase tracking, thread role categorization.
  Closest production model to our Stage abstraction.

- OpenAI Triton — Block-level programming where barriers are compiler-managed.
  Persistent kernel support with explicit multi-phase loops.

- Hou, Zhou, Guo. "BSGP: Bulk-Synchronous GPU Programming." SIGGRAPH 2008.
  BSP model for GPU with explicit developer-placed barriers.

**Our contribution relative to the literature:** Existing work reasons at the
**thread level** (GPUVerify, Kojima-Igarashi, VerCors) or makes barriers
**compiler-implicit** (Futhark, Halide). Our model reasons at the **collective
operation level** — `Map` and `Scan` are atomic proof-level statements whose
internal thread-level correctness is established separately (KernelSpec scatter
injectivity, scan algorithm proofs). This gives a higher-level, more compositional
proof structure while reusing the existing verified CuTe layout algebra for the
spatial correctness within each stage.

#### Estimated Implementation

| New piece | Lines | Difficulty |
|---|---|---|
| `Stage` enum + `SharedState` + `StatePredicate` types | ~65 | Trivial |
| `staged_eval` spec (sequential composition semantics) | ~80 | Medium |
| Race-freedom checker (scatter injectivity between barriers) | ~50 | Easy (reuses KernelSpec proofs) |
| Per-kernel composition proofs (Mandelbrot, GEMM, etc.) | ~100 each | Medium |
| Codegen: `Stage` → WGSL with barriers | ~150 | Trust boundary |
| **Total framework** | **~345** | |

#### 2. Verified fixed-point arithmetic

`verus-fixed-point` already provides multi-limb fixed-point with verified arithmetic
(275 functions), NTT-based multiplication, and Karatsuba proofs. For GPU use:

- **N ≤ 8 limbs:** Karatsuba unrolled as ArithExpr (per-thread, no shared memory)
- **N ≥ 16 limbs:** Batch NTT via multi-stage KernelSpecs (butterfly passes as Map stages,
  barriers between passes, reusing `ntt_butterfly_exec` proofs from verus-fixed-point)
- Both approaches compose with the Stage model — the NTT butterfly passes are just
  `Seq([Map(butterfly_pass_1), Barrier, Map(butterfly_pass_2), Barrier, ...])`

#### 3. Vector/matrix types
GPU kernels operate on vec2/vec3/vec4 and mat2/mat3/mat4. Need:
```rust
spec struct Vec3 { x: int, y: int, z: int }
fn vec3_dot(a: Vec3, b: Vec3) -> int
    ensures result == a.x * b.x + a.y * b.y + a.z * b.z;
```
These are straightforward to verify — just named tuples with arithmetic.
`verus-linalg` already has generic `Vec2<T>`, `Vec3<T>`, `Mat3<T>` over any Ring.

#### 4. SDF primitives library
For raymarching kernels:
```rust
spec fn sdf_sphere(p: Vec3, center: Vec3, radius: int) -> int;
spec fn sdf_box(p: Vec3, half_extents: Vec3) -> int;
spec fn sdf_union(d1: int, d2: int) -> int { min(d1, d2) }
spec fn sdf_intersect(d1: int, d2: int) -> int { max(d1, d2) }
spec fn sdf_subtract(d1: int, d2: int) -> int { max(d1, -d2) }

//  Key property: Lipschitz-1 (|sdf(a) - sdf(b)| <= |a - b|)
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
Phase 2: Stage framework (Stage, Barrier, staged_eval)  ← parallel with Phase 1
    │   ~345 lines. Compositional kernel model with
    │   explicit barriers + Hoare-style invariants.
    │   No GPU axioms needed — pure spec-level model.
    │
Phase 3: First verified kernel (tiled GEMM)             ← depends on 1 + 2
    │   Stage tree: Loop(k_tiles, [Map(load), Barrier, Map(accumulate)])
    │
Phase 4: FixedPoint on GPU (Karatsuba + batch NTT)      ← independent
    │   Karatsuba unrolled as ArithExpr for N≤8.
    │   Batch NTT as Stage pipeline for N≥16.
    │
Phase 5: Verified Mandelbrot renderer                   ← depends on 1 + 2 + 4
    │   Stage tree: Loop(epochs, [Map(step), Barrier,
    │   Scan(compact), Barrier, Map(scatter), Barrier])
    │   First kernel with dynamic work redistribution!
    │
Phase 6: Verified Flash Attention                       ← depends on 1 + 2 + 3
    │   Stage tree: [Map(load_Q), Barrier, Loop(kv_blocks,
    │   [Map(load_K), Map(compute), Barrier, Map(swap)])]
    │   Developer-controlled double buffering.
    │
Phase 7: SDF primitives + raymarching                   ← depends on 4
    │
Phase 8: Marching cubes                                 ← depends on 1 + 2 + vec3
    │
Phase 9: Water simulation (SPH)                         ← depends on 1 + 2
    │   Stage tree: Loop(timesteps, [Map(hash), Barrier,
    │   Scan(sort), Barrier, Map(density), Barrier,
    │   Map(forces), Map(integrate)])
```

### Milestone targets

1. **First shader**: ArithExpr → WGSL that actually runs on GPU (Phase 1)
2. **Stage framework**: Stage type + staged_eval + race-freedom checker (Phase 2)
3. **First verified multi-stage kernel**: tiled GEMM (Phase 3)
4. **First kernel with work compaction**: Mandelbrot renderer (Phase 5)
5. **First ML kernel**: Flash Attention with verified online softmax (Phase 6)
6. **First physics kernel**: Water sim with CFL stability proof (Phase 9)

---

## Trust Boundary Summary

| Component | Status | Trust Level |
|-----------|--------|-------------|
| Layout algebra (compose, divide, complement) | Verified (1553 fns) | None |
| ArithExpr IR + correctness proofs | Verified | None |
| ArithExpr exec evaluator | Verified | None |
| GEMM value correctness | Verified | None |
| Bank conflict freedom | Verified | None |
| Scan algorithms (Hillis-Steele, Blelloch, Brent-Kung) | Verified | None |
| Stream compaction (compact_result, compact_indices) | Verified | None |
| FixedPoint arithmetic (add, sub, mul, NTT, Karatsuba) | Verified (275 fns) | None |
| Stage framework (staged_eval, race-freedom, invariants) | **Phase 2 (next)** | None (once proved) |
| ArithExpr → WGSL/SPIR-V emission | **Phase 1 (next)** | None (once proved) |
| Stage → WGSL codegen (barrier placement, loop emission) | **Phase 2** | **Trusted** (auditable template) |
| Barrier semantics (workgroupBarrier = full sync) | Axiom | **Axiom** |
| SPIR-V → GPU machine code | Driver | **Trusted** |
| GPU hardware | Silicon | **Trusted** |
| Verus + Z3 | Proof checker | **Trusted** |

**Irreducible trust: proof checker + barrier axiom + Stage→WGSL codegen + driver + silicon.**

Note: the barrier axiom is minimal — it states only that after `workgroupBarrier()`,
all prior shared memory writes by all threads in the workgroup are visible to all threads.
This is guaranteed by the WGSL/Vulkan/CUDA specification.

---

## What Makes This Tractable

1. **Narrow arithmetic subset**: GPU compute shaders use only integer arithmetic, array indexing, and bounded loops. No pointers, no dynamic dispatch, no heap allocation.

2. **Building blocks exist**: The hard proofs (compose identity, divide correctness, accumulation, bank conflicts) are done. ArithExpr correctness is done.

3. **Fixed-point sidesteps FP**: By using `FixedPoint<N>` backed by integers, all proofs remain in exact integer arithmetic. Known precision loss is bounded, not unbounded.

4. **Simple trust boundary**: A handful of GPU memory axioms. Everything else is verified.

5. **Incremental validation**: Cross-validation (CPU vs GPU) catches trust boundary bugs immediately.

6. **Reusable infrastructure**: Each new kernel type reuses the same ArithExpr IR, emission pipeline, and GPU intrinsics. The per-kernel work is just the domain-specific spec + proof.
