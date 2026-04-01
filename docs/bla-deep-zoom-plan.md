# BLA Deep Zoom: Verified Perturbation Theory for Mandelbrot

## Overview

Bivariate Linear Approximation (BLA) enables deep Mandelbrot zoom (10^100+ magnification) by skipping most iterations via precomputed linear maps. This document plans a verified implementation using our existing infrastructure.

**Key insight:** BLA composition is algebraically identical to our verified `Reduce` splitting — merging two linear maps is the same structure as splitting a summation into blocks. The validity radius is interval arithmetic. The reference orbit uses arbitrary-precision fixed-point.

## The Algorithm

### Three precision tiers

| Component | Precision | Our library |
|-----------|-----------|-------------|
| Reference orbit `Z_m`, center `C` | Arbitrary precision | verus-fixed-point (multi-limb) |
| BLA coefficients `A, B, R` | f64 or float-exp | verus-interval-arithmetic |
| Per-pixel delta `z`, `c` | f32 (GPU) | ArithExpr + WGSL emission |

### Step 1: Reference orbit (CPU, arbitrary precision)

Compute `Z_{m+1} = Z_m² + C` for `m = 0..M` using `verus-fixed-point`:
- `Z_0 = 0`
- Each step: `ComplexFP.mandelbrot_step(c)` from verus-fractals
- Store full-precision orbit AND downconverted f64 version for GPU

### Step 2: BLA table construction (CPU, f64)

For each reference iteration, build a single-step BLA:
```
BLA[0][n] = { A = 2·Z_n, B = 1, R = ε · |2·Z_n|, l = 1 }
```

Then merge bottom-up in a binary tree:
```
BLA[k+1][i] = merge(BLA[k][2i], BLA[k][2i+1])
```

Merge formula:
```
A_z = A_y · A_x
B_z = A_y · B_x + B_y
R_z = max(0, min(R_x, (R_y - |B_x|·|c_max|) / |A_x|))
l_z = l_x + l_y
```

Total: O(M) entries across O(log M) levels.

### Step 3: Per-pixel iteration (GPU, f32)

For each pixel with delta `c` from reference center:
```
m = 0, z = 0
while not escaped and m < M:
    bla = find_largest_valid_bla(m, |z|)
    if bla:
        z = bla.A · z + bla.B · c    //  skip l iterations!
        m += bla.l
    else:
        z = 2·Z[m]·z + z² + c        //  one perturbation step
        m += 1
    if |Z[m] + z| < |z|:             //  rebase check
        z = Z[m] + z
        m = 0
```

### Step 4: Display

Map iteration counts to colors (same as current Mandelbrot renderer).

## What we need to verify

### Property 1: BLA composition correctness
```
If T_x: z → A_x·z + B_x·c  and  T_y: z → A_y·z + B_y·c
Then T_y(T_x(z)) = (A_y·A_x)·z + (A_y·B_x + B_y)·c
```
This is straightforward complex algebra. Proves the merge formula is correct.

### Property 2: Validity radius soundness
```
If |z| < R_z where R_z = max(0, min(R_x, (R_y - |B_x|·|c_max|) / |A_x|))
Then |z| < R_x  AND  |A_x·z + B_x·c| < R_y
```
Proves that if the merged radius is satisfied, both component BLAs are valid.

### Property 3: Error bound
```
|z_{n+l}^exact - (A·z_n + B·c)| ≤ ε · |z_{n+l}^exact|
```
The nonlinear error from omitting `z²` terms is bounded by machine epsilon times the result. This is the core correctness theorem — it says BLA introduces less error than floating-point rounding.

### Property 4: Rebasing preserves orbit
```
After: z' = Z_m + z, m' = 0
Invariant: Z_{m'} + z' = Z_0 + (Z_m + z) = Z_m + z (unchanged)
```
Trivial but important — rebasing doesn't change the mathematical orbit.

### Property 5: Table construction invariant
```
BLA[k][i] correctly represents the composition of 2^k consecutive
single-step BLAs starting at iteration i·2^k + 1.
```
Proved by induction on k, using Property 1 for the merge step.

## Connection to our verified infrastructure

### BLA composition = ArithExpr Reduce splitting

The BLA merge `T_z = T_y ∘ T_x` is structurally identical to our `lemma_reduce_sum_split`:
```
Σ_{i=0}^{a+b-1} f(i) = Σ_{i=0}^{a-1} f(i) + Σ_{i=a}^{a+b-1} f(i)
```

Both decompose a sequential computation into composable blocks. The BLA table IS a segment tree of composed linear maps, just as our tiled reduction IS a segment tree of partial sums.

### Validity radius = interval arithmetic

The radius `R_z = max(0, min(R_x, (R_y - |B_x|·|c_max|) / |A_x|))` is an interval bound computation. `verus-interval-arithmetic` (220 verified lemmas) provides exactly this: containment proofs for arithmetic on intervals.

### Reference orbit = ComplexFP iteration

`Z_{m+1} = Z_m² + C` is exactly `ComplexFP.mandelbrot_step(c)` from verus-fractals, using verus-fixed-point for arbitrary precision.

### Per-pixel GPU kernel = KernelSpec

The per-pixel iteration (with BLA lookup) is a map kernel: each pixel independently computes its escape time. The BLA table and reference orbit are read-only input buffers. This fits our `KernelSpec` architecture with `Index` reads from the BLA table buffer.

## Implementation plan

### Phase A: Arbitrary-precision reference orbit (verus-fractals + verus-fixed-point)

**File:** `verus-fractals/src/reference_orbit.rs`

1. `compute_reference_orbit(center: ComplexFP, max_iter: nat) -> Vec<ComplexFP>`
2. Uses existing `ComplexFP.mandelbrot_step` with `mul_spec` + `reduce_down_spec`
3. Prove: orbit[m+1] = orbit[m]² + center (induction)
4. Downconvert to f64 for BLA table construction

**Depends on:** verus-fixed-point mul, add, reduce (all verified)

### Phase B: BLA table (verus-fractals)

**File:** `verus-fractals/src/bla.rs`

Types:
```rust
struct BlaEntry {
    a_re: f64, a_im: f64,  //  complex A coefficient
    b_re: f64, b_im: f64,  //  complex B coefficient
    r2: f64,               //  validity radius squared
    l: u32,                //  skip length
}

struct BlaTable {
    entries: Vec<Vec<BlaEntry>>,  //  entries[level][index]
    num_levels: nat,
}
```

Functions:
1. `single_step_bla(z_n: Complex<f64>, epsilon: f64) -> BlaEntry`
2. `merge_bla(t_x: BlaEntry, t_y: BlaEntry, c_max: f64) -> BlaEntry`
3. `build_bla_table(orbit: &[Complex<f64>], epsilon: f64, c_max: f64) -> BlaTable`
4. `lookup_bla(table: &BlaTable, m: u32, z_mag: f64) -> Option<&BlaEntry>`

Proofs:
- `lemma_merge_correct`: composition formula is algebraically correct
- `lemma_merge_radius_sound`: merged radius implies both component radii satisfied
- `lemma_table_invariant`: table[k][i] = composition of 2^k single-step BLAs

### Phase C: GPU kernel for per-pixel BLA iteration

**File:** `verus-cutedsl-codegen` + `verus-gpu-examples`

WGSL shader:
- Reads: `params` (viewport), `ref_orbit` (Z[] as vec2<f32>), `bla_table` (flat buffer), `bla_offsets` (level starts)
- Writes: `out` (iteration counts)
- Per pixel: BLA lookup + perturbation + rebase loop

This is a compute shader similar to our current Mandelbrot, but with:
- BLA table buffer reads via `Index`
- Reference orbit buffer reads via `Index`
- The inner loop has BLA skip + fallback perturbation

### Phase D: Browser integration

Update `mandelbrot.html`:
- CPU (JS/WASM): compute reference orbit + BLA table at arbitrary precision
- GPU (WebGPU): per-pixel BLA iteration with the generated WGSL
- Interactive: pan/zoom regenerates reference orbit + BLA table

For the browser, arbitrary precision can use a JS bignum library or WASM-compiled verus-fixed-point.

## Precision and zoom depth

| Precision | Max zoom | Notes |
|-----------|----------|-------|
| f32 GPU + f64 BLA | ~10^7 | No rescaling |
| f32 GPU + floatexp BLA | ~10^15 | With rescaling |
| f64 GPU + floatexp BLA | ~10^15 | Better quality |
| f32 GPU + arbitrary ref | ~10^100+ | Needs periodic rescaling |

With our verus-fixed-point (multi-limb): reference orbit precision is limited only by memory and computation time. The BLA table uses f64 or floatexp (can be implemented with verus-interval-arithmetic for verified bounds). Per-pixel GPU computation stays in f32.

## What to prove vs what to trust

| Component | Verification |
|-----------|-------------|
| Reference orbit computation | Verus-proved (ComplexFP.mandelbrot_step) |
| BLA composition formula | Verus-proved (complex algebra) |
| BLA validity radius soundness | Verus-proved (interval arithmetic) |
| BLA table construction | Verus-proved (induction on levels) |
| Rebasing correctness | Verus-proved (trivial orbit preservation) |
| Error bound (ε analysis) | Verus-proved (interval containment) |
| WGSL shader emission | Auditable (~100 lines) + naga-validated |
| GPU f32 arithmetic | Trusted (hardware) |
| Arbitrary precision library | Verus-proved (verus-fixed-point, 381 functions) |

## Dependencies on existing work

| Need | Have | Status |
|------|------|--------|
| Complex multiply + add | ComplexFP in verus-fractals | Done (8 verified) |
| Arbitrary-precision fixed-point | verus-fixed-point | Done (381 verified) |
| Interval arithmetic | verus-interval-arithmetic | Done (220 verified) |
| GPU kernel emission | verus-cutedsl-codegen | Done (20 tests) |
| ArithExpr with Shr | verus-cutedsl | Done (1635 verified) |
| Buffer reads for BLA table | Index(buf, expr) in ArithExpr | Done |
| Interactive WebGPU | mandelbrot.html | Done |

## Key references

- Claude Heiland-Allen: [mathr.co.uk/web/deep-zoom.html](https://mathr.co.uk/web/deep-zoom.html)
- Phil Thompson: [BLA explainer](https://philthompson.me/2023/Faster-Mandelbrot-Set-Rendering-with-BLA-Bivariate-Linear-Approximation.html)
- Fraktaler 3: [fraktaler.mathr.co.uk](https://fraktaler.mathr.co.uk/)
- FractalShark (CUDA BLA): [github.com/mattsaccount364/FractalShark](https://github.com/mattsaccount364/FractalShark)
- Original thread: [fractalforums.org/index.php?topic=4360](https://web.archive.org/web/20230125202704/https://fractalforums.org/f/28/t/4360)
