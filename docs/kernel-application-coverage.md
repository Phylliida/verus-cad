# Kernel Application Coverage

How each GPU application maps to the verified Kernel framework. Six kernel patterns are proved correct; the rest are either reducible to these patterns or need specific ArithExpr extensions.

## Proved kernel constructors (6)

| Kernel | Spec | Pattern | Proof |
|--------|------|---------|-------|
| **GEMM** | `C[i,j] = Σ_k A[i*K+k] * B[k*N+j]` | 2D dispatch, Reduce(Sum), row-major gather | `lemma_gemm_kernel_element_correct` |
| **Vector add** | `out[i] = A[i] + B[i]` | 1D dispatch, element-wise | `lemma_vector_add_kernel_correct` |
| **Dot product** | `out[0] = Σ_k a[k] * b[k]` | Single-thread, Reduce(Sum) | `lemma_dot_product_kernel_correct` |
| **Layout offset** | `out[x] = layout.offset(x)` | 1D dispatch, CuTe offset_expr | `lemma_offset_kernel_correct` |
| **1D convolution** | `out[i] = Σ_d input[i+d] * weight[d]` | 1D dispatch, Reduce(Sum), sliding-window gather | `lemma_conv1d_kernel_correct` |
| **Scan (prefix sum)** | `out[i] = Σ_{j=0}^{i} input[j]` | 1D dispatch, Reduce(Sum) with variable bound | `lemma_scan_kernel_correct` |

## Applications covered by existing kernels (no new ArithExpr nodes needed)

### Reducible to GEMM

| Application | How | Notes |
|-------------|-----|-------|
| **Matrix-vector multiply** | `gemm_kernel(M, K, 1)` | GEMM with N=1, 1D output |
| **Batched GEMM** | Add batch dimension to GEMM index | `A[b*M*K + i*K + k]`, 3D dispatch |
| **Outer product** | `Mul(Index(0, Var(0)), Index(1, Var(1)))` | No Reduce, pure element-wise |
| **Fixed-size matmul** | GEMM with small constants | Mat2x2, Mat3x3, Mat4x4 from verus-linalg |

### Reducible to convolution (sliding-window pattern)

| Application | How | Notes |
|-------------|-----|-------|
| **2D convolution** | Nested Reduce over 2D window | `Σ_{dy} Σ_{dx} input[(i+dy)*W + (j+dx)] * kernel[dy*KW + dx]` |
| **1D blur** | `conv1d_kernel` with uniform weights | Special case: all weights = 1/W |
| **Stencil (erosion, fluid)** | Reduce(Sum) over neighbor offsets | Same sliding-window gather, different computation |
| **SSAO** | Reduce over K sample points | Each sample: gather depth at projected offset |

### Reducible to dot product / reduction

| Application | How | Notes |
|-------------|-----|-------|
| **Sum reduction** | `dot_product_kernel` with all b[k] = 1 | Or: `Reduce(1, Const(N), Index(0, Var(1)))` |
| **Weighted average** | Two-output kernel: `(Σ w[i]*x[i], Σ w[i])` | Multi-output, then host divides |
| **Norm squared** | `Reduce(1, Const(N), Mul(Index(0, Var(1)), Index(0, Var(1))))` | Dot product of x with itself |

### Reducible to element-wise (vector add pattern)

| Application | How | Notes |
|-------------|-----|-------|
| **Vector scale** | `Mul(Const(alpha), Index(0, Var(0)))` | Single-buffer, scalar multiply |
| **SAXPY** | `Add(Mul(Const(alpha), Index(0, Var(0))), Index(1, Var(0)))` | a*x + y |
| **Transpose** | Scatter `Add(Mul(Var(1), Const(M)), Var(0))`, compute `Index(0, Add(Mul(Var(0), Const(N)), Var(1)))` | Swapped gather/scatter indices |
| **Negate** | `Sub(Const(0), Index(0, Var(0)))` | Unary minus via Sub |
| **Element-wise multiply** | `Mul(Index(0, Var(0)), Index(1, Var(0)))` | Hadamard product |

### Reducible to scan (prefix sum pattern)

| Application | How | Notes |
|-------------|-----|-------|
| **Exclusive scan** | `partial_sum(input, i)` instead of `partial_sum(input, i+1)` | Shift by one |
| **Stream compaction offsets** | Scan of predicate array | `input[j] = if predicate(j) { 1 } else { 0 }` (needs Select) |
| **Radix sort offsets** | Scan of per-digit histogram | Multi-kernel pipeline: histogram → scan → scatter |

### Multi-output (uses OutputSpec)

| Application | How | Notes |
|-------------|-----|-------|
| **Cross product** | 3 outputs, each Sub(Mul, Mul) | `out_x = a.y*b.z - a.z*b.y`, etc. |
| **Orient2D** | 1 output: `Sub(Mul(...), Mul(...))` | Determinant, 5 ArithExpr nodes |
| **Batch norm (stats)** | 2 outputs: mean (Reduce/Sum/N), variance (Reduce of squared diff) | Needs Reduce(Max) for running stats variant |
| **Mandelbrot step** | 4 outputs: z_re, z_im, escaped, iter | Needs Shr for fixed-point (Phase 2) |

### Multi-kernel pipeline (uses Pipeline)

| Application | How | Notes |
|-------------|-----|-------|
| **Mandelbrot** | Repeat(step_kernel, max_iter) | Each step is multi-output kernel |
| **Radix sort** | Repeat(4, Seq([histogram, scan, scatter])) | 4 passes for 32-bit keys |
| **Hierarchical reduction** | Seq([block_reduce, block_reduce]) | Two-level tree |
| **Conjugate gradient** | RepeatUntil(max_iter, Seq([SpMV, dot, update])) | 3 kernels per iteration |
| **Physics timestep** | Seq([force, integrate]) or Seq([density, pressure, force, integrate]) for SPH | Each step is a kernel |

## Applications needing ArithExpr extensions

### Need Shr (Phase 2 — fixed-point)

| Application | What Shr provides |
|-------------|-------------------|
| **Mandelbrot** | Fixed-point multiply: `(a * b) >> N` |
| **All fixed-point math** | Arithmetic shift right for fractional bits |
| **Radix sort** | Digit extraction: `(key >> (pass * bits)) & mask` (also needs BitAnd) |

### Need Select (Phase 3 — softmax trigger)

| Application | What Select provides |
|-------------|---------------------|
| **ReLU** | `Select(Cmp(Gt, x, 0), x, 0)` = max(0, x) |
| **Clamp** | `Select(Cmp(Lt, x, lo), lo, Select(Cmp(Gt, x, hi), hi, x))` |
| **Safe division** | `Select(Cmp(Ne, denom, 0), Div(a, denom), 0)` |
| **Abs** | `Select(Cmp(Lt, x, 0), Sub(0, x), x)` |
| **Stream compaction** | Predicate mask for scan input |

### Need Reduce(Max/Min) (Phase 3)

| Application | What Max/Min provides |
|-------------|----------------------|
| **Softmax** | `max_k(score[k])` for numerical stability |
| **Argmax** | `max` over values (needs Tuple for (value, index) pair) |
| **SDF min-distance** | `min_k(distance(p, object_k))` |
| **Hi-Z culling** | `min/max` of depth values in tile |

### Need BitXor/BitAnd (Phase 6 — swizzle)

| Application | What bitwise provides |
|-------------|----------------------|
| **Swizzle** | `idx ^ (idx >> shift)` for bank-conflict-free shared memory |
| **Radix sort** | `(key >> bit_pos) & mask` for digit extraction |
| **FFT bit-reversal** | Bit-reverse permutation index |

### Need Intrinsic or fixed-point approximation

| Application | Function needed | Fixed-point alternative |
|-------------|----------------|------------------------|
| **Attention** | exp(x) | Polynomial approximation (Padé/minimax) |
| **N-body/SPH** | sqrt(x) | Newton iteration in fixed-point |
| **FFT** | sin(x), cos(x) | Chebyshev polynomial |
| **Noise/terrain** | sin(x), floor(x) | Polynomial + integer truncation |

### Need shared memory + barriers (Phase 6)

| Application | Why shared memory |
|-------------|-------------------|
| **Tiled GEMM** | Load tiles from global → shared, MAC from shared |
| **Flash attention** | K/V tile loading, online softmax accumulation |
| **Tree reduction** | Intra-workgroup reduction via shared memory |
| **Blelloch scan** | Up-sweep + down-sweep in shared memory |
| **Tiled convolution** | Halo region management for stencil |

### Need atomics (Phase 6+)

| Application | What atomics provide |
|-------------|---------------------|
| **Histogram** | `atomicAdd(&bins[bucket], 1)` |
| **Particle emission** | `atomicAdd(&count, 1)` for append buffer |
| **FEM assembly** | `atomicAdd(&global_stiffness[dof], local_value)` |
| **Decoupled lookback scan** | `atomicAdd` for single-pass prefix sum |

## Summary

| Category | Count | Status |
|----------|-------|--------|
| Proved correct today | 6 kernels | vector_add, GEMM, dot, offset, conv1d, scan |
| Expressible today (no new nodes) | ~20 applications | GEMM variants, element-wise, reductions, transposes |
| Need Shr (Phase 2) | ~5 applications | Fixed-point math |
| Need Select (Phase 3) | ~8 applications | Conditional computation |
| Need Reduce(Max/Min) (Phase 3) | ~5 applications | Softmax, argmax, SDF |
| Need shared memory (Phase 6) | ~10 applications | Tiled kernels |
| Need atomics (Phase 6+) | ~5 applications | Histogram, scatter-add |
