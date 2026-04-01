# GPU Compute Application Analysis

Comprehensive analysis of 27 GPU compute applications: their mathematical specs,
parallel patterns, arithmetic requirements, memory access patterns, and how they
map to a Gather-Compute-Scatter execution model.

## Legend

**Parallel Patterns:** map, reduce, scan (prefix sum), stencil, scatter, gather, sort
**Arithmetic Levels:**
- `int` — integer only
- `float` — add/sub/mul/div, fma
- `transcendental` — exp, log, sin, cos, sqrt, rsqrt, pow, atan2

**Memory Patterns:**
- `element-wise` — each thread reads/writes its own independent element
- `neighbor` — each thread reads a fixed local neighborhood (stencil)
- `random` — data-dependent indexing (indirect/pointer-chasing)
- `atomic` — concurrent read-modify-write to shared locations

---

## 1. GPU Particle Systems

**Math spec:** For each particle i with position p_i, velocity v_i:
- Emission: p_i = emitter_pos + random_offset; v_i = initial_velocity + noise
- Physics: v_i += F_ext * dt; p_i += v_i * dt
- Collision: if distance(p_i, surface) < 0 then reflect/dampen v_i
- Sort: back-to-front ordering by camera distance for alpha blending

**Parallel patterns:** map (emission, physics), gather (collision against SDF/grid), sort (radix sort for depth ordering), scan (prefix sum for compaction of dead particles)

**Arithmetic:** `float` for physics, `transcendental` (sqrt for distance, noise functions may need sin/cos)

**Memory pattern:** element-wise (physics update), random (collision lookups against spatial structures), atomic (emission counter for append buffer)

**Gather-Compute-Scatter fit:** Partially. Physics update is pure map. Emission needs an atomic counter. Sort requires multi-pass radix sort with scan. Collision needs random gather from spatial structures.

**Special requirements:** Atomics for particle count management. Indirect dispatch (particle count drives workgroup count). Multi-pass for sort. Prefix sum for stream compaction of dead particles.

---

## 2. Terrain Generation

**Math spec:**
- Noise: height(x,y) = sum_{i=0}^{octaves} amplitude_i * noise(frequency_i * (x,y))
  where noise is Perlin/simplex noise
- Erosion: iterative hydraulic simulation — water carries sediment downhill,
  deposits when velocity decreases. Thermal erosion: material slides when slope > threshold.
- LOD mesh: generate triangle mesh at varying detail levels based on distance

**Parallel patterns:** map (noise evaluation per grid cell), stencil (erosion reads neighbors), gather (LOD mesh reads height values at varying resolutions)

**Arithmetic:** `transcendental` (noise uses floor, fract, smoothstep which involves polynomial; erosion needs sqrt for gradient magnitude, possibly sin/cos for noise)

**Memory pattern:** element-wise (noise), neighbor (erosion — 4 or 8 neighbors), element-wise (LOD vertex generation)

**Gather-Compute-Scatter fit:** Noise generation is a perfect map. Erosion is a stencil pattern — each cell gathers from fixed neighbors, computes, writes back. Multiple iterations. LOD mesh generation may need prefix sum for variable output counts.

**Special requirements:** Multi-pass for erosion iterations. Shared memory for stencil halo regions. Possibly scan for mesh compaction.

---

## 3. Marching Cubes / Dual Contouring

**Math spec:** Given a 3D scalar field f(x,y,z) and isovalue c:
- For each cube of 8 neighboring samples, classify vertices as inside/outside (f > c)
- 256 possible configurations, lookup table gives triangle edges
- Interpolate vertex positions along edges: p = p0 + (c - f(p0))/(f(p1) - f(p0)) * (p1 - p0)

**Parallel patterns:** map (classify each voxel), gather (read 8 corner values per voxel), scan (prefix sum for output compaction — variable # triangles per voxel)

**Arithmetic:** `float` (linear interpolation, no transcendentals needed)

**Memory pattern:** neighbor (each voxel reads 8 corners from 3D grid), random (lookup table indexed by 8-bit classification)

**Gather-Compute-Scatter fit:** Two-pass design:
1. Pass 1: map over voxels, gather 8 corners, compute triangle count per voxel
2. Prefix sum (scan) over triangle counts to get output offsets
3. Pass 2: map over voxels, gather corners again, scatter triangles to compacted output buffer

**Special requirements:** Multi-pass (classify + scan + emit). Lookup table in constant/uniform memory. Prefix sum is critical for compaction. Variable output per thread.

---

## 4. Screen-Space Ambient Occlusion (SSAO)

**Math spec:** For each screen pixel p with normal n and depth z:
- Generate K sample points in a hemisphere oriented along n
- For each sample s_i: project to screen space, compare depth
- occlusion(p) = (1/K) * sum_{i=1}^{K} [depth(project(s_i)) < z(s_i) ? 1 : 0]

**Parallel patterns:** map (per-pixel), gather (sample depth buffer at K random offsets per pixel)

**Arithmetic:** `transcendental` (sqrt for hemisphere sampling, possibly sin/cos for rotation of sample kernel)

**Memory pattern:** element-wise output, random gather (depth buffer sampled at projected positions), neighbor (blur pass reads nearby pixels)

**Gather-Compute-Scatter fit:** Yes, excellent fit. Each pixel gathers K depth samples, computes occlusion, writes single output. Followed by a separable blur pass (stencil/gather pattern).

**Special requirements:** Random/noise texture for sample kernel rotation (avoids banding). Two passes typically: SSAO generation + bilateral blur. Depth buffer as read-only input.

---

## 5. Tiled/Clustered Deferred Lighting

**Math spec:** For each screen tile T (e.g. 16x16 pixels):
- Compute tile frustum from depth bounds (min_z, max_z)
- For each light L: test intersection(tile_frustum, light_sphere)
- Build per-tile light list
- For each pixel in tile: shade using only lights in tile's list

**Parallel patterns:** reduce (min/max depth per tile), map (frustum-sphere test per light-tile pair), gather (shade pixel using variable-length light list)

**Arithmetic:** `transcendental` (sqrt for distance, pow for attenuation falloff, lighting uses dot products and possibly specular pow)

**Memory pattern:** neighbor (depth min/max over tile), random (light list indexing), element-wise (final pixel shading)

**Gather-Compute-Scatter fit:** Multi-phase:
1. Reduce: per-tile depth min/max
2. Map+scatter: test each light against each tile, build per-tile light lists (needs atomics or local counting)
3. Gather+compute: each pixel gathers from its tile's light list, evaluates lighting equation

**Special requirements:** Shared memory for tile's light list construction. Atomics for appending to per-tile lists. Workgroup = tile. Variable work per tile (some tiles have 0 lights, others 100+).

---

## 6. Shadow Map Generation

**Math spec:** Render scene from light's POV, store only depth:
- For each triangle, rasterize and write depth z = dot(light_dir, vertex_pos)
- Cascaded shadow maps: split view frustum into N cascades, render shadow map per cascade

**Parallel patterns:** map (vertex transform from light perspective), gather (frustum culling reads bounding volumes)

**Arithmetic:** `float` (matrix multiply for transforms, depth comparison)

**Memory pattern:** element-wise (vertex transform), random (index buffer indirection)

**Gather-Compute-Scatter fit:** The compute shader part is primarily the culling pass: gather bounding volumes, compute frustum test, scatter to indirect draw buffer. The actual depth rendering is rasterization pipeline, not a compute pattern.

**Special requirements:** Typically uses rasterization pipeline, not compute. Compute shader role is mainly culling and generating indirect draw arguments.

---

## 7. Mesh Skinning / Skeletal Animation

**Math spec:** For each vertex v with bone weights w_j and bone indices b_j:
- skin_matrix = sum_{j=0}^{3} w_j * bone_matrices[b_j]
- v_skinned = skin_matrix * v_rest_pose
- n_skinned = transpose(inverse(skin_matrix)) * n_rest_pose

**Parallel patterns:** map (one thread per vertex), gather (read bone matrices indexed by per-vertex bone indices)

**Arithmetic:** `float` (4x4 matrix multiply, weighted sum of matrices)

**Memory pattern:** gather (bone matrices from uniform/storage buffer via indirect index), element-wise output

**Gather-Compute-Scatter fit:** Excellent fit. Each vertex gathers up to 4 bone matrices (indirect indexed), computes weighted blend, writes transformed vertex. Pure Gather-Compute-Scatter.

**Special requirements:** Bone matrices uploaded as uniform/storage buffer. Typically 4 bones per vertex (fixed gather count). Output feeds directly to vertex buffer for rendering.

---

## 8. Occlusion Culling (Hi-Z)

**Math spec:**
- Build hierarchical depth buffer: for each 2x2 block, max_depth = max(z00, z01, z10, z11)
  Repeat at each mip level.
- For each object bounding box: project to screen, find appropriate mip level,
  compare object's min depth against Hi-Z max depth. If min_z > max_z_hiz, object is occluded.

**Parallel patterns:** reduce (2x2 max for mip chain), map (per-object culling test), gather (sample Hi-Z at projected bounding box location)

**Arithmetic:** `float` (matrix multiply for projection, depth comparison, min/max)

**Memory pattern:** neighbor (2x2 downsample), random (Hi-Z lookup at projected coordinates), element-wise (write visibility flag per object)

**Gather-Compute-Scatter fit:**
1. Hi-Z build: stencil/reduce pattern — gather 2x2 block, compute max, write to next mip. Multi-pass.
2. Culling: gather (sample Hi-Z texture), compute (depth test), scatter (write visibility bit). Clean Gather-Compute-Scatter.

**Special requirements:** Multi-pass mip chain generation (can be done single-pass with shared memory + atomics). Output drives indirect draw for visible objects.

---

## 9. N-Body Gravity Simulation

**Math spec:** For each body i:
- F_i = sum_{j != i} G * m_i * m_j / |r_ij|^2 * hat(r_ij)
  where r_ij = p_j - p_i, with softening: |r_ij|^2 + epsilon^2
- a_i = F_i / m_i; v_i += a_i * dt; p_i += v_i * dt

Direct: O(n^2). Barnes-Hut: O(n log n) via octree approximation.

**Parallel patterns:** map (force accumulation per body, integration), reduce (tree center-of-mass in Barnes-Hut), gather (all-pairs or tree traversal)

**Arithmetic:** `transcendental` (sqrt or rsqrt for distance normalization)

**Memory pattern:**
- Direct: each thread reads ALL other bodies (massive gather, but regular)
- Barnes-Hut: random (pointer-chasing tree traversal)
- Both: element-wise output

**Gather-Compute-Scatter fit:**
- Direct all-pairs: Each thread gathers all N positions, computes force sum, writes acceleration. Fits well but the gather is the entire input array. Tiled shared-memory optimization loads blocks of 256 bodies into shared memory.
- Barnes-Hut: Poor fit due to irregular tree traversal (random gather with data-dependent depth).

**Special requirements:** Direct: shared memory tiling (load 256 bodies, compute partial forces, repeat). Barnes-Hut: tree construction (sort by Morton code + scan), irregular traversal. rsqrt is performance-critical.

---

## 10. Cloth Simulation (PBD)

**Math spec:** Position-Based Dynamics:
1. v_i += (F_ext / m_i) * dt; p_predicted_i = p_i + v_i * dt
2. For each constraint C (distance, bending):
   delta_p = -C(p) / |grad_C|^2 * grad_C  (Jacobi iteration)
3. Repeat constraint projection K times
4. v_i = (p_new - p_old) / dt

**Parallel patterns:** map (velocity integration, position prediction), stencil (constraint projection reads connected vertices), gather (collision detection against bodies)

**Arithmetic:** `transcendental` (sqrt for distance constraints, rsqrt for normalization)

**Memory pattern:** neighbor (each vertex reads connected vertices — but connectivity is irregular, not grid-aligned), random (collision queries), element-wise (integration step)

**Gather-Compute-Scatter fit:** Integration steps are pure maps. Constraint projection is problematic: two vertices sharing a constraint both want to update, causing write conflicts. Jacobi solver resolves this: read all neighbors' predicted positions (gather), compute corrections independently (compute), write own position (scatter). Converges with iteration.

**Special requirements:** Graph coloring or Jacobi iteration for parallel constraint solving. Multiple iterations per frame (10-30). Collision detection against external geometry.

---

## 11. Eulerian Fluid Simulation

**Math spec:** Navier-Stokes on a grid:
1. Advect: u^{n+1} = u^n(x - u^n * dt)  (semi-Lagrangian, backtrack and interpolate)
2. Diffuse: solve (I - nu * dt * Laplacian) * u = u^n  (implicit diffusion)
3. Add forces: u += F * dt
4. Project (pressure solve): solve Laplacian(p) = div(u), then u -= grad(p)
   Ensures div(u) = 0 (incompressibility)

**Parallel patterns:** gather (advection: backtrack and bilinear interpolate), stencil (Laplacian = 5-point stencil in 2D, 7-point in 3D), map (add forces), stencil (divergence, gradient), reduce (pressure solver convergence check)

**Arithmetic:** `transcendental` (possibly sqrt for vorticity confinement, but core operations are float add/mul)

**Memory pattern:** neighbor (Laplacian stencil, gradient, divergence), random (advection backtrace can land anywhere in grid, typically bilinear interpolate), element-wise (force application)

**Gather-Compute-Scatter fit:**
- Advection: gather (sample grid at backtraced position via bilinear interpolation), compute, scatter (write new velocity). Fits well.
- Pressure solve (Jacobi): stencil — gather 4/6 neighbors, compute weighted average, write center. Multi-iteration.
- Divergence/gradient: stencil — gather neighbors, compute finite differences, write.

**Special requirements:** Multi-pass per timestep (advect, diffuse, force, project). Pressure solver needs 20-50 Jacobi iterations or use multigrid. Ping-pong buffers for iterative solvers. Boundary conditions.

---

## 12. Rigid Body Physics

**Math spec:**
- Broad phase: find potentially colliding pairs using AABB overlap
- Narrow phase: exact contact point computation (GJK/EPA algorithms)
- Constraint solving: sequential impulse or PGS to resolve contacts + joints

**Parallel patterns:** sort (sort AABBs along axis for sweep-and-prune), map (AABB computation per object), scan (prefix sum for pair compaction), gather (narrow phase reads shape data), reduce (constraint solver convergence)

**Arithmetic:** `float` (AABB test, dot products, cross products), `transcendental` (sqrt for GJK distance, normalize)

**Memory pattern:** random (broad phase pair generation, narrow phase shape data), atomic (pair list append), element-wise (AABB computation, integration)

**Gather-Compute-Scatter fit:**
- Broad phase: sort AABBs, then map/gather to test overlaps, scatter pairs. Needs sort.
- Narrow phase: gather (read shape data for each pair), compute (GJK/EPA), scatter (write contact manifold). Fits, but variable work per pair.
- Constraint solver: sequential dependencies between constraints sharing bodies. Hard to parallelize — typically uses graph coloring + Jacobi.

**Special requirements:** Multi-phase pipeline. Sort for broad phase. Atomics for pair list building. Graph coloring for parallel constraint solving. Variable work per pair in narrow phase. Indirect dispatch.

---

## 13. Hair/Fur Simulation

**Math spec:** Each hair strand is a chain of N particles with:
- Distance constraints between consecutive particles: |p_{i+1} - p_i| = rest_length
- Bending/curvature constraints
- Collision with head/body mesh
- Interpolation: simulate K guide strands, interpolate rest

**Parallel patterns:** map (per-strand or per-particle force application), scan (parallel cyclic reduction for tridiagonal solve along strand), gather (collision against body mesh), map (interpolation of non-guide strands)

**Arithmetic:** `transcendental` (sqrt for distance constraints, normalize vectors)

**Memory pattern:** element-wise within strand (sequential particle chain), random (collision against body), gather (interpolation weights from guide strands)

**Gather-Compute-Scatter fit:** Per-strand processing: each strand is independent, internal particles form a chain. Within a strand, constraints are sequential but solvable with parallel cyclic reduction. Guide-to-follower interpolation is pure gather-compute-scatter.

**Special requirements:** Parallel cyclic reduction for O(log n) along-strand solve. Only ~10% of strands simulated (guides), rest interpolated. Collision against skinned mesh requires updated body positions.

---

## 14. Crowd Simulation / Agent-Based Models

**Math spec:** For each agent i with position p_i, velocity v_i:
- Desired velocity: v_desired = normalize(goal - p_i) * max_speed
- Neighbor query: find all agents j within radius R
- Steering forces: separation + alignment + cohesion (Boids) or ORCA velocity obstacles
- v_i = v_i + (steering_force / mass) * dt; p_i += v_i * dt

**Parallel patterns:** map (integration, desired velocity), gather (spatial hash lookup for neighbors), reduce (local averaging for alignment/cohesion)

**Arithmetic:** `transcendental` (sqrt for distance, normalize, possibly atan2 for heading)

**Memory pattern:** random (spatial hash neighbor lookup), element-wise (integration), atomic (spatial hash insertion)

**Gather-Compute-Scatter fit:**
1. Scatter: insert agents into spatial hash (atomics needed)
2. Gather: each agent queries spatial hash for neighbors
3. Compute: evaluate steering forces
4. Scatter: write updated positions

**Special requirements:** Spatial hash table with atomics for insertion. Variable neighbor count per agent. Sorting by spatial hash key improves cache coherence. Shared memory for local neighbor lists.

---

## 15. FFT (Fast Fourier Transform)

**Math spec:** DFT: X[k] = sum_{n=0}^{N-1} x[n] * exp(-2*pi*i*k*n/N)
Cooley-Tukey: decompose into butterfly operations at log2(N) stages.
Each butterfly: (a,b) -> (a + W*b, a - W*b) where W = exp(-2*pi*i*k/N)

**Parallel patterns:** map (butterfly operations at each stage — each thread computes one butterfly), gather (read two elements at stride determined by stage)

**Arithmetic:** `transcendental` (sin, cos for twiddle factors W = cos(theta) + i*sin(theta)), `float` (complex multiply-add for butterflies)

**Memory pattern:** Regular but stride changes each stage. Stage s reads elements at stride 2^s. Shared memory for intra-workgroup stages. Global memory for cross-workgroup stages.

**Gather-Compute-Scatter fit:** Each stage is a Gather(2 elements at computed stride)-Compute(butterfly)-Scatter(write 2 results). Multi-pass: log2(N) stages. Within a workgroup, stages can execute in shared memory without global barriers.

**Special requirements:** Multi-pass (log2(N) stages). Shared memory critical for coalescing. Twiddle factors precomputed or computed on-the-fly with sin/cos. Bit-reversal permutation at start or end. Radix-8/16 kernels to reduce passes.

---

## 16. Sparse Matrix-Vector Multiply (SpMV)

**Math spec:** y = A * x where A is sparse (CSR format):
y[i] = sum_{j in row(i)} A[row_ptr[i]..row_ptr[i+1]] * x[col_idx[j]]

**Parallel patterns:** map (one thread/warp per row), reduce (sum products within each row), gather (indirect read of x[col_idx[j]])

**Arithmetic:** `float` (multiply-add)

**Memory pattern:** random (x vector accessed via indirect col_idx), sequential (values and col_idx arrays within a row), element-wise output

**Gather-Compute-Scatter fit:** Yes: gather (read sparse matrix entries + indirect x values), compute (multiply-accumulate), scatter (write y[i]). The gather is indirect (col_idx determines which x elements to read).

**Special requirements:** Load imbalance (rows have wildly varying nnz). Vector kernel: warp cooperatively reduces one row for better load balance. CSR-Adaptive: variable rows per workgroup based on nnz. Shared memory for partial reductions within warp.

---

## 17. Conjugate Gradient Solver

**Math spec:** Solve Ax = b iteratively:
```
r = b - Ax; p = r; rsold = dot(r,r)
repeat:
  Ap = A*p                    //  SpMV
  alpha = rsold / dot(p, Ap)  //  dot product (reduce)
  x = x + alpha * p           //  vector update (map)
  r = r - alpha * Ap           //  vector update (map)
  rsnew = dot(r, r)           //  dot product (reduce)
  if sqrt(rsnew) < tol: break
  p = r + (rsnew/rsold) * p   //  vector update (map)
  rsold = rsnew
```

**Parallel patterns:** map (vector add/scale: axpy), reduce (dot product), SpMV (see #16)

**Arithmetic:** `float` (multiply-add), `transcendental` (sqrt for convergence check only)

**Memory pattern:** element-wise (vector ops), random (SpMV), reduce (dot products)

**Gather-Compute-Scatter fit:** Each operation individually fits:
- SpMV: gather-compute-scatter (see #16)
- dot product: gather-compute-reduce
- axpy: map (element-wise)
But the CG algorithm itself is sequential: each iteration depends on the previous.

**Special requirements:** Multi-pass (each CG iteration is ~3 kernels: SpMV + 2 dot products + 3 axpy). Global synchronization between iterations. Preconditioning adds another SpMV or triangular solve per iteration.

---

## 18. Monte Carlo Path Tracing

**Math spec:** For each pixel, estimate the rendering equation integral:
L_o(x, w_o) = L_e + integral_{hemisphere} f_r(w_i, w_o) * L_i(x, w_i) * cos(theta) dw_i

Approximate via Monte Carlo: sample N random ray paths per pixel, average contributions.
Each path: ray-scene intersection -> material evaluation -> next bounce direction -> repeat.

**Parallel patterns:** map (one thread per pixel or per ray), gather (BVH traversal for ray-scene intersection — random memory access), reduce (average samples per pixel)

**Arithmetic:** `transcendental` (sqrt, rsqrt, sin, cos, exp, log, pow for sampling distributions, BRDF evaluation, tone mapping)

**Memory pattern:** random (BVH tree traversal, texture lookups, material data), element-wise (accumulate per-pixel results)

**Gather-Compute-Scatter fit:** Poorly. The BVH traversal is deeply irregular: each ray follows a different path through the tree, with data-dependent branching and variable work per ray. Thread divergence is a major issue.

**Special requirements:** PRNG per thread (or quasi-random sequences). Stream compaction / ray regeneration to maintain SIMD efficiency when rays terminate. BVH structure in global memory. Texture atlas for materials. Typically progressive: accumulate samples over multiple frames.

---

## 19. Molecular Dynamics

**Math spec:** For each atom i:
- F_i = sum_{j in neighbors(i)} f(r_ij)  where f is the force function
  (Lennard-Jones: f(r) = 24*epsilon * [2*(sigma/r)^12 - (sigma/r)^6] / r)
  (Coulomb: f(r) = k * q_i * q_j / r^2)
- a_i = F_i / m_i; v_i += a_i * dt; p_i += v_i * dt  (velocity Verlet)

**Parallel patterns:** map (integration), gather (neighbor list: each atom reads positions of nearby atoms), reduce (force accumulation per atom)

**Arithmetic:** `transcendental` (pow or repeated multiply for LJ 6-12, sqrt/rsqrt for distance, exp for Ewald summation long-range corrections)

**Memory pattern:** random (neighbor list — indirect indexing), element-wise (integration), reduce (energy/temperature computation)

**Gather-Compute-Scatter fit:** Good fit: gather (read neighbor positions via neighbor list), compute (evaluate force function, accumulate), scatter (write force/acceleration for own atom). Each atom's force computation is independent once neighbor list is built.

**Special requirements:** Neighbor list rebuild every N steps (spatial hash or cell list + sort). Cutoff radius determines neighbor count. Force evaluation is the bottleneck (~90% of time). Shared memory for tile-based force computation.

---

## 20. Finite Element Method (FEM)

**Math spec:**
- For each element e: compute local stiffness matrix K_e by numerical integration
  K_e = integral B^T * D * B * det(J) * dV  (B = strain-displacement, D = material, J = Jacobian)
- Assemble: K_global[I,J] += K_e[i,j] for all elements e mapping local DOF i,j to global DOF I,J
- Solve: K * u = f  (linear system, typically using CG or direct solver)

**Parallel patterns:** map (per-element stiffness computation — embarrassingly parallel), scatter (assembly: multiple elements contribute to same global DOF), reduce (assembly conflicts at shared nodes), CG solver (see #17)

**Arithmetic:** `float` (matrix multiply, numerical integration), `transcendental` (sqrt, possibly exp for nonlinear materials)

**Memory pattern:** gather (element reads its node positions via connectivity table), scatter+atomic (assembly to global matrix), random (sparse matrix access in solver)

**Gather-Compute-Scatter fit:**
- Element computation: gather (node positions via connectivity), compute (stiffness matrix via quadrature), scatter (to global matrix). Fits, but scatter has conflicts.
- Assembly: race conditions when multiple elements write to shared DOFs. Use atomics or coloring.
- Solve: CG or multigrid (see #17).

**Special requirements:** Graph coloring to avoid assembly conflicts (or atomics). Numerical integration (Gauss quadrature). Element connectivity (indirect indexing). Multi-phase: compute elements -> assemble -> solve.

---

## 21. Flash Attention

**Math spec:**
S = Q * K^T / sqrt(d_k)    (scaled dot-product attention scores)
P = softmax(S, dim=-1)      (row-wise softmax)
O = P * V                   (weighted value aggregation)

**Parallel patterns:** map (scale), reduce (row-wise max and sum for softmax), gather (tiled matrix multiply reads blocks of Q, K, V)

**Arithmetic:** `transcendental` (exp for softmax, sqrt for scaling factor, rsqrt)

**Memory pattern:** Tiled block access (load tiles of Q/K/V from HBM to SRAM), element-wise within tile, reduce across tiles

**Gather-Compute-Scatter fit:** The tiling strategy is: gather (load Q tile + K tile from HBM), compute (tile GEMM + online softmax update), scatter (accumulate to output tile). The "online softmax" trick allows computing softmax across tiles incrementally.

**Special requirements:** Tiled execution critical for memory efficiency. Online softmax (track running max and sum). Recomputation in backward pass instead of storing O(n^2) attention matrix. Shared memory for tile storage.

---

## 22. Convolution (1D, 2D, 3D)

**Math spec:** For 2D: output[y][x] = sum_{ky,kx} input[y+ky][x+kx] * kernel[ky][kx]
Generalized: output[i] = sum_{k} input[i+k] * kernel[k] (with appropriate boundary handling)

**Parallel patterns:** stencil (each output reads a local neighborhood of input), map (one thread per output element)

**Arithmetic:** `float` (multiply-accumulate). For depthwise-separable: same. For FFT-based convolution: needs transcendentals.

**Memory pattern:** neighbor (fixed-size kernel neighborhood), element-wise output

**Gather-Compute-Scatter fit:** Excellent fit. Each output element gathers input[y-K..y+K][x-K..x+K] (fixed neighborhood), computes dot product with kernel, writes output. Shared memory tiling loads input tile + halo into shared memory, eliminating redundant global reads.

**Special requirements:** Shared memory for tiled input + halo region. Constant memory for kernel weights. Halo region handling at tile boundaries. For large kernels, FFT-based convolution may be faster.

---

## 23. Batch Normalization / Layer Normalization

**Math spec:**
- Compute mean: mu = (1/N) * sum(x_i)
- Compute variance: sigma^2 = (1/N) * sum((x_i - mu)^2)
- Normalize: y_i = (x_i - mu) / sqrt(sigma^2 + epsilon)
- Scale and shift: z_i = gamma * y_i + beta

Batch norm: statistics over batch+spatial dims per channel.
Layer norm: statistics over feature dims per sample.

**Parallel patterns:** reduce (sum for mean, sum of squares for variance), map (normalization and scale/shift)

**Arithmetic:** `transcendental` (sqrt or rsqrt for 1/sqrt(var+eps))

**Memory pattern:** element-wise (normalization), reduce (statistics computation)

**Gather-Compute-Scatter fit:** Two-pass:
1. Reduce: gather all elements in normalization group, compute sum and sum-of-squares, produce mean and variance (reduce pattern)
2. Map: each element gathers mean/variance (single values), computes normalized output

**Special requirements:** Two-pass (compute statistics, then normalize). Welford's online algorithm can compute mean+variance in one pass. Shared memory for partial sums within workgroup. Cross-workgroup reduction for batch norm (atomics or multi-level reduce).

---

## 24. Embedding Lookup / Gather

**Math spec:** Given indices I[0..B] and embedding table E[V][D]:
output[b] = E[I[b]]  (copy row I[b] from embedding table)
Optionally with reduction: output[b] = sum/mean(E[I[b][0]], E[I[b][1]], ...)

**Parallel patterns:** gather (pure indirect memory read)

**Arithmetic:** `int` (index computation only) or `float` (if reduction over multiple embeddings)

**Memory pattern:** random (each lookup reads a different row based on input index — completely data-dependent)

**Gather-Compute-Scatter fit:** Perfect gather pattern. Each thread reads an index, gathers the corresponding embedding row, writes to output. Pure memory bandwidth bound, minimal compute.

**Special requirements:** Memory bandwidth bound (not compute bound). Coalescing is difficult since indices are random. Pre-sorting indices by value can improve cache hit rate. Vector loads (float4) for reading embedding rows.

---

## 25. Top-K Selection

**Math spec:** Given input array A[N], find the K largest (or smallest) elements and their indices.
Equivalently: find the K-th order statistic and partition.

**Parallel patterns:** sort (partial — only need top K), reduce (partial: find K-th element as pivot), map (partition around pivot)

**Arithmetic:** `float` or `int` (comparison-based, no transcendentals)

**Memory pattern:** random (during radix-based selection, elements scatter to buckets), element-wise (during comparisons)

**Gather-Compute-Scatter fit:** Multiple strategies:
1. **Bitonic top-K:** Local sort to length K, then merge pairs. Fits gather(2 elements)-compute(compare-swap)-scatter pattern. O(N * log^2(K)).
2. **Radix selection:** Histogram bits, pick bucket containing K-th element, recurse. Multi-pass: histogram(reduce+atomic) -> select bucket(map) -> compact(scan).
3. **Heap-based:** Each thread maintains local heap of K elements. Final merge.

**Special requirements:** Multi-pass for radix selection. Shared memory for bitonic networks or local heaps. For small K, bitonic approach is efficient. For large K relative to N, full sort may be simpler.

---

## 26. Histogram / Binning

**Math spec:** Given input A[N] and B bins with boundaries b_0 < b_1 < ... < b_B:
H[k] = count({i : b_k <= A[i] < b_{k+1}})

**Parallel patterns:** map (classify each element to bin), reduce (count per bin — via atomics)

**Arithmetic:** `int` (bin computation), `float` (if bin boundaries are float, comparison)

**Memory pattern:** atomic (multiple threads increment same bin counter), element-wise input read

**Gather-Compute-Scatter fit:** Each thread: gather (read element), compute (determine bin), scatter (atomicAdd to bin counter). The scatter is the bottleneck due to contention.

**Special requirements:** Shared memory privatization: each workgroup maintains local histogram in shared memory (using shared atomics), then merges to global. Dramatically reduces contention. For few bins, sub-histograms per thread. For many bins, shared memory is sufficient.

---

## 27. Radix Sort on GPU

**Math spec:** Sort N keys by examining digits from LSB to MSB.
For each digit position d (using radix R, typically R=256 for 8-bit digits):
1. Histogram: count occurrences of each digit value
2. Prefix sum: exclusive scan of histogram gives write offsets
3. Scatter: write each element to its computed destination

**Parallel patterns:** reduce (histogram per digit), scan (prefix sum of histogram), scatter (reorder elements), gather (read elements for next pass)

**Arithmetic:** `int` (bit extraction, comparison, offset computation)

**Memory pattern:** element-wise read, atomic (histogram), sequential (scan), random scatter (reorder)

**Gather-Compute-Scatter fit:** Each pass is:
1. Gather (read keys) -> Compute (extract digit, build histogram) -> Reduce (histogram via atomics)
2. Scan (prefix sum of histogram — separate kernel)
3. Gather (read keys + scan results) -> Compute (calculate destination) -> Scatter (write to destination)
Four passes for 32-bit keys with 8-bit radix (4 digits).

**Special requirements:** Multi-pass (4 passes for 32-bit, 8 for 64-bit). Prefix sum is critical primitive. Local sort in shared memory before global scatter improves coalescing. One-sweep variants reduce to single pass per digit using decoupled lookback.

---

## Summary Table

| # | Application | Patterns | Arithmetic | Memory | GCS Fit | Passes |
|---|-------------|----------|-----------|--------|---------|--------|
| 1 | Particle System | map, sort, scan | float+trans | elem+random+atomic | Partial | Multi |
| 2 | Terrain Gen | map, stencil | float+trans | elem+neighbor | Good | Multi |
| 3 | Marching Cubes | map, gather, scan | float | neighbor+LUT | Good (2-pass) | 3 |
| 4 | SSAO | map, gather | float+trans | random gather | Excellent | 2 |
| 5 | Tiled Lighting | reduce, map, gather | float+trans | neighbor+random+atomic | Good | 3 |
| 6 | Shadow Maps | map | float | elem | N/A (raster) | 1 |
| 7 | Mesh Skinning | map, gather | float | indirect gather | Excellent | 1 |
| 8 | Hi-Z Culling | reduce, map, gather | float | neighbor+random | Good | 2 |
| 9 | N-Body | map, reduce, gather | float+trans | all-to-all or random | Good (direct) | 1 |
| 10 | Cloth Sim | map, stencil | float+trans | irregular neighbor | OK (Jacobi) | Multi |
| 11 | Fluid Sim | gather, stencil, map | float | neighbor+random | Good | Multi |
| 12 | Rigid Body | sort, map, scan, gather | float+trans | random+atomic | Partial | Multi |
| 13 | Hair Sim | map, scan | float+trans | elem+random | Good | Multi |
| 14 | Crowd Sim | map, gather | float+trans | random+atomic | OK | Multi |
| 15 | FFT | map, gather | float+trans | strided | Good | log(N) |
| 16 | SpMV | map, reduce, gather | float | indirect random | Excellent | 1 |
| 17 | Conjugate Grad | map, reduce, SpMV | float | elem+random | Good | Multi (iter) |
| 18 | Path Tracing | map, gather | float+trans | random (BVH) | Poor | Multi |
| 19 | Molecular Dyn | map, gather, reduce | float+trans | indirect random | Good | 1+rebuild |
| 20 | FEM | map, scatter, reduce | float+trans | indirect+atomic | OK | Multi |
| 21 | Flash Attention | map, reduce, gather | float+trans | tiled block | Good | 1 (tiled) |
| 22 | Convolution | stencil, map | float | neighbor | Excellent | 1 |
| 23 | BatchNorm/LayerNorm | reduce, map | float+trans | elem+reduce | Good | 2 |
| 24 | Embedding Lookup | gather | int/float | random | Excellent | 1 |
| 25 | Top-K | sort, reduce, map | int/float | random+elem | OK | Multi |
| 26 | Histogram | map, reduce(atomic) | int/float | atomic scatter | Good | 1 |
| 27 | Radix Sort | reduce, scan, scatter | int | atomic+random scatter | Good | 4-8 |

---

## Pattern Frequency Analysis

**Most common patterns across all 27 applications:**
- **map**: 25/27 (nearly universal — per-element independent computation)
- **gather** (indirect read): 20/27 (reading data at computed/indirect addresses)
- **reduce**: 17/27 (summing, min/max, dot products, histograms)
- **scatter** (indirect write): 10/27 (writing to computed addresses)
- **scan** (prefix sum): 7/27 (compaction, offset computation, radix sort)
- **stencil** (fixed neighbor): 6/27 (convolution, fluid sim, erosion, Hi-Z)
- **sort**: 5/27 (particles, rigid body, radix sort, top-K, broad phase)

**Arithmetic requirements:**
- Integer only: 3/27 (embedding lookup, histogram with int data, radix sort)
- Float (add/mul/div): 27/27 (universal)
- Transcendentals: 18/27 (sqrt/rsqrt nearly universal; sin/cos for FFT, noise, sampling; exp for softmax, distributions; pow for lighting)

**Most critical transcendentals by frequency:**
1. sqrt / rsqrt — distance computation, normalization (14/27)
2. exp — softmax, distributions, attenuation (5/27)
3. sin / cos — FFT twiddle factors, noise, hemisphere sampling (6/27)
4. pow — lighting BRDF, LJ potential (3/27)
5. log — Monte Carlo, information-theoretic (2/27)

**Memory access patterns:**
- Element-wise: 25/27
- Regular neighbor (stencil): 6/27
- Indirect/random gather: 18/27
- Atomic: 9/27
- Strided: 2/27 (FFT, specific scan patterns)

---

## Implications for a Verified GPU Compute Framework

### Core Primitives Needed (ordered by coverage)

1. **Map** (per-element): covers 25/27 apps. Simplest to verify.
2. **Reduce** (sum, max, min, count): covers 17/27. Needs tree reduction in shared memory.
3. **Gather** (indirect read): covers 20/27. Index bounds checking is the key verification target.
4. **Scan** (prefix sum): covers 7/27 but critical for compaction/sort. Well-studied algorithm.
5. **Scatter** (indirect write): covers 10/27. Needs uniqueness proof or atomics.
6. **Stencil** (fixed neighborhood): covers 6/27. Halo region management is verification target.
7. **Sort** (radix): covers 5/27. Built from histogram + scan + scatter.

### Arithmetic Operations Needed

**Tier 1 (integer-only viable for 3 apps):**
- i32/u32: add, sub, mul, div, mod, bitwise (and, or, xor, shift), comparison

**Tier 2 (float required for 24 more apps):**
- f32: add, sub, mul, div, fma, comparison, min, max, clamp, mix/lerp
- f32: floor, ceil, fract, abs, sign

**Tier 3 (transcendentals needed for 18 apps):**
- sqrt, rsqrt (14 apps — most critical single operation)
- sin, cos (6 apps — FFT, noise, sampling)
- exp (5 apps — softmax, distributions)
- log (2 apps)
- pow (3 apps — could implement as exp(y*log(x)))
- atan2 (2 apps — angle computation)

### Special Operation Support

- **Atomics** (atomicAdd, atomicMax, atomicMin, atomicCompareExchange): 9/27 apps
- **Shared/workgroup memory**: 20/27 apps benefit significantly
- **Indirect dispatch**: 5/27 apps (particle systems, rigid body, variable workloads)
- **Multi-pass execution**: 20/27 apps need multiple kernel launches per frame
