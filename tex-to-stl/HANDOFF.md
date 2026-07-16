# HANDOFF — Bergeron's 2-Tamari figure → 3D models

## What this is

Started from a hand-drawn classroom figure (`lattice.jpg`) + its TikZ source (`figure.tex`):
a 3D colored decomposition of a polytope into cubes/prisms/blobs. Goal evolved from
"convert to STL" → "make a faithful, convex, printable model with the right math."

**Identified definitively:** `figure.tex` is **Figure 6 of F. Bergeron, "Combinatorics of
r-Dyck paths, r-Parking functions, and the r-Tamari lattices" (arXiv:1202.6269)** — the
geometric realization of the **2-Tamari poset `Dyck^(2)_4`**.
- 55 vertices = the 2-Tamari elements (Fuss–Catalan `(1/9)C(12,4)=55`)
- 14 cells = **products of associahedra**: 4 cubes (K3×K3×K3), 8 pentagon-prisms (K4×K3),
  2 K5 (the 3-associahedron). These are the fibers of the projection 2-Tamari → 1-Tamari (T4),
  and they correspond to **sublattices** of the Tamari lattice.
- `catalan_combinatorics.tex` (the paper source) only `\includegraphics{Tamari42.pdf}` — it
  has NO coordinates. `figure.tex` is the actual drawing source of Fig 6.

## The central mathematical finding

The **rigorous ν-associahedron** (Ceballos–Padrol–Sarmiento brick polytope) of the 2-Tamari
lattice is **6-DIMENSIONAL** (`dim = 2(n-1) = 6` for n=4). Bergeron's 3D figure is a
**flattened shadow** of that 6D object. This is *why* the schematic's walls were non-planar
and why naive "keep the outer shell fixed" convexification was infeasible
(witness: shared wall `{221,321,431,331}` has `det=12≠0`; vertex `321` over-constrained by 5
fixed planes).

BUT: Bergeron's *coarse 3D decomposition* (14 product cells) is a different, genuinely
3-dimensional object, and it CAN be realized convexly with all 55 vertices free.

## Key scripts (in `tex-to-stl/`)

| file | what it does |
|---|---|
| `tex_to_stl.py` | parse `figure.tex`, planarize faces (`--crease=convex/concave/fan`), write STL, `--split` per cell. Validated, watertight checks built in. |
| `tamari_normal_fan.py` | Loday K5 (3D associahedron) + **normal-fan decomposition** = 14 cells whose adjacency is EXACTLY the Tamari Hasse diagram. |
| `tamari_symmetric.py` | **symmetric K5** = secondary polytope of a regular hexagon (the "plump" associahedron). |
| `tamari_k6.py`, `tamari_k6_schlegel.py` | 4D associahedron **K6** + Schlegel projection. `build_k6_hexfacet()` makes the projected-through facet EXACTLY the symmetric K5. → `tamari_k6/symm_*.stl` |
| `tamari_k5xk3.py` | **K5 × K3** prism (cube-containing) Schlegel. |
| `tamari_nu.py` | **ν-trees** (55, validated against Catalan + the paper's ENEEN=7) + **brick vectors** (Pilaud–Stump, validated EXACTLY against the paper's 7 ENEEN vectors). The rigorous 6D object. |
| `tamari_wireframe.py` | hollow/wireframe STLs (struts; `--joints` for corner balls). |

## Output directories

- `tamari/`, `tamari_sym/`, `tamari_k6/`, `tamari_k5xk3/` — **convex, watertight associahedron
  decompositions** (verified convex + exact tiling). `tamari_sym/` and `tamari_k6/` have the
  **symmetric associahedron** outer.
- `tamari_nu_out/` — the rigorous 6D ν-associahedron projected to a 3D **shadow** (wireframe STL).
- `pieces_out/` — Fig 6's 14 cells as solids, straight from `figure.tex` (verified 14 closed solids).
- `flat_out/` (+ `flattened_coords.json`) — `figure.tex` **planarized**: convex cells, faces flat
  (dev 0.0004), watertight. All 14 cells convex.
- `product_out/` (+ `product_coords.json`) — **genuine metric products**: cubes = real
  parallelepipeds (`[4,4,4]` parallel edge classes), prisms = real pentagon-prisms
  (`[2,2,2,2,2,5]`), parallelism exact to 0.01°. Convex cells, watertight.
- `convex_product_out/` (+ `convex_product_coords.json`) — **frontier (see below).**

## Constraints checklist — RESOLVED

`convex_product_out/` (+ `convex_product_coords.json`, `figure_convex_product.tex`):

- [x] pieces are products of associahedra (segments K3, pentagons K4, products) — verified by f-vectors
- [x] cubes rare — 4/14 (vs 8 prisms)
- [x] pieces correspond to sublattices of the Tamari lattice — 1-skeleton == 2-Tamari Hasse
      diagram exactly; orienting by the x-axis makes every cell a closed interval (= sublattice)
- [x] genuine metric products (parallelepipeds / real prisms) — **parallelism 0.001°**
- [x] convex cells, watertight (0 boundary edges, 14 closed solid pieces)
- [x] **outer shell = convex 3D associahedron (K5)** — clean convex: max poke-out beyond any of
      the 9 facet supporting planes = +0.00001 (0.000% of the 11.7-unit span); faces planar 2e-5
- [~] **outer = SYMMETRIC associahedron** — impossible *with* metric products (proof below), but
      ACHIEVED *with combinatorial* products → `symmetric_combo_out/` (the user's chosen tradeoff).

## 2026-07-16 CORRECTION: symmetric+products is PARTLY POSSIBLE (C2 built!)

Danielle suspected the impossibility proof was sus. She was right. The old proof
(§ below) compared the forced parallel classes against ONE FIXED shape (the
secondary polytope of the regular hexagon). That only rules out that exact
polytope — parallel classes are not combinatorial invariants, and "symmetric"
should quantify over ALL symmetric realizations. Corrected analysis
(`symmetric_metric_feasibility.py`):

**Realization-independent classification** (join argument): if a realization
has a geometric symmetry realizing a subgroup G <= Aut(K5-skeleton) (order 12),
its parallel partition must refine-contain P* = join_{g in G} g(P), where
P = forced partition (sizes [1,1,1,2,2,2,2,2,3,5], re-derived + verified).
- **|G| >= 3 is IMPOSSIBLE** (this part of the old conclusion survives, now
  realization-independently): C3 join = three classes of 7 containing
  adjacent parallel edges (degenerate vertex) + 3 parallel edges in one
  pentagon facet. Order-6 elements collapse all 21 edges. ALL V4s fail.
  So the max possible symmetry order is 2.
- **Three involutions pass all necessary conditions**: inv#0, inv#2
  (4 resp. 6 fixed corners => must be mirrors; both orientation-reversing OK)
  and inv#6 (no fixed corners, fixed edge (222,442) with swapped endpoints
  => must be a C2 rotation; orientation-preserving OK).

**inv#6 (C2 rotation) is REALIZED** — `symmetric_metric_optimize.py 6 600 2400`
=> `symmetric_metric_inv6_coords.json`, `figure_symmetric_metric.tex`,
`symmetric_metric_out/` (STLs, watertight, 14 closed pieces),
`symmetric_metric_compare.png`:
- outer shell EXACTLY C2-symmetric (corner error 0 by hard projection;
  facet flatness 9e-12, poke-out 8e-12); convex K5 with 9 facets
  (3 opposite pairs parallel-with-offset — benign, prism-like)
- 14/14 cells convex, exact tiling (shell vol == sum cell vol to 5e-9),
  genuine metric products (parallelism 0.0000 deg, parallelogram length
  mismatch 8e-11), min cell volume 8.2, min edge 0.21
- The C2 involution REVERSES all 21 outer path ascents — it is the
  geometric realization of the Tamari lattice's self-duality. Its axis is
  perpendicular to the fixed edge (222,442), which crosses it.
- residuals decay geometrically to 1e-10 at fixed weights => the constraint
  system is consistent (true solution, not a near-miss).

**Mirrors (inv#0, inv#2) resist realization**: same optimizer fails —
inv#0 stuck badly non-convex; inv#2 converges planarity but a parallelogram
collapses to zero width (length mismatch -> 1), suggesting a LENGTH
obstruction invisible to the direction-level necessary conditions. OPEN,
leaning infeasible.

**2-Tamari ground truth now implemented** (`tamari2_order.py`):
- labels decode as f-vectors: digits (f4 f3 f2) trimmed, f_i = #E before
  i-th N; 642 = (NEE)^4 = lattice MIN, 0 = N^4E^8 = MAX.
- the complex's 110 primitive edges == the 110 covering relations EXACTLY;
  14/14 cells are exactly the 2-Tamari intervals of their piece labels
  (piece label = "bottom-top").
- CORRECTION of an old claim: convex_product's x-axis is NOT a global
  Hasse functional (16/110 covers violated) — the old checklist item was
  the weaker per-cell unique-min/max property. BUT a strict global Hasse
  functional EXISTS for every realization (cone/extreme-ray test):
  original figure margin 0.025, convex_product c=(0.72,-0.35,0.60)
  margin 0.14, C2-symmetric c=(-0.31,0.95,0.00) margin 0.078. The
  symmetric one's functional is perpendicular to the C2 axis — forced,
  because the C2 reverses the order (rot-pi negates horizontal vectors).
- directed union-find confirms: all 15 forced parallel classes are
  Hasse-SIGN-consistent (parallelogram chains never force a cover up and
  another down along the same direction) — so metric products never
  combinatorially obstruct a poset drawing.
- gotcha: unsigned parallelism terms let DISTINCT classes accidentally
  align antiparallel in a converged solution (observed; harmless for the
  polytope but it can mask functional feasibility — always test the cone
  with the TRUE Hasse orientation from tamari2_order, not a proxy axis).

## 2026-07-16 (later): matching the "typical associahedron" (associahedron.fbx)

Goal: make the model resemble the classic textbook associahedron (gift for
F. Bergeron). `associahedron.fbx` = binary FBX (parser: `fbx_parse.py`) →
14 verts / 9 facets, full **D3d order-12** isometry group → exact match with
metric products is impossible (order ≥ 3 theorem above). How close can we get?

- `ref_match.py`: 12 combinatorial isos (all equivalent — ref fully symmetric);
  our C2 inv#6 IS one of the ref's three C2 rotations (rms 0). Horn machinery
  (jacobiN + quaternion) lives here.
- KEY INSIGHT: the metric-products variety is **GL(3)-invariant** (planarity,
  parallelism, translates, convexity, tiling are all affine-invariant), so
  gauge = AFFINE, not similarity. `affine_pin.py` pins in affine gauge.
- Pin-flow attempts (pin_to_reference.py: continuation + stiffening;
  project_from_ref.py: relax from ref shape) all land 16.5–19% from ref when
  the C2 constraint is kept — the C2 basin resists. Dynamics note: penalty
  flows here find the basin's natural point, NOT the constrained optimum.
- **Best result: drop hard C2, start from convex_product** →
  `affine_pin.py convex_product_coords.json 0 ...` → **10.30% of ref span**
  (affine rms), fully valid: 14/14 convex, products to 0.0000°, watertight,
  min edge 1.23 = 9.5% of span (vs 0.21 for the C2 model — much more
  printable), min cell volume 17.5, TRUE-Hasse functional margin 0.078.
- Deliverables: `typical_look_coords.json` (affine-mapped INTO the ref frame
  — valid because affine-invariance), `figure_typical_look.tex`,
  `typical_look_out/` STLs, `bergeron_gift_options.png` (ref vs typical-look
  vs C2-exact).
- OPEN follow-up: true constrained optimum via reduced parameterization
  (15 class directions + parallelogram-orbit lengths, corners linear in
  lengths, per-face closure+planarity) — would tell whether ~10% is optimal.

## OLD RESULT (superseded above): convex+products YES, symmetric+products NO (with proof)

The user's intuition was right on the first half and I had been wrong to doubt it:

**convex associahedron outer + genuine metric products is ACHIEVABLE.** `convex_product_coords.json`
is a clean convex K5 (9 flat facets, all convex-supporting to 1e-5) whose 14 cells are exact
metric products (parallel-edge spread 0.001°), watertight, all the lattice constraints hold.
It is just *skewed*, not symmetric.

**A SYMMETRIC associahedron outer + genuine metric products is impossible.** Clean structural
obstruction (iso-free, optimizer-free; see the feasibility scripts run this session):
1. Genuine metric products (parallelepipeds + prisms with parallel verticals) force edges to be
   parallel. Union-find on the cells' opposite-edge relations collapses the 21 K5 edges of the
   outer into **10 forced-parallel groups**, with sizes `[1,1,1,2,2,2,2,2,3,5]` — in particular
   **one group of 5 mutually-parallel edges** and one of 3. (No two of them share a corner, so
   they are realizable in a convex polytope — which is why the skewed `convex_product` works.)
2. The symmetric associahedron (secondary polytope of the regular hexagon, `tamari_symmetric.py`)
   has its 21 edges in **15 parallel classes of max size 2** (`[1×9, 2×6]`).
3. A forced group of 5 parallel edges cannot embed in a polytope whose largest parallel class is
   2. Under all 12 combinatorial K5-isomorphisms, ≥4 of the 10 forced groups map to non-parallel
   symmetric edges. So no symmetric realization can host these parallelepipeds.

Intuition: parallelepiped/prism cells demand long shared parallel directions; an associahedron
must be **stretched** along those directions to supply them, and that stretch is exactly what
breaks the D3 symmetry. Symmetry ⇒ generic edge directions (≤2 parallel) ⇒ no metric products.

### If symmetric outer is the priority — DONE (`symmetric_combo_out/`)
Dropping *metric* (parallelism) but keeping *combinatorial* products gives the user's full goal on
**Bergeron's exact 14-cell decomposition**. `symmetric_combo_coords.json` /
`figure_symmetric_combo.tex` / `symmetric_combo_out/` (verified this session):
- outer = **symmetric associahedron**: 14 corners identical to the symmetric-K5 vertices to 1e-6;
  9 facets flat through those corners to 7e-6; 3 square-facet normals mutually 60-60-60 (D3); convex
  (max poke-out +1e-5).
- 14 cells = **convex combinatorial products**: 4 cubes + 8 prisms + 2 K5 (14/14 convex), watertight
  (0 boundary edges), 14 closed solid STLs (cube=12 tri, prism=16, K5=24).
- **sublattices**: 14/14 cells are Tamari intervals (unique min & max under orientation c=(1,0,0));
  1-skeleton = 2-Tamari Hasse. Cubes rare (4/14).
- NOT metric products (parallelism given up by design — provably required, see above).

How it was built (the recipe that worked): the 12 combinatorial K5-isomorphisms include one with
**Horn corner-RMS = 0** — i.e. Bergeron's outer corners already ARE the symmetric K5 under a rigid
motion+scale. Horn-align figure.tex by that iso, then optimize **corner-pin to SV (w=50) + 9-facet
coplanarity (w 3→12 annealed) + per-face planarity (w=1), NO parallelism term**. Converges to
corner-pin 0, facet-flatness 0, planar 1e-4, 14/14 convex. (The earlier symmetric attempts failed
only because they kept the parallelism term, which fought the pinning, and/or used a bad iso.)

Also available: `tamari_k6/symm_*` (build_k6_hexfacet Schlegel) — symmetric K5 outer with convex
combinatorial product cells, but it's the 13-cell K6 decomposition, not Bergeron's 14-cell one.

VERIFICATION GOTCHA: `N.hull_facets` returns facet vertex *sets* NOT in polygon order — `newell()`
on them yields garbage normals. To get a facet plane, use the cross product of edges from 3
well-separated vertices, or order the polygon first.

### Optimizer pattern that works (for the convex+products realization)
Per-vertex 3×3 normal-equation solve combining (a) face-plane terms `n nᵀ` per incident face,
(b) parallelism terms `(I − u uᵀ)` per parallel-edge class (u = class direction, refit each iter),
(c) facet-group plane terms `n nᵀ` (n = averaged sub-face normal of the 9 facet groups), (d) small
λ regularization toward previous coords. Anneal the facet weight 3→12 over ~400 iters. Converges
to planar 2e-5, products 0.001°, facet-flatness 1e-5.

## Gotchas / facts learned
- ν-incompatibility (ν-trees) needs **strict** SW/NE in both coords (else counts wrong).
- Brick vector: tree pts = elbows, others = crossings; at each lattice pt (col-by-col,
  bottom-to-top) count pipes at levels `1..q` BEFORE the crossing; `b(T)_i = -(#pts below pipe i)`.
- numpy/scipy are BROKEN in this env (`libz.so.1` missing) — everything is pure-Python
  (brute-force hulls, Gram–Schmidt, 3×3 Cramer). matplotlib works.
- No PDF renderer available (pdftoppm/gs/convert all absent).
- The decomposition's 14 cells ↔ T4 (1-Tamari) via projection x→⌈x/2⌉ on ν-tree lattice points.
