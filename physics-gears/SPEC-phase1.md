# SPEC: Phase 1 implementation (phys-01 .. phys-06, + phys-22 prismatic)

Companion to DESIGN.md v1.3. Written to be implementable by an agent without
re-deriving design intent. Where this SPEC and DESIGN conflict, SPEC wins for
phase 1. House rules apply: no `external_body`/`assume`/`admit`; no f32/f64
anywhere in the crate; check early with `verus_check` per module; helpers in
separate proof files; spec fns in dependency order; commit freely.

## 0. Crate & module layout

Crate `verus-physics2d`, depending on verus-rational, verus-linalg
(Vec2<Rational>), verus-geometry (orient2d etc. where reusable).

```
src/
  rotq.rs         phys-02   rotation type + tan-half constructor
  angle_ledger.rs phys-02   arctan alternating-series enclosures
  body.rs         phys-01   Body, BodyId, World state
  shape.rs        phys-04   ConvexPoly, Compound, transforms
  massprops.rs    phys-04   exact area/centroid/inertia
  broadphase.rs   phys-04   AABBs + sort-and-sweep, canonical pairs
  narrowphase.rs  phys-04   SAT + clipping → ContactManifold
  row.rs          phys-05   the ONE constraint row type (E1)
  solver.rs       phys-06   PGS over rows + position projection
  joints.rs       phys-07/22 revolute + prismatic → rows
  step.rs         phys-03/06 pure functional stepper, reject/retry
  certificate.rs  phys-06   StepCert + proven checker
  proofs/*.rs               lemma files (keep triggers isolated)
tests/scenes.rs             acceptance scenes below
```

All public exec fns carry requires/ensures; every `Vec` iteration order is
canonical (E6): bodies by index, pairs (i,j) with i<j sorted lex, rows in
fixed construction order (joints first, then contacts by (i,j,feature)).
No hash containers anywhere.

## 1. Core types (phys-01)

```rust
struct Body {
    pos: Vec2<Rational>,
    rot: RotQ,
    vel: Vec2<Rational>,
    omega: Rational,          // rad/time in ledger semantics
    inv_mass: Rational,       // 0 for static bodies — never divide by mass
    inv_inertia: Rational,    // 0 for static
    shape: Compound,
}
struct World {
    bodies: Vec<Body>,
    joints: Vec<Joint>,
    gravity: Vec2<Rational>,
    dt: Rational,             // default 1/240
    ledger: Ledger,           // accumulated enclosure widths, §3
}
```

World invariant (`open spec fn world_inv`): every body's RotQ invariant holds;
every shape invariant holds; dt > 0. The stepper is PURE (E3):

```rust
fn step(w: &World) -> (r: StepResult)   // StepResult = Ok(World) | Reject(Reason)
    requires world_inv(w)
    ensures  r is Ok ==> world_inv(r.world) && cert_ok(w, r.world)
```

Reject/retry policy (driver loop, not step itself): on Reject, halve dt for
that step only; give up below dt/16 of nominal and surface the reason.
Rollback is free because step is pure.

## 2. RotQ (phys-02)

```rust
struct RotQ { c: Rational, s: Rational }
// type invariant: c*c + s*s == 1
```

- `apply(v)` = (c·vx − s·vy, s·vx + c·vy). `compose(a,b)` = angle-sum
  formulas. `inverse()` = (c, −s). All exact; invariant preservation for
  compose is the identity (ac·bc − as·bs)² + (as·bc + ac·bs)² = (…)·(…) —
  prove via helper lemma with by(nonlinear_arith) on the expanded products
  (assert the two squared-norm bounds first, per house pitfall list).
- `from_tan_half(t: Rational) -> RotQ` = ((1−t²)/(1+t²), 2t/(1+t²)).
  Invariant proof hint: (1−t²)² + (2t)² == (1+t²)². Never divides by zero
  (1+t² ≥ 1).
- Integration step chooses t ≈ tan(ω·dt/2) **untrusted** (truncated series
  h + h³/3 + 2h⁵/15 at h = ω·dt/2, no correctness claim), then constructs
  RotQ exactly. §3 accounts for the angle actually applied.
- Composition growth → after compose, optionally re-snap through a fresh t
  (D3); the ledger entry covers it.

## 3. Angle ledger (phys-02) — the arctan alternating series (E2)

For rational t with |t| ≤ 1 define partial sums
A_k(t) = Σ_{j=0..k} (−1)ʲ t^{2j+1}/(2j+1). Alternating-series structure:
consecutive partial sums bracket; width of [A_{k+1}, A_k] (order by parity)
is t^{2k+3}/(2k+3).

- `applied_angle_enclosure(t, k) -> IntervalQ` returns that bracket for
  2·arctan(t): [2·A_odd, 2·A_even] with |width| = 2·t^{2k+3}/(2k+3).
  Verus proves: the interval endpoints are exactly these rational values,
  width formula, monotone shrink in k. (For |t| > 1 use
  arctan t = π/2 − arctan(1/t) — requires a π enclosure constant; phase 1
  restricts |ω·dt/2| small so |t| ≤ 1 always; assert it, reject-step if not.)
- The ledger entry for a step: interval `target = ω·dt` (exact rational, width
  0 — the *semantic* target) vs `applied ∈ applied_angle_enclosure(t, k)`;
  accumulated per body: `ledger.angle_err[i] += |applied − target|` as an
  interval-arithmetic upper bound (rational).
- **Semantic anchoring is NOT a Verus obligation.** Lean card **G0** proves
  once, over ℝ: A_k brackets arctan; tan-half parametrization covers the
  circle; angle-sum formulas. Verus only ever proves ledger *arithmetic*.

## 4. Shapes & mass properties (phys-04)

```rust
struct ConvexPoly { verts: Vec<Vec2<Rational>> }
// invariant: len ≥ 3, counter-clockwise, strictly convex
//   (orient2d(v[i], v[i+1], v[i+2]) > 0 for all i, cyclic; no repeated verts)
struct Compound { parts: Vec<ConvexPoly> }   // may overlap; union semantics
```

Exact mass properties (all rational, prove nonnegativity where claimed):
- area: A = ½ Σ cross(v_i, v_{i+1})   (cyclic; > 0 by ccw invariant)
- centroid: C = (1/(6A)) Σ (v_i + v_{i+1})·cross(v_i, v_{i+1})
- inertia about origin: I₀ = (1/12) Σ cross(v_i, v_{i+1}) ·
  (v_i·v_i + v_i·v_{i+1} + v_{i+1}·v_{i+1}); about centroid via parallel axis
  I_c = I₀ − A·|C|². Compound: sum parts (overlap double-counts — document:
  compounds SHOULD be disjoint-interior; not an invariant in phase 1).
Body construction takes density ρ (rational): mass = ρA_total,
inv_mass = 1/mass etc.; static bodies constructed with a flag instead.

Broadphase: world-space AABB per body (transform each vertex, min/max —
exact). Sort-and-sweep on x, emit candidate pairs (i<j), sort pairs lex.
No margin/prediction in phase 1 (dt small, speeds bounded by scene design).

## 5. Narrowphase: SAT + clipping (phys-04)

For world-space convex polys A, B (candidate pair):

1. For every edge (pᵢ, pᵢ₊₁) of A with outward normal n (right-hand ⊥ of the
   edge, exact, unnormalized is fine for signs but store the edge for later):
   sep(n) = min over verts q of B of dot(n, q − pᵢ). Same with roles swapped.
2. If any sep > 0 (strict, exact): **Separated**; witness = that axis.
   Verified ensures: the axis strictly separates (a forall over both vertex
   sets — this IS the proof, cheap).
3. Else **Touching/Penetrating**: reference feature = the (poly, edge) with
   maximum sep (ties: lower body index, then lower edge index). Incident
   edge = edge of the other poly whose outward normal has minimal dot with
   reference normal (ties: lower edge index). Clip incident edge segment
   against the two side half-planes of the reference edge (exact rational
   segment clipping); keep endpoints with sep ≤ 0 relative to reference
   face; result: 1 or 2 contact points.

```rust
struct ContactPoint { point: Vec2<Rational>, sep: Rational }  // sep ≤ 0
struct ContactManifold {
    a: BodyId, b: BodyId,           // a < b always
    normal: Vec2<Rational>,          // from A toward B, NOT normalized;
                                     // store n and |n|² — never sqrt
    points: Vec<ContactPoint>,       // len 1..=2, canonical order (lex)
    feature: (u32, u32),             // (ref edge, inc edge) for sorting
}
```

**No square roots anywhere.** Normalization is avoided by folding |n|² into
the effective-mass denominator (it's a ratio — stays rational). This is a
standing rule: any formula that seems to need |n| must be restructured to
use |n|² (they all can — velocities and impulses along unnormalized n just
rescale λ).

Verified ensures for the penetrating case (phase 1 scope): every reported
contact point lies on the reference face within the clipped span, and its
sep equals the exact point-to-face signed distance (times |n| — document the
scaling). Deeper completeness claims (e.g. "sep is THE max over all axes")
are stated but may land in phase 2; the certificate (§7) re-checks what it
needs independently, so solver correctness never depends on narrowphase
completeness.

## 6. Rows & solver (phys-05/06) — E1: one row type

```rust
struct Row {
    a: BodyId, b: BodyId,
    jla: Vec2<Rational>, jaa: Rational,   // J blocks for body a (linear, angular)
    jlb: Vec2<Rational>, jab: Rational,   // for body b
    lo: BoundQ, hi: BoundQ,               // BoundQ = Finite(Rational) | Inf
    bias: Rational,                        // velocity-level bias (0 in phase 1
                                           //   except restitution, e=0 default)
    lambda: Rational,                      // accumulated impulse
}
```

- Contact row (per contact point): J = [−n, −cross(rₐ, n), n, cross(r_b, n)]
  with r = point − body center; lo = 0, hi = ∞.
- Revolute joint: two rows (x, y anchors). lo = −∞, hi = ∞.
- Prismatic (phys-22): two rows — off-axis anchor drift + relative angle lock.
- Effective mass per row: mEff = jla·jla·inv_mₐ + jaa²·inv_Iₐ + (same for b);
  strictly positive whenever any endpoint is dynamic; a row with mEff = 0 is
  dropped at construction (both endpoints static — nothing to solve).
- PGS sweep, canonical row order, fixed iteration count N = 16:
  v_rel = J·v; Δ = −(v_rel + bias)/mEff; λ' = clamp(λ + Δ, lo, hi);
  apply (λ' − λ) through Jᵀ scaled by inverse masses. Exact rationals
  throughout; **denominator hygiene**: after the sweep, snap all velocities
  to denominator bound 2^K (K = 64 default) with ledger entries (D3/E5).
- Position projection pass (no Baumgarte, keeps energy story clean):
  after velocity solve + integration, re-run narrowphase; for each still-
  penetrating contact, translate bodies along n proportionally to inverse
  mass by β·pen (β = 1/2), M rounds (M = 4); joints similarly project anchor
  drift. Then final certificate check.

Integration order inside `step` (the precise pipeline):
1. apply external forces to velocities (gravity: v += g·dt)
2. build joint rows; broadphase; narrowphase; build contact rows
3. PGS N iterations; velocity snap (ledger)
4. integrate: pos += v·dt; rot = compose(rot, from_tan_half(t)) per §2/§3
5. position projection M rounds; position snap (ledger)
6. run certificate checker on (pre, post, cert); Ok or Reject

## 7. Certificate & proven checker (phys-06)

```rust
struct StepCert {
    rows: Vec<Row>,                  // final λ per row
    tan_halfs: Vec<Rational>,        // per body t used this step
    enclosures: Vec<IntervalQ>,      // per body applied-angle enclosure
    snaps: Vec<SnapEntry>,           // every snap: which quantity, |delta| bound
}
fn check_step(pre: &World, post: &World, cert: &StepCert) -> (ok: bool)
    ensures ok ==> step_certified(pre, post, cert)
```

`step_certified` (spec fn) is the conjunction of exactly these, each an exact
rational check, each its own lemma in proofs/:

C1 (momentum bookkeeping): for every body i,
    post.vel[i] == pre.vel[i] + g·dt + inv_m·(Σ over rows touching i of
    λ·J-block) + Σ snap deltas declared for i — an exact equality re-computed
    by the checker. Corollary lemma (proved once, not per-step): rows with
    a,b both dynamic transfer momentum equal-and-opposite, so for a closed
    system (no gravity, no statics, no snaps) total momentum is conserved
    exactly. Same shape for angular momentum about the origin.
C2 (bounds): every row's λ ∈ [lo, hi].
C3 (restitution/no-suck, e=0): for every contact row, post relative normal
    velocity ≥ −tol_v (tol_v: scene parameter, default 0 — exactness allows it).
C4 (non-penetration): re-run exact SAT on all broadphase pairs of post; every
    pair is separated or penetrating ≤ tol_p (default: 1/1000 of min body
    radius, rational). NOTE: checker calls narrowphase itself — it does not
    trust the solver's manifolds.
C5 (joint drift): every joint anchor error ≤ tol_j (exact).
C6 (ledger): every snap delta within its declared bound; angle enclosure
    widths ≤ per-step cap; accumulated ledger totals updated correctly.

The checker is the ONLY thing the engine's headline claims rest on (D8);
solver and narrowphase can be optimized freely without re-proof, and a
weaker implementing agent can even get C-obligations passing with a naive
solver first, then optimize.

## 8. Acceptance scenes (tests/scenes.rs)

Each card lands with its scene green (exact assertions, not approximate):

- S1 (phys-03): two bodies, zero gravity, initial velocities; 1000 steps;
  assert total momentum and angular momentum EXACTLY equal to initial
  (rational ==; snaps declared into the ledger are momentum-neutral by
  construction — snap velocity deltas must be recorded and the assertion is
  on the ledger-adjusted total).
- S2 (phys-02): body spinning at ω = 3 rad/s, 240 steps; assert RotQ invariant
  (implicit), assert accumulated enclosure width ≤ 240 · cap.
- S3 (phys-04): brute-force pair classification vs SAT on 200 fixed generated
  poly pairs (mix: separated / touching / overlapping; include parallel-edge
  and vertex-vertex cases); assert witness validity for every separated pair.
- S4 (phys-05): head-on equal-mass squares, e=0; after impact both velocities
  exactly equal (common velocity, momentum-preserving).
- S5 (phys-06): stack of 3 boxes on static ground, gravity; 2000 steps; no
  certificate rejection; final penetration ≤ tol_p; boxes asleep-still
  (|v| below threshold).
- S6 (phys-22): pendulum on revolute (energy monitored, drift ≤ tol_j) and
  block on prismatic rail with spring — oscillates, drift ≤ tol_j, exact
  spring potential appears in energy ledger.

## 9. Phase-1 non-goals (do not let the implementing agent wander)

No friction. No restitution > 0. No warm starting. No sleeping/islands
(S5's "asleep" is just a velocity check). No continuous collision. No
compound-overlap invariants. No profile generators (that's phys-10a).
No 3D. No performance work beyond denominator hygiene.
