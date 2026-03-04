# VerusCAD Roadmap

High-level plan for getting from where we are to a fully functional,
formally verified CAD program (think: verified Onshape).

---

## Where we are now

The project has been split from a monolithic ~70K-line prototype (`old/VerusCAD`)
into clean, independently-verified crates:

| Crate | Lines | Verified items | Status |
|---|---|---|---|
| **verus-bigint** | ~4,200 | 346+ | Production -- signed/unsigned arbitrary-precision ints |
| **verus-rational** | ~1,780 | 689+ | Production -- exact rationals, full algebraic library |
| **verus-geometry** | ~1,200 | 29 | Stable -- orient2d/orient3d, proven with 0 assumes |
| **verus-linalg** | ~90 | 195+ | Stable -- generic Vec2/Vec3/Vec4/Mat3 over any Ring |
| **verus-interval-arithmetic** | ~5,300 | WIP | Phase 2 done, Phase 3 (15 correctness lemmas) in progress |

The old monolith also contains a substantial **half-edge topology** layer
(~38K lines) and **quaternion rotation** support that can be mined.

### Per-crate planning docs

Every crate has detailed TODO documentation with phased implementation plans,
proof difficulty estimates, and milestones:

| Crate | Planning docs |
|---|---|
| **verus-algebra** | `docs/TODO.md` — IntegralDomain, GCD, polynomials, Module/VectorSpace traits |
| **verus-bigint** | `docs/` (12 files) — zero-trust roadmap, per-module proof tasks, trust assumptions |
| **verus-rational** | `docs/` (3 files) — downstream proof reuse, runtime rational tasks |
| **verus-linalg** | `docs/TODO.md` — Mat2x2/Mat4x4, matrix inverse, quaternions, affine transforms |
| **verus-geometry** | `docs/TODO.md` — sign extraction, collinearity, sidedness, intersection predicates |
| **verus-interval-arithmetic** | `TODO.md` + `CORRECTNESS_PROOFS_PLAN.md` — Phases 0-8 complete, 15 correctness lemmas in progress |
| **verus-topology** | `docs/TODO.md` — half-edge mesh, structural invariants, Euler operators, genus tracking |

---

## The layers we need

A CAD system like Onshape is roughly this stack, bottom to top:

```
 7. UI / collaboration          ← web frontend, real-time sync
 6. Feature timeline            ← parametric history, rollback, branching
 5. Modeling operations         ← extrude, revolve, fillet, chamfer, boolean, shell, draft ...
 4. Constraint solver           ← 2D sketch constraints + 3D assembly mates
 3. Geometric kernel            ← BREP evaluation, NURBS/subdivision surfaces, intersection
 2. Topology                    ← half-edge / cell-complex, Euler operators, genus tracking
 1. Exact arithmetic & geometry ← bigint, rational, interval, predicates, linear algebra
```

Layer 1 is largely done. Everything else needs work.

---

## Phase 1 -- Finish the arithmetic foundation

**Goal:** Rock-solid, zero-assume numeric stack.

- [ ] **verus-interval-arithmetic Phase 3** -- land the 15 correctness-proof lemmas
      (scale identities, mul edge cases, associativity, monotonicity, subdistributivity)
- [ ] **verus-interval-vectors** -- interval-valued Vec2/Vec3 with verified containment,
      built on top of verus-interval-arithmetic + verus-linalg
- [ ] **verus-bigint zero-trust migration** -- finish the 40K-line roadmap to minimize
      trusted surface
- [ ] **Float-to-interval bridge** -- verified conversion from f64 input to exact interval,
      so the rest of the pipeline stays exact

**What this buys us:** Every number in the kernel carries a machine-checked proof
that the true value lies in the computed interval. No silent precision loss, ever.

---

## Phase 2 -- Topology

**Goal:** A verified half-edge (or cell-complex) mesh that can represent any
manifold solid.

- [ ] **Port vcad-topology** -- extract the 38K-line half-edge mesh from the old monolith
      into a standalone `verus-topology` crate, cleaning up to match the new crate style
- [ ] **Euler operators** -- implement and verify the six Euler operators
      (make-vertex-face-solid, kill-vertex-face-solid, etc.) as the *only* way to mutate
      topology. Prove each one preserves the Euler-Poincare invariant
      (`V - E + F = 2(S - G) + R`).
- [ ] **Topological invariants as types** -- encode manifoldness, orientability, and
      closure as type-level predicates so that downstream code can require them in specs

**What this buys us:** Any solid produced by the kernel is *proven* to be a valid,
closed, oriented manifold. Entire classes of bugs (self-intersection, dangling edges,
non-manifold geometry) are eliminated at compile time.

---

## Phase 3 -- Geometric kernel (BREP)

**Goal:** Evaluate boundary representations -- the core of any solid modeler.

- [ ] **Curve types** -- line segments, circular arcs, conics, rational B-splines (NURBS).
      Each curve carries a verified parameterization and containment proof.
- [ ] **Surface types** -- planes, cylinders, cones, spheres, tori, NURBS surfaces.
      Same deal: verified parameterization, normal orientation, containment.
- [ ] **Curve-curve intersection** -- verified intersection routines using interval
      Newton or subdivision. Output is either exact (for algebraic cases) or an interval
      that provably contains every intersection point.
- [ ] **Curve-surface / surface-surface intersection** -- the hard one. Interval
      methods + marching + singularity handling, all with containment proofs.
- [ ] **BREP evaluation** -- given topology + geometry, verify that every edge lies on
      its adjacent faces' surfaces, every face is bounded by its wire, and the whole
      thing is watertight.
- [ ] **Tessellation** -- verified mesh generation for visualization. Prove that the
      output mesh is within epsilon of the true surface.

**What this buys us:** A geometric kernel where every intersection, trim, and
evaluation is machine-checked. This is the heart of the CAD system.

---

## Phase 4 -- Modeling operations

**Goal:** The user-facing operations that make a CAD tool useful.

- [ ] **2D sketch primitives** -- lines, arcs, circles, splines, dimensions, construction geometry
- [ ] **2D constraint solver** -- geometric constraint satisfaction (coincident, parallel,
      perpendicular, tangent, equal, fix, symmetric ...). Prove that the solver either
      finds a solution consistent with all constraints or correctly reports failure.
- [ ] **Extrude** -- blind, symmetric, up-to-face, up-to-surface. Prove output is valid BREP.
- [ ] **Revolve** -- same treatment as extrude but around an axis.
- [ ] **Boolean operations** -- union, intersection, subtraction. The classic hard problem.
      Prove correctness of face classification and topology reconstruction.
- [ ] **Fillet / chamfer** -- rolling-ball fillet with verified offset surfaces.
- [ ] **Shell** -- offset all faces inward/outward, prove watertightness.
- [ ] **Draft** -- tilt faces relative to a pull direction.
- [ ] **Loft / sweep** -- interpolate between cross-sections along a spine.
- [ ] **Pattern** -- linear, circular, and mirror patterns with proven periodicity.

**What this buys us:** A parametric modeling language comparable to Onshape's
feature set, where every operation is proven to produce valid geometry.

---

## Phase 5 -- Feature timeline & parametrics

**Goal:** Onshape-style parametric history tree.

- [ ] **Feature graph** -- DAG of modeling operations with typed inputs/outputs.
      Each node is a verified operation from Phase 4.
- [ ] **Rollback / replay** -- re-evaluate from any point in history. Prove that
      replay is deterministic (same inputs => same outputs, always).
- [ ] **Parameter propagation** -- change a dimension, re-solve constraints,
      regenerate downstream features. Prove that the regeneration terminates
      and respects the dependency order.
- [ ] **Configurations / variants** -- branch the feature tree for design variants.
- [ ] **Persistent naming** -- stable references to faces/edges/vertices across
      regeneration. Prove that names are consistent after topology changes where
      possible, and that failures are reported (not silent mismatches).

**What this buys us:** A parametric system where "rebuild" is guaranteed to
terminate, be deterministic, and flag any topology changes that break references.

---

## Phase 6 -- Assemblies

**Goal:** Multiple parts assembled with mates/constraints.

- [ ] **Assembly constraint solver** -- fasten, revolute, slider, cylindrical, planar,
      ball-joint, parallel, gear-ratio. Prove DOF accounting is correct.
- [ ] **Interference detection** -- verified spatial query (BVH + exact predicate
      refinement) to detect collisions between parts.
- [ ] **Mass properties** -- verified volume, surface area, center of mass, moments
      of inertia computed from BREP. Prove correctness against the integral definition.

---

## Phase 7 -- UI & collaboration

**Goal:** Make it usable by actual humans.

- [ ] **Rendering pipeline** -- tessellated BREP -> GPU. The tessellation is verified
      (Phase 3); the rendering itself is unverified but isolated behind a clean API.
- [ ] **Interaction layer** -- sketch on face, click-to-select, dimension dragging.
      Unverified UI code, but every mutation goes through the verified kernel.
- [ ] **File format** -- import/export STEP, IGES, or a native format. Verify round-trip
      fidelity where practical.
- [ ] **Collaboration** -- multi-user editing (CRDT or OT on the feature tree).
      The merge semantics are interesting to verify; the networking is not.
- [ ] **Web deployment** -- WASM compilation of the verified kernel + WebGPU frontend.

The verification boundary is clear: **everything below the UI is verified,
the UI itself is not** (and doesn't need to be -- it's just a view).

---

## What to verify vs. what not to

The point isn't to verify everything. It's to verify the parts where bugs are
catastrophic and hard to find:

| Verify | Don't verify |
|---|---|
| Arithmetic correctness | GPU rendering |
| Topological validity | UI layout / interaction |
| Geometric intersection | Networking / sync protocol |
| Constraint solver soundness | File parsing (fuzz instead) |
| Boolean operation correctness | Syntax highlighting |
| Feature replay determinism | Undo/redo UI state |

The unverified parts are isolated behind narrow interfaces so that bugs there
can't corrupt the verified core.

---

## Rough ordering & dependencies

```
Phase 1 (arithmetic)
  |
  v
Phase 2 (topology) ----+
  |                     |
  v                     v
Phase 3 (kernel) --> Phase 4 (operations)
                        |
                        v
                   Phase 5 (parametrics)
                        |
                        v
                   Phase 6 (assemblies)
                        |
                        v
                   Phase 7 (UI)
```

Phases 1 and 2 can proceed in parallel. Phase 3 needs both.
Phase 7 can start early as a thin shell over mock geometry for iteration.

---

## Open questions

- **NURBS vs. subdivision surfaces** -- NURBS is the industry standard but hard to
  verify (rational polynomial evaluation, knot insertion). Subdivision surfaces
  (Catmull-Clark, Loop) are simpler to reason about. Hybrid approach?
- **Constraint solver architecture** -- Newton-Raphson with verified convergence?
  Symbolic (Grobner basis)? Graph-based decomposition?
- **How much of vcad-topology to reuse vs. rewrite** -- the old code is big and
  uses a different style. May be faster to rewrite with the new crate conventions.
- **Performance** -- exact arithmetic is slow. Interval arithmetic with adaptive
  precision (start with floats, refine to rationals only when needed) is the
  standard trick. Need to design this so the proofs compose cleanly.
- **What's the MVP?** -- a reasonable first milestone might be: sketch -> extrude ->
  boolean -> fillet on a single part, with full verification. That's enough to
  demonstrate the concept and is probably Phases 1-4 with a minimal subset of
  operations.
