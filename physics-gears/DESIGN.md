# DESIGN: Formalized 2D Physics Engine with Working Gears

Status: plan v1, 2026-07-24 (Fable + Danielle)
Board: phys-00 .. phys-15 (below)

## 1. Vision

A rigid-body physics engine where the claims are machine-checked, culminating
in *working gear mechanisms* — first as verified constraint joints, then as
emergent behavior from actual tooth-on-tooth contact between exactly-represented
gear profiles. Alongside it, a Lean/mathlib development of classical gear
theory (the involute, the law of gearing) that gives the engine's gear story
a continuous-mathematics foundation.

Why this workspace is unusually well positioned:
- Exact rational geometry with verified predicates already exists
  (verus-geometry orient2d/SAT ingredients, verus-rational, verus-linalg,
  verus-interval-arithmetic, verus-bigint).
- The certificate/trace-checker architecture is already proven out twice here
  (tactus nlsat trace-checking; GAP-2 emitters). We reuse the same philosophy:
  simulate with whatever solver pragmatics we like, then *verify a certificate
  about the produced state* with a proven checker.
- Long-term, an engine written as a Verus crate becomes a tactus flagship:
  its proofs discharge in Lean, and can eventually cite the Lean gear theory
  directly. Nothing here collides with the tactus critical path.
- The WHY: mechanisms are game material. A verified mechanism layer feeds the
  proof-factory game family (gears, linkages, escapements as puzzle pieces).

## 2. Architecture: three layers

```
L3  Lean/mathlib gear theory          (continuous ideal: involutes, law of gearing)
        |  approximation theorems (stretch, phys-15)
L2  Certificates & proven checkers    (per-step: non-penetration, momentum ledger,
        |                              restitution bounds, joint drift, ratio drift)
L1  Exact rational engine core        (Verus exec: bodies, contacts, joints, stepper)
```

**L1 — the engine** is executable Verus (plain Z3 workspace now, tactus-idiom
compatible). All *positions, shapes, velocities, impulses* are exact rationals.
Contact geometry uses exact predicates: no epsilon tuning, no "almost touching"
ambiguity — a first-class advantage over every floating-point engine.

**L2 — certificates** is where "formalized" gets teeth without requiring
research-grade proofs of solver convergence. The iterative contact solver is
NOT proven convergent (that is hard and partly false in general); instead every
step emits a state the *proven checker* validates:
- no interpenetration beyond tolerance (exact SAT/orient2d re-check),
- linear + angular momentum ledger balances exactly against applied impulses,
- per-contact restitution inequality holds,
- joint anchor drift within bound,
- (gear joints) ratio drift within bound.
A step that fails certification is rejected (halve dt / more iterations).
This is exactly the nlsat-oracle pattern: fast untrusted search, exact
verified check.

**L3 — Lean theory** is the continuous ideal the discrete engine approximates:
involute geometry and conjugate action. Independent repo, pure mathlib, no
tactus dependency — parallelizable with everything.

## 3. Key design decisions

### D1. 2D first
Gearing is essentially planar (spur gears). All the conceptual content —
exact contact, certificates, emergent meshing — exists in 2D at a fraction of
the cost. 3D is a later parallel-port (per house style: mechanical typed-copy
over premature genericity).

### D2. Rotation: exact rational unit vectors + certified snapping
The classic obstacle: integrating orientation θ += ω·dt and then needing
cos θ (irrational) for geometry. Resolution:

- A body's orientation is a **rational point on the unit circle**:
  `RotQ = (c, s) with c² + s² = 1`, both rational (type invariant, verified).
  These are dense on the circle (tan-half-angle parametrization: any rational
  t gives ((1−t²)/(1+t²), 2t/(1+t²))).
- Composition of two RotQ is exact and closed (angle-sum formulas are
  polynomial). Inverse is exact.
- Integration step: the true rotation by ω·dt is **snapped** to a nearby RotQ
  within 2⁻ᵏ (via interval-arithmetic enclosure of (cos, sin), then a
  rational circle point inside the enclosure — verus-interval-arithmetic does
  the enclosure; a small verified lemma certifies the snapped point's error).
- The per-step angle error is bounded and *accumulated in the certificate
  ledger*: after N steps the orientation is within N·2⁻ᵏ of the ideal.
  Positions/contacts are exact **given** the snapped orientations.

Slogan: **exact geometry, certified-approximate time integration.**
(Same story as dt-discretization error itself — snapping is just one more
certified discretization, not a soundness hole.)

### D3. Denominator hygiene
Exact rationals blow up under iteration (bigint denominators compound).
Same remedy, uniformly: periodic **certified rounding** — snap state to
bounded-denominator rationals with the error entered into the ledger.
Position snapping must re-verify non-penetration (cheap: it's the same
checker). This makes long simulations viable. (Experience base:
verus-mandelbrot perturbation + bigint arithmetic.)

### D4. Contact: convex polygons, frictionless first
- Shapes: convex rational polygons (+ unions of convex parts later).
- Detection: SAT with exact predicates; witness = separating axis (proof of
  disjointness) or deepest-penetration feature pair (proof of contact).
  Verified claim: the reported classification is correct. This reuses/extends
  verus-geometry.
- Resolution: impulse-based (sequential impulses), **frictionless + pin
  joints first**. Crucial scoping insight: *gear trains work frictionless* —
  gears transmit through tooth normal forces; friction is a loss term, not
  the mechanism. This dodges the Painlevé-paradox swamp entirely for the
  flagship demo. Friction (with its weaker guarantees) is a later, clearly
  fenced extension.

### D5. Gears twice: constraint-level, then emergent
- **Gear joint (phys-08):** constraint ω₁·r₁ + ω₂·r₂ = 0 (+ optional phase/
  backlash window). Cheap, robust; verified ratio-drift certificate. This
  gives "working gear mechanisms" early (gear trains, cranks, winches).
- **Emergent gearing (phys-10/11):** generate exact rational polygonal
  approximations of involute tooth profiles; mesh two such gears; drive one;
  the other turns *because the contact solver pushes teeth*. Certificate adds:
  contact maintained, no interpenetration, and the empirical ratio tracks
  −z₁/z₂ within a bound. This is the flagship demo and the novel artifact:
  I know of no verified-simulation demonstration of emergent gearing.

### D6. Solver honesty
Convergence of PGS/sequential impulses: not proven — checked (L2).
Multi-contact restitution can gain energy in exotic configurations: default
demos use e = 0 (perfectly inelastic contacts, which is also what real
gearboxes are); the energy ledger *monitors* rather than proves, and any
violation rejects the step. State plainly in docs what is proven vs checked
vs monitored. (Transparency = faithfulness.)

## 4. The Lean side (the part that can start today)

Independent repo `lean-gears` (pin manifest from lean-flocq per house recipe;
elan, not Nix lake; never bare `lake update`). Pure mathlib real analysis /
plane geometry. No tactus coupling — this is the "can some of it be done in
Lean while we finish tactus" answer: yes, this whole layer.

Theorem program, in dependency order:

- **G1 (involute basics).** γ(t) = r_b·(cos t + t sin t, sin t − t cos t).
  Prove: ‖γ(t)‖² = r_b²(1+t²); γ'(t) = r_b·t·(cos t, sin t).
- **G2 (string property).** The normal line to the involute at γ(t) is
  tangent to the base circle (it passes through the unwind point
  r_b·(cos t, sin t)). Direct from G1.
- **G3 (transmission lemma).** For two rigid profiles in tangent contact,
  the angular velocity ratio equals the ratio of the perpendicular distances
  from the two rotation centers to the common contact normal. (Rigid-body
  kinematics + tangency; the workhorse lemma.)
- **G4 (law of gearing / conjugate action).** Two involutes on base circles
  r_b1, r_b2: every contact normal is the common internal tangent of the base
  circles, hence a *fixed* line, hence by G3 the ratio is constant
  ( = −r_b2/r_b1 ), and it passes through the fixed pitch point on the center
  line. This is the crown theorem: *involute gears transmit uniform rotation.*
- **G5 (stretch).** Contact ratio ≥ 1 for standard proportions (existence of
  continuous drive); undercut/interference bound (z ≥ 2/sin²α for pressure
  angle α). Real analysis heavier; optional.
- **G6 (bridge, far-future).** Polygonal ε-approximation of involute ⇒ ratio
  deviation O(ε) bound — the theorem that would connect L3 to L1's emergent
  demo. Research-grade; explicitly not on any critical path.

Effort feel: G1–G2 are a pleasant week-scale warmup; G3–G4 the real project
(order weeks, mathlib-fluency dependent); G5+ open-ended. All of it is
independent of everything else in this plan.

## 5. Board

| Card | Deliverable | Depends |
|---|---|---|
| phys-00 | this DESIGN | — |
| phys-01 | crate `verus-physics2d` skeleton: `Body{pos: Vec2<Rational>, rot: RotQ, vel, omega, inv_mass, inv_inertia}`, `World`, fixed-dt step loop | — |
| phys-02 | `RotQ`: rational unit-circle type; verified invariant c²+s²=1, exact compose/inverse; `snap(angle_enclosure, k)` with certified 2⁻ᵏ error (uses verus-interval-arithmetic) | phys-01 |
| phys-03 | free-flight symplectic Euler; **proved:** exact conservation of linear & angular momentum for closed systems | phys-02 |
| phys-04 | convex rational polygons; SAT contact detection; **proved:** classification correctness with witness (axis or feature pair) | phys-01 |
| phys-05 | single-contact impulse; **proved:** momentum exchange exact, restitution inequality post-state | phys-03,04 |
| phys-06 | sequential-impulse multi-contact loop + **proven certificate checker** (non-penetration, ledgers); reject-and-retry stepping | phys-05 |
| phys-07 | revolute (pin) joint + drift certificate; certified rounding pass (D3) | phys-06 |
| phys-08 | gear joint (ratio constraint, ratio-drift certificate); **demo: gear train + crank** | phys-07 |
| phys-09 | trace JSON + tiny canvas viewer (unverified glue; maybe steal verus-canvas bits) | phys-06 |
| phys-10 | involute tooth polygon generator: exec, interval-arithmetic enclosures → exact rational vertices within stated ε of true involute (per-vertex certificate) | phys-02 |
| phys-11 | **flagship: emergent meshing** — two generated gears, one driven, contact does the rest; certificate: contact chain maintained, empirical ratio within bound of −z₁/z₂ | phys-06,10 |
| phys-12 | Lean G1–G2 (repo setup + involute basics + string property) | — (parallel) |
| phys-13 | Lean G3–G4 (transmission lemma, law of gearing) | phys-12 |
| phys-14 | Lean G5 stretch (contact ratio, undercut) | phys-13 |
| phys-15 | bridges: engine as tactus crate once B6/user-traits mature; Lean G6 approximation theorem | far-future |

Suggested first arc: phys-01 → 02 → 03 (a verified free-flight world with the
rotation story solved is already a milestone), with phys-12 as the Lean-side
palate cleanser whenever the mood is more mathlib than Verus.

## 6. Risks / open questions

- **R1 rational blowup** — mitigated by D3, but the certified-rounding pass is
  load-bearing; build it early (phys-07, could pull earlier if phys-03 demos
  already crawl).
- **R2 solver stalls** on tight gear meshes (many simultaneous tooth contacts)
  → reject-retry with smaller dt is the safety net; tooth count / clearance
  tuning is the practical fix. Backlash exists in real gears for a reason.
- **R3 emergent-mesh chatter**: polygonal teeth create contact flicker; e=0
  and modest polygonalization ε should tame it; if not, contact caching /
  persistent manifolds (standard engine tech, no verification novelty).
- **R4 Lean effort uncertainty** on G3–G4: mathlib has the analysis pieces
  (deriv, inner-product plane geometry) but "rigid contact of parametric
  curves" needs our own scaffolding. If it balloons, G1–G2 alone still stand
  as a publishable-nice artifact and the engine never blocks on it.
- **Q1**: escapement demo (anchor + pallets) after phys-11? It's the charisma
  demo — a ticking verified clock — and needs nothing beyond phys-11 tech.
- **Q2**: does the game-facing API want determinism guarantees across
  platforms? (Exact rationals give it for free — worth advertising.)

## 7. What is claimed, honestly

Proven: type invariants, conservation in free flight, contact-classification
correctness, per-step certificate soundness (if checker passes, the stated
inequalities hold of the produced state), tooth-vertex approximation bounds.
Checked-per-run: solver success, non-penetration, ledgers, ratio tracking.
Not claimed: solver convergence in general, energy correctness with e > 0,
anything about the continuous limit (until/unless G6).
