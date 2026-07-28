# DESIGN: Formalized 2D Physics Engine with Working Gears

Status: plan v1.5, 2026-07-28 (Fable + Danielle) — v1.1 adds weird-gear
generalization (D6/D7, phys-16..21, Lean G7/G8); v1.2 adds cams
(D6/D7 extended, D8 follower-jump honesty, phys-22..25, Lean G9);
v1.3 adds elegance revisions E1..E6 (§3.5) + SPEC-phase1.md (precise
implementation spec for phys-01..06 & 22) + Lean G0 + phys-10 split;
v1.4: phys-01..04 LANDED (see "Implementation status" below) — board
updated, deviations recorded (E7 global convexity, raw predicates);
v1.5: signed-enclosure debt RESOLVED + design-review decisions
(§3.7: ledger two-source bound D9, canonicalize D10, calc! D11,
local→global convexity D12; rejected options recorded).
Board: phys-00 .. phys-25 (below)

## Implementation status (v1.4, 2026-07-25)

Landed in `verus-physics2d` (full crate green):

- **phys-01** (07b3f14): crate skeleton — Scalar/SVec2 aliases, RotQ with
  unit-norm invariant + identity, Body wf + static/dynamic ctors, World.
- **phys-02** (a31597b, 4bc8c6d): RotQ apply/compose/inverse/from_tan_half
  with invariant proofs via INTEGER cross-multiplication (no reals — real
  NLA diverges Z3 in this toolchain); arctan angle ledger with exact
  endpoints, width formula, term-decreasing, odd/even bracket monotonicity,
  enclosure nesting; exact exec evaluators.
- **phys-03** (401e3fe): free-flight symplectic Euler (pure step fn with
  reject-on-|t|>1 and a Some-guarantee contract), E2 ledger accumulation
  2·|term_{k+1}(t)| per body per step, exact zero-gravity conservation of
  total linear AND angular momentum (the cross(pos+v·dt, v) telescope),
  scenes S1 (1000-step momentum) and S2 (240-step spin ledger) proven
  statically.
- **phys-04** (f8ad2d5): ConvexPoly with the GLOBAL convexity invariant
  (E7 below) + nlsat-style checked constructor; SAT classifier whose
  Separated verdict proves the witness axis strictly separates both vertex
  sets (min-attainment + dot = −orient, which is fully structural on
  Rational); Touching proves no-axis-separates and carries the max-sep
  reference feature; scene S3 (k-family of square pairs incl. touching/
  vertex-vertex/parallel-edge, classification proven equal to known
  answers).
- **Signed enclosure** (a0ae4c9, 7c73aed): the v1.4 debt RESOLVED — the
  series is odd, mirror equalities are structural, `angle_enclosure_signed`
  ordered on [−1,1] with uniform width 2·|term|; `step_free_flight`
  accepts |t| ≤ 1; scene S2-mirror (ω = −3) green.
- **phys-05a** (26fc8c7): exact mass properties — shoelace ≡ fan-sum
  identity, area2 > 0 via the global invariant, exact centroid/inertia
  evaluators; scene M1 (unit square: area2 == 2, centroid == (1/2,1/2),
  I₀ == 2/3). Inertia nonnegativity deferred (see §3.7c).
- **phys-05b** (5541b32): world-space transforms (exact RotQ-apply),
  AABBs with coordinate-fold vertex bounds, disjoint-ranges ⇒
  pointwise-separation soundness, canonical broadphase pair list ==
  spec filter. Deviation: O(n²) filter, no sort-and-sweep (identical
  guarantees at phase-1 sizes; C4 re-checks all pairs anyway).

Deviations from v1.3 text (they amend SPEC where they conflict):

- **E7. Global convexity invariant.** ConvexPoly's invariant is the global
  form — every vertex on the inner side of every edge (orient ≥ 0, strict
  for non-endpoints) — not the local consecutive-turn form of SPEC §4.
  Construction is nlsat-style: producers are untrusted, a checked
  constructor verifies the invariant at runtime. The local→global
  convexity lemma (consecutive positive turns suffice) is deferred; the
  global check is the construction-time authority.
- **Raw predicates.** shape.rs defines its own raw-form orient/edge_normal/
  axis_sep/min_sep instead of reusing verus-geometry's Point2/orient2d:
  the geometry crate's trait-op predicates on its own types cost more in
  conversion glue than they save. All polygon algebra runs on the
  integer cross-multiplication discipline (SPEC addendum A1).
- **World carries the ledger.** World has `series_k` and per-body
  `angle_err` fields (SPEC §1's `ledger: Ledger` made concrete).
- **Signed-enclosure debt — RESOLVED (2026-07-28).** The arctan bracket
  lemmas now cover the full [−1, 1]: the series is odd, and the mirror is
  structural (term/sum/enclosure negation are `==`, not just `≡`), so the
  negative-t endpoints come out swapped. `angle_enclosure_signed` restores
  a uniform ordered enclosure with uniform width 2·|term_{k+1}|
  (`lemma_angle_enclosure_signed_ordered/_width`, `lemma_arctan_term_abs_bound`).
  `step_free_flight` accepts |t| ≤ 1 (scene S2-mirror, ω = −3, green).
  This was the last phys-06 blocker on the ledger side (C6).

Proof-engineering addendum (recorded in workspace AGENTS.md and
proofs/rational_raw.rs header): the NLA discipline R1–R5, ghost-let
opacity to `by(nonlinear_arith)`, and exact body-form
(`x.denom_nat() as int`) unfold staging. All of phase 1 was verified
under this discipline.

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

### D6. Coupling joints: transmission functions over any coordinates
The constraint-level gear joint (D5) generalizes twice. First, from a constant
ratio to a **transmission function**: q₂ = f(q₁) with i = f' given as a
rational piecewise function (piecewise-polynomial / rational spline,
exact-evaluable). Second, from angles to **any pair of generalized
coordinates** — revolute angle or prismatic slide position:
- angle→angle, constant i        → ordinary gears
- angle→angle, periodic varying i → elliptical / oval / square / nautilus
- angle→angle, dwell spans (i = 0) → Geneva drives, mutilated gears
- angle→slide, linear f          → rack and pinion
- angle→slide, programmed rise-dwell-return f → **cams as constraints**
  (any motion law: uniform, parabolic, 3-4-5 polynomial exactly; SHM /
  cycloidal laws via certified enclosure like D2)
- inequality coupling (one-way) → ratchets, freewheels, overrunning clutches
One joint type + one certificate (|q₂ − f(q₁)| ≤ tol, exact since f is
rational) covers the constraint-level zoo of gears AND cams. Requires the
prismatic joint primitive (phys-22).

### D7. Generalized profile pipeline (emergent weird gears)
The emergent path factors into: **pitch-curve pair → conjugate tooth profile →
certified polygonalization → contact engine**. The contact engine (phys-04/06)
is shape-agnostic — a gear is just a non-convex union of convex rational
pieces — so weirdness lives entirely in the generator:
- **Non-circular pitch pairs**: rolling centrodes r₁(φ)+r₂(φ) = d with the
  no-slip rolling condition; realize any smooth periodic i(φ). Closure needs a
  rationality condition on ∫ i dφ (see Lean G7). Use rational-parametrized
  pitch curves (conics / rational Béziers) to stay in exact land.
- **Conjugate flanks**: generated as envelopes of the mating profile under
  relative rolling motion (Camus / Euler–Savary). Numerically approximated,
  then *certified pointwise* like the involute (phys-10's machinery, reused).
- **Pin / lantern gears** (cycloidal clockwork): the pin wheel's teeth are
  literal circles — **exactly rational, zero approximation** — only the mating
  cycloidal flank needs certified polygonalization. Likely the *cheapest*
  emergent demo, possibly ahead of involute.
- **Internal / ring gears**: concave contact — handled since gears are already
  non-convex unions; enables planetary trains.
- Ratchet-and-pawl, mutilated gears, Geneva pin-and-slot, escapements: no new
  theory at all — they are contact mechanisms the solver handles for free once
  non-convex unions work. They're demo cards, not tech cards.
- **Cams, emergent** (phys-24/25): same pipeline, different synthesis input —
  a displacement law s(θ) instead of a mating gear. Profile = envelope/offset
  construction per follower type (knife-edge: pitch curve directly; roller:
  inner offset by roller radius; flat-face: envelope of face lines), then the
  same certified polygonalization. Pressure-angle and undercut checks
  (ρ ≥ r_roller; flat-face ρ = r_b + s + s'' > 0) run at generation time.
  Exactness sweet spot: circular-arc / tangent cams — profiles built from
  lines and arcs, the cam-world analogue of lantern gears. Closure both ways:
  force-closed (spring, phys-22) and form-closed (groove/track cams,
  constant-breadth pairs, conjugate cam pairs — non-convex unions again).
- Linkages (four-bar, slider-crank, Peaucellier…) come **free** with
  revolute + prismatic joints — noted as demo material, zero new tech.
Explicitly deferred: 3D-only types (helical, bevel, worm, hypoid; barrel and
face cams) and flexible drives (belts, chains) — the latter need
distance-constraint tech, noted as a future extension, not smuggled in.

### §3.5 Elegance revisions (v1.3) — these OVERRIDE earlier text where they conflict

- **E1. One constraint-row type.** Contacts, revolute/prismatic anchors,
  gear/cam couplings, ratchets: all become rows {J, λ_lo, λ_hi, bias}.
  Bounds encode the type (unilateral [0,∞), bilateral (−∞,∞), one-way).
  One PGS update, ONE certificate-validation lemma. See SPEC §6.
- **E2. Arctan-ledger integration.** Replace D2's "snap via cos/sin
  enclosure": the step picks a rational tan-half t (untrusted truncated
  series), builds the exact on-circle RotQ, and the certificate encloses the
  applied angle 2·arctan(t) by alternating-series partial sums (rational,
  self-bracketing) against the target ω·dt. Untrusted search, verified
  check — inside the integrator. See SPEC §3.
- **E3. No-reals discipline + Lean G0.** Verus specs never mention real
  numbers: they maintain rational enclosures and prove ledger arithmetic.
  A small Lean file (G0) anchors, once over ℝ: arctan partial-sum
  bracketing, tan-half circle coverage, angle-sum identities. This is the
  clean Verus/Lean division and dissolves "how do we state angle error
  without ℝ" entirely.
- **E4. Generator trust split.** phys-10 splits: **phys-10a** untrusted
  profile generator (float allowed OUTSIDE the verified crate, emits exact
  rational vertices) — unblocks flagship demos immediately, because engine
  certificates are about whatever polygons exist; **phys-10b** certified
  profile-to-ideal ε bounds — only needed for the L3 bridge (G6). phys-11/18
  depend on 10a only.
- **E5. One snap primitive.** Rotation re-snapping and denominator rounding
  are the same operation: replace a quantity by a nearby bounded-denominator
  one, emitting a ledger entry with an exact |delta| bound. One concept, one
  entry type, uniform in the certificate (C6).
- **E6. Canonical determinism.** Every iteration order is canonically sorted
  (bodies by index, pairs lex, rows by construction order). No hash-order
  iteration anywhere. Exactness + canonical order = bit-identical replays
  across platforms — free determinism guarantee (answers Q2 affirmatively).

### D8. Solver honesty
Convergence of PGS/sequential impulses: not proven — checked (L2).
Multi-contact restitution can gain energy in exotic configurations: default
demos use e = 0 (perfectly inelastic contacts, which is also what real
gearboxes are); the energy ledger *monitors* rather than proves, and any
violation rejects the step. State plainly in docs what is proven vs checked
vs monitored. (Transparency = faithfulness.)

Cam-specific honesty: a **force-closed** cam only tracks its motion law while
the required contact force stays ≥ 0 — at speed, real followers *jump*, and
the engine models that truthfully (the contact simply opens; unilateral
contacts never pull). So tracking certificates are claimed unconditionally
only for form-closed cams and for the constraint-level joint; for force-closed
emergent cams the certificate is conditional ("tracks while contact force
≥ 0") and follower jump is a *correct physical outcome*, not an error.

### §3.7 Design-review decisions (v1.5, 2026-07-28) — OVERRIDE earlier text where they conflict

From a full review after the signed-enclosure + phys-05a/b sessions
(context: closed-eval discipline and structural-mirror lessons, recorded
in memory/). Rejected options are recorded with their reasons — do not
revive them without engaging the reason.

- **D9. The angle ledger is a TWO-SOURCE bound (corrects E2's accounting).**
  `|applied − target| = |2·arctan(t) − ω·dt|` has two independent parts:
  the arctan series-truncation (enclosure width, k-tunable) and the tan
  chooser's own truncation (`tan(h) − series₅(h) ≈ 17h⁷/315`, NOT
  k-tunable). The width alone does NOT upper-bound the total — near
  h = 1/2 the tan remainder exceeds the k = 8 width by orders of
  magnitude, so the old reading ("accumulated width bounds the angle
  error") was wrong. Resolution: enclose tan first — `[t_lo, t_hi]`
  around `tan(α/2)` with certified rational remainder `R·h⁷`
  (R ≈ 1/16 on [0, 1/2]) — then the arctan enclosure of the endpoints
  contains the target BY CONSTRUCTION (arctan is 1-Lipschitz). The
  ledger increment becomes enclosure width + R·h⁷, all rational
  arithmetic on the Verus side. **G0 grows one theorem**: tan Taylor
  remainder with rational constant. Fallback if the remainder proof
  balks: demote the ledger to D8's *monitored* category and drop the
  "within N·ε of ideal" headline.
- **D10. `canonicalize()` via checked constructor; NOT normalize-on-write.**
  Denominator blowup in the PGS sweep is a real phys-06 viability risk,
  but normalize-on-write was rejected: it flips every `out@ == op_spec`
  ensures to eqv-form and destroys the structural-`==` discipline that
  makes mirror/closed proofs cheap. Instead: an explicit value-preserving
  canonicalize op — untrusted reducer proposes `(num', den')`, the
  constructor CHECKS `num'·den == num·den'` (one exact multiply, no gcd
  proof — the nlsat pattern), eqv-form seams only at rare explicit call
  sites (step boundary, optionally between PGS iterations). No ledger
  entry (value unchanged; snap remains the ledgered, value-CHANGING
  primitive). **Fixed-point solver core** (global 2^K denominator via
  verus-fixed-point) recorded as a phys-06+ evaluation, not a
  prerequisite: adds exact, muls round with E5 ledger entries.
- **D11. `calc!` for eqv chains; normalized-rational spec ops rejected.**
  A computable gcd-normalize inside spec `add_spec`/`mul_spec` would make
  eqv collapse to `==`, but at the cost of a recursive-euclid unfold at
  EVERY op in EVERY proof plus a verus-rational refactor — rejected.
  The eqv discipline is right for this toolchain; the ergonomic fix is
  `calc!`-style eqv chains (already used inside verus-rational) as house
  style, plus hoisting shared helpers (the q_* bridge pack, closed-eval
  `*_closed_int` lemmas) into shared modules. Standing spec-design rule:
  prefer forms whose symmetry laws hold STRUCTURALLY (the sign-blind
  `den` made the mirror proofs nearly free) — that rule, not
  normalization, is where the savings are.
- **D12. Local→global convexity before phys-10a; generators emit
  turn-signs.** The O(n²) global invariant (E7) stays as the proof-facing
  form, but construction moves to the O(n) consecutive-turn check once
  the local→global lemma (consecutive positive turns ⇒ global convexity,
  a sweep argument) lands — scheduled BEFORE phys-10a makes gear-scale
  polygons urgent. phys-10a's profile generator additionally EMITS the
  local-turn signs as a convexity certificate (nlsat pattern for shapes).
  Fan-positivity as a cheaper invariant was explicitly rejected: it is
  star-shapedness, strictly weaker than convexity, and SAT is unsound
  for non-convex inputs.
- **Also folded in:** (a) `StepResult = Ok | Reject(Reason)` replaces
  `Option` (SPEC §1 already said this; the code catches up), and
  `Body.shape` + `World.joints` land in the SAME phys-05c datatype
  change — one crate-wide cache invalidation, not three. (b) S4 goes
  through the certificate: run one single-contact-impulse step, verify
  C1–C4 on the produced state — that IS D8, and it de-risks the phys-06
  checker early. (c) Inertia nonnegativity via the fan decomposition
  (same telescoping shape as area; per-triangle dot-sum is a
  sum-of-squares form) scheduled before phys-06 so the density
  constructor is principled. (d) `angle_enclosure_signed` becomes the
  standard API; the parity-ordered `angle_enclosure` becomes internal.
  (e) `verus-rational/src/rational/applications.rs.bak` to be deleted.

## 4. The Lean side (the part that can start today)

Independent repo `lean-gears` (pin manifest from lean-flocq per house recipe;
elan, not Nix lake; never bare `lake update`). Pure mathlib real analysis /
plane geometry. No tactus coupling — this is the "can some of it be done in
Lean while we finish tactus" answer: yes, this whole layer.

Theorem program, in dependency order:

- **G0 (enclosure anchoring, small but load-bearing).** Over ℝ: arctan
  alternating partial sums bracket arctan on [0,1]; tan-half-angle
  parametrization ((1−t²)/(1+t²), 2t/(1+t²)) covers the unit circle with
  angle 2·arctan t; angle-sum formulas. This is the ONLY place the engine's
  ledger semantics touch real numbers (E3); everything the Verus side proves
  is rational arithmetic whose reading G0 fixes. Mathlib has all
  ingredients; days, not weeks.
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
- **G7 (non-circular closure).** Rolling-centrode pair for a smooth periodic
  transmission function closes into two closed curves iff the total turning
  over one period satisfies a rationality condition (∮ i dφ commensurate with
  2π). Concrete instance: closure for the elliptical pair. This is the
  theorem that says *which* weird gears can exist as closed wheels.
- **G8 (generalized law of gearing — Willis).** Profiles are conjugate for
  transmission function f iff every contact normal passes through the
  *instantaneous* pitch point (dividing the center line in ratio i(φ₁)).
  G4's involute law becomes the constant-i special case. The moving-pitch-
  point statement is the true crown of the Lean program; do G4 concretely
  first, then generalize.
- **G9 (cam theory).** For a flat-faced follower, the cam profile is the
  envelope of the follower face lines; its radius of curvature is
  ρ(θ) = r_b + s(θ) + s''(θ), and the profile is valid (no cusp/undercut)
  iff ρ > 0 everywhere. Companion: the roller-follower pressure-angle
  formula tan α = s'/(r_b + s) (radial translating case) and the undercut
  condition ρ_pitch ≥ r_roller. Self-contained plane-curve/envelope work,
  independent of G3–G8; a good mathlib envelope-machinery warmup for G8.

Effort feel: G1–G2 are a pleasant week-scale warmup; G3–G4 the real project
(order weeks, mathlib-fluency dependent); G5+ open-ended. All of it is
independent of everything else in this plan.

## 5. Board

| Card | Deliverable | Depends |
|---|---|---|
| phys-00 | this DESIGN | — |
| phys-01 ✅ | crate `verus-physics2d` skeleton: `Body{pos: Vec2<Rational>, rot: RotQ, vel, omega, inv_mass, inv_inertia}`, `World`, fixed-dt step loop | — |
| phys-02 ✅ | `RotQ`: rational unit-circle type; verified invariant c²+s²=1, exact compose/inverse; `snap(angle_enclosure, k)` with certified 2⁻ᵏ error (uses verus-interval-arithmetic) | phys-01 |
| phys-03 ✅ | free-flight symplectic Euler; **proved:** exact conservation of linear & angular momentum for closed systems | phys-02 |
| phys-04 ✅ | convex rational polygons; SAT contact detection; **proved:** classification correctness with witness (axis or feature pair) | phys-01 |
| phys-05 | single-contact impulse; **proved:** momentum exchange exact, restitution inequality post-state; SPEC §4 leftovers LANDED (05a massprops, 05b transforms/AABBs); remaining: triple datatype change (Body.shape, World.joints, StepResult enum — one invalidation) + S4 through the certificate (§3.7) | phys-03,04 |
| phys-06 | sequential-impulse multi-contact loop + **proven certificate checker** (non-penetration, ledgers); reject-and-retry stepping; C6 uses the two-source ledger bound (D9); signed-enclosure debt RESOLVED | phys-05 |
| phys-07 | revolute (pin) joint + drift certificate; certified rounding pass (D3) | phys-06 |
| phys-08 | gear joint (ratio constraint, ratio-drift certificate); **demo: gear train + crank** | phys-07 |
| phys-09 | trace JSON + tiny canvas viewer (unverified glue; maybe steal verus-canvas bits) | phys-06 |
| phys-10a | untrusted profile generator (involute + cycloid flanks): float tooling allowed outside the verified crate; emits exact rational polygon vertices AND local-turn signs as a convexity certificate (D12); engine certificates carry all verified claims (E4) | phys-04 |
| phys-10b | certified profile bounds: per-vertex enclosure ε to ideal curve (needed only for the L3/G6 bridge, NOT for demos) | phys-10a |
| phys-11 | **flagship: emergent meshing** — two generated gears, one driven, contact does the rest; certificate: contact chain maintained, empirical ratio within bound of −z₁/z₂ | phys-06,10a,16 |
| phys-12 | Lean G1–G2 (repo setup + involute basics + string property) | — (parallel) |
| phys-13 | Lean G3–G4 (transmission lemma, law of gearing) | phys-12 |
| phys-14 | Lean G5 stretch (contact ratio, undercut) | phys-13 |
| phys-15 | bridges: engine as tactus crate once B6/user-traits mature; Lean G6 approximation theorem | far-future |
| phys-16 | non-convex shape unions (convex-piece decomposition; concave/internal contact) — gears are non-convex, so this unblocks ALL emergent cards | phys-04 |
| phys-17 | transmission-function joint (D6): rational piecewise f(φ), drift certificate; demos: elliptical-as-constraint, Geneva dwell, one-way ratchet joint | phys-08 |
| phys-18 | pin/lantern gear generator: pins are exact circles (zero approximation), certified cycloidal mating flank; emergent clockwork demo — candidate FIRST emergent demo, cheaper than involute | phys-06,16 |
| phys-19 | non-circular pitch pairs (rational conic/Bézier centrodes) + conjugate flank generator (envelope method, certified pointwise); emergent elliptical gears | phys-10a,16 |
| phys-20 | internal/ring gear contact + planetary train demo | phys-10a,16 |
| phys-21 | mechanism demo pack: ratchet+pawl, mutilated gear, Geneva pin-slot, **escapement (the ticking verified clock)** | phys-16,17 |
| phys-22 | prismatic (slider) joint + spring/damper force elements; energy ledger extended with exact elastic potential | phys-07 |
| phys-23 | cam-as-constraint via D6 coupling joint (angle→slide): rise-dwell-return motion laws, rack & pinion; drift certificate | phys-17,22 |
| phys-24 | cam profile generator: motion law → profile for knife-edge / roller / flat-face followers (offset + envelope, certified); generation-time pressure-angle & undercut checks; arc/tangent cams exact | phys-10a,22 |
| phys-25 | emergent cam demos: force-closed roller follower (follower-jump physics, conditional certificate per D8), form-closed groove cam, constant-breadth pair, conjugate pair; four-bar linkage bonus demo | phys-16,24 |

Suggested first arc: phys-01 → 02 → 03 ✅ (done, with phys-04 landed right
after). Current arc: phys-05 (05a/05b landed; 05c triple datatype change +
Row + single-contact impulse, 05d S4 through the certificate) → phys-06
(row solver + certificate checker; C6 on the two-source ledger bound D9).
phys-12 (Lean G1–G2) remains the Lean-side palate cleanser whenever the
mood is more mathlib than Verus — and G0 now also owes the tan-remainder
theorem (D9). First emergent demo: consider phys-18 (lantern gears)
before phys-11 (involute) — exact pins mean less approximation machinery
on the critical path, and clockwork charisma arrives sooner.

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
