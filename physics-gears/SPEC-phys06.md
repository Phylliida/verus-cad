# SPEC: phys-06 — sequential-impulse solver + proven certificate checker

Companion to DESIGN.md v1.5 and SPEC-phase1.md (A1–A11). Self-contained
implementation plan written after phys-05d; a fresh context should be able
to execute from this file alone. House rules apply: no
`external_body`/`assume`/`admit`; no f32/f64; module checks are for
iteration only — **the full-crate green is the only green that counts**
(memory: module-checks-and-nla-opacity).

## 1. Scope & headline claims

phys-06 delivers the complete exact-rational engine step:

- Contact manifolds (clipping) from SAT results (SPEC §5 step 3 — deferred
  from phys-05/A6).
- Multi-row PGS velocity solver (N = 16 iterations, canonical row order).
- The full step pipeline (gravity → rows → PGS → snap → integrate →
  project → snap → certify) as a PURE fn `World -> StepResult`.
- `StepCert` + the proven checker (`check_step`), the ONLY thing the
  engine's headline claims rest on (D8): ok == the checks pass, and
  ok ⟹ step_certified (C1–C6).
- Reject-and-retry driver (halve dt on Reject, give up below dt/16).
- Scene S5: 3-box stack on static ground, gravity, 2000 steps, no
  rejection, final penetration ≤ tol_p, boxes still (SPEC §8).

Explicitly OUT (phase-1 non-goals, SPEC §9): friction, restitution > 0,
warm starting, sleeping, CCD, joint rows (phys-07: C5 is vacuously true
over `World.joints == []` for now), density constructor (uses A9(f)
inertia nonnegativity — optional, see §8.4).

## 2. Current state (what exists to build on)

- `row.rs`: Row/BoundQ, eff_mass/row_vel exact evaluators,
  `contact_row_exec` (one contact point → row), `apply_impulse_exec`,
  `solve_row_lambda_exec` (single-row PGS update with clamp), `clamp_spec`,
  `bounds_consistent`, `lambda_in_bounds`.
- `proofs/row.rs`: J·v′ ≡ J·v + λ·mEff (per-row workhorse), momentum
  transfer m·Δv ≡ λ·j, contact exchange ΔP_a + ΔP_b ≡ 0,
  `lemma_solve_row_c3` (fresh-row restitution), eff-mass sign theory.
- `certificate.rs`: the phys-05d single-contact checker — **the template
  for phys-06**: per-check exec fns with EXACT bidirectional ensures
  (`ok == spec_conjunct`), composed into `ok == contact_checks_pass`,
  `ok ⟹ contact_step_certified`. C4 self-transforms world polys, gates
  through `ConvexPoly::new_checked`, re-runs `classify_side`, depth-checks
  `max(ms_a, ms_b) ≥ −tol_p`.
- `proofs/world.rs` (17 lemmas): rigid transforms preserve orient and
  global convexity — the C4 workhorse. `proofs/cert.rs`: touching-case
  depth reasoning. `proofs/shape.rs`: min_sep fold lemmas (le_all,
  ge_all, attained, min_pos_all).
- `narrowphase.rs`: `sat_classify`, `classify_side` (max-sep reference
  feature + max property + value), `min_axis_sep_exec`, `axis_sep_exec`,
  `edge_normal_exec`. NO manifold/clipping yet.
- `broadphase.rs`: `world_verts_exec`, AABBs, `broadphase_pairs` (O(n²)
  filter == spec filter, canonical lex order).
- `step.rs`: `step_free_flight` (gravity + symplectic integration +
  tan-half rotation + angle ledger, StepResult = Ok | Reject).
  `body_step_rel`, `ledger_increment`, unit-interval series lemmas.
- `angle_ledger.rs` + `proofs/angle_ledger.rs`: `angle_enclosure_signed`
  (standard API per A9(g) — swap not done yet), signed term/enclosure
  lemmas on [−1,1], `arctan_term_exec`.
- `proofs/rpow.rs`: ipow for the C6 h⁷ term.
- scenes S1–S4, M1: step loops with statically-proven invariants,
  closed-eval discipline (`*_closed_int` helpers in scenes.rs).

## 3. Pre-flight checks (do FIRST, ~1 hour, cheap)

1. **canonicalize feasibility (D10).** Does the BigInt/RuntimeRational
   stack have a gcd or division suitable for an untrusted-reducer
   canonicalize (constructor checks `num'·den == num·den'`, one exact
   multiply)? Look in verus-bigint (gcd? exact div?) and
   verus-rational runtime_rational. If gcd is missing, canonicalize via
   `normalize_constructive`-style spec + a runtime Euclid is 06c scope;
   note it changes 06c's estimate.
2. **Exec runtime sanity.** Time `scene_s1` (1000 steps) compiled and
   run for real — S5 is 2000 steps with PGS+certificate per step; if a
   plain free-flight step is slow, plan denominator hygiene earlier
   (canonicalize between PGS iterations, D10 explicitly allows it:
   value-preserving, no ledger entry, eqv-seams at explicit call sites).
3. **angle_enclosure_signed API swap (A9(g))** — mechanical, do it in the
   pre-work commit (parity-ordered `angle_enclosure` becomes internal).
4. Delete `verus-rational/src/rational/applications.rs.bak` (A9(h)).

## 4. Datatypes — ONE batch commit, one invalidation (§3.7(a) principle)

Land ALL of these in the same commit before any 06a proof work:

```rust
// narrowphase.rs (SPEC §5)
struct ContactPoint { point: SVec2, sep: Scalar }        // sep ≤ 0
struct ContactManifold {
    a: usize, b: usize,              // a < b (E6 canonical)
    normal: SVec2,                   // A → B, UNNORMALIZED (never sqrt)
    points: Vec<ContactPoint>,       // len 1..=2, lex order
    feature: (usize, usize),         // (ref edge, inc edge)
}

// certificate.rs (SPEC §7)
struct SnapEntry {
    body: usize,
    kind: SnapKind,                  // VelX | VelY | Omega | PosX | PosY
    delta: Scalar,                   // actual signed delta applied
    bound: Scalar,                   // declared |delta| ≤ bound (C6)
}
struct StepCert {
    rows: Vec<Row>,                  // final λ per row (untrusted witness)
    tan_halfs: Vec<Scalar>,          // per body (already in Ok payload)
    snaps: Vec<SnapEntry>,
    angle_entries: Vec<Scalar>,      // per body ledger increment used
}

// step.rs — CHANGE the Ok payload (this is the breaking one):
enum StepResult { Ok(World, StepCert), Reject(RejectReason) }
```

`step_free_flight` keeps its current signature (scenes S1/S2 use it) OR
migrates to the new StepResult with an empty-cert; decide at
implementation time, prefer migrate (one step fn long-term; SPEC §1
already says `step(w) -> StepResult` with cert on Ok). RejectReason
gains: `CertFailed`, `DenomOverflow` (if a snap/canonicalize fails),
`ManifoldFailed` (degenerate contact: zero-length normal etc.).

## 5. The step pipeline (exec; untrusted except ensures)

```
fn step(w: &World) -> (r: StepResult)
    requires w.wf_spec()
    ensures  r is Ok ==> r->Ok_0.wf_spec()
                          && step_checks_pass(w, r->Ok_0, r->Ok_1)
                          && step_certified(w, r->Ok_0, r->Ok_1)
```

Pipeline (SPEC §6 order):
1. gravity: v += g·dt per dynamic body (reuse step_free_flight's loop
   shape; statics untouched).
2. joint rows — none (phys-07); loop over `w.joints` is empty but
   written (C5 spec form lands now).
3. broadphase (`broadphase_pairs` existing) → per candidate pair
   `sat_classify` → per Touching result `build_manifold` (§6) → per
   contact point `contact_row_exec` (existing). Row order: pairs lex,
   then points lex (E6).
4. PGS N=16 (§7).
5. velocity snap (06c; in 06a/06b: canonicalize only, no ledger).
6. integrate (reuse step_free_flight's pos/rot + ledger loop; the
   tan_halfs and angle_entries go into the cert).
7. position projection M=4 rounds (06b, §9).
8. position snap (06c).
9. build StepCert, call `check_step`; Ok or Reject(CertFailed).

**Proof budget for the pipeline: thin.** The solver is untrusted (D8).
Each stage needs only: bodies stay wf, Vec lengths preserved, cert
fields populated consistently (lengths match bodies/rows). All deep
content lives in the checker + its lemmas. Do NOT prove solver
convergence, monotonicity, or manifold completeness.

## 6. Manifold construction (06a; SPEC §5 step 3)

Given Touching { from_a, edge } on world polys A, B:

1. reference edge = (owner, edge); incident edge = edge of `other`
   whose outward normal has minimal dot with ref normal (ties: lower
   index). New exec `incident_edge_exec` with ensures: the returned
   index attains the min (fold lemma, mirror of min_axis_sep_exec).
2. clip the incident segment against the two side half-planes of the
   reference edge (exact rational segment-halfplane clip):
   t-values as rational params, NO sqrt. New `clip_segment_exec`.
3. keep clipped endpoints with sep ≤ 0 relative to the reference face
   (sep = axis_sep(ref_normal, ref_p0, point)); 1 or 2 ContactPoints,
   lex-sorted (E6).

Verified ensures (phase-1 scope, per SPEC §5):
- every reported point lies on the reference face line within the
  clipped span (eqv: point ≡ ref_p0 + t·(ref_p1 − ref_p0), t ∈ [0,1]),
- its stored sep ≡ the exact axis_sep value,
- normal ≡ ref edge_normal (unnormalized), |n|² ≠ 0 (strict convexity
  ⟹ edge endpoints distinct — needs a distinctness lemma from
  convex_poly_inv: orient > 0 for off-edge vertices ⟹ adjacent verts
  differ; closed form per use).

The checker never trusts manifolds (D8): weak/incomplete manifolds only
risk Reject via C4, never a wrong accept. Degenerate results (0 points)
→ drop the pair silently (solver choice; C4 still guards).

## 7. PGS sweep (06a)

```
for iter in 0..16:                       // fixed count, canonical order
    for r in rows:                       // construction order
        v_rel = row_vel_exec(r, bodies[r.a], bodies[r.b])
        Δ = −(v_rel + bias)/mEff         // mEff from row build ( > 0 )
        λ' = clamp(λ + Δ, lo, hi)        // clamp_spec discipline
        apply (λ' − λ) via apply_impulse_exec to both bodies
        r.lambda = λ'
```

- mEff per row computed ONCE at build (bodies' inv masses don't change
  mid-step); row dropped if mEff ≡ 0 (SPEC §6).
- Invariants: bodies wf, rows' J/bounds unchanged (only λ mutates),
  bodies@.len() constant. NOTHING else — the certificate is the claim.
- canonicalize velocities between iterations (D10, value-preserving) as
  needed for exec feasibility (pre-flight 2 decides).

Note on C3 (spec form is per-row post v_rel ≥ −tol_v): PGS residuals
after N=16 are exact rationals whose sign is NOT guaranteed ≥ 0 in
general. tol_v is a scene parameter — S5 should plan on a small
rational tol_v (e.g. 1/1000) rather than 0; record actuals. (For the
single-row S4 case exact 0 was provable; multi-row is not exact-zero
in general — flag in DESIGN if S5 wants tol_v = 0 and can't have it.)

## 8. The certificate (the card's core)

### 8.1 step_checks_pass / step_certified (spec fns, C1–C6)

Mirror of phys-05d: `check_step` returns `ok == step_checks_pass(pre,
post, cert)` and `ok ⟹ step_certified(pre, post, cert)`. The two spec
fns differ only in that checks_pass includes the constructive gates
(new_checked convexity) needed for the bidirectional direction.

- **C1 (velocity bookkeeping, exact).** For every body i:
  `post.vel[i] ≡ pre.vel[i] + g·dt + inv_m_i · Σ_{r: r touches i} λ_r·jl_r(i)
                + Σ_{s: vel-snap on i} s.delta`
  `post.omega[i] ≡ pre.omega[i] + inv_I_i · Σ λ_r·ja_r(i) + Σ omega-snaps`
  Checker: per body, fold over cert.rows (spec fold `impulse_sum(rows,
  i)` + exec fold with invariant == fold so far), compare each
  component with `eq` (eqv bridges, symmetric as in 05d). Corollary
  lemma (prove ONCE, proofs/solver.rs): rows with both endpoints
  dynamic transfer momentum equal-and-opposite — total momentum of a
  closed system is invariant under the solver (05c's exchange lemma is
  the per-row case; this is the fold).
- **C2 (bounds).** ∀ r: lambda_in_bounds(r.lo, r.hi, r.lambda). Fold.
- **C3 (restitution, e=0).** ∀ contact row r: row_vel(r, post) ≥ −tol_v.
  Fold; per-row spec identical to 05d.
- **C4 (non-penetration, re-derived).** Checker runs ITS OWN broadphase
  on post (existing broadphase_pairs), and for each candidate pair:
  world polys via world_verts_exec + new_checked gate + classify_side ×2
  + depth check — the 05d check_c4 body per pair, generalized to a
  loop. Spec per pair: the exists-separated-witness OR
  (no_axis_separates ∧ ∃ edge with min_sep ≥ −tol_p) disjunct
  (**exists-EDGE-witness — the exists-ms form is vacuous, A11**).
  Static-vs-static pairs: skip (no motion possible; document).
- **C5 (joint drift).** ∀ joint: anchor drift ≤ tol_j. Loop over
  `w.joints` — empty in phys-06, spec form lands, exec loop trivially
  passes. (Full content phys-07.)
- **C6 (ledgers, 06c).**
  (a) snaps: ∀ s ∈ cert.snaps: |actual delta| ≤ s.bound, where actual
      is recomputed from pre/post fields per s.kind. (In 06a/06b
      snaps == [], vacuous.)
  (b) angle: per body i, `cert.angle_entries[i] ≤ width_i + R·h_i⁷`
      where width_i = 2·|term_{k+1}(t_i)| (existing
      `ledger_increment`, t_i = cert.tan_halfs[i], k = w.series_k),
      h_i = ω_i·dt/2 (recomputed), R = 1/16 — the D9 TWO-SOURCE bound:
      enclosure width + tan-remainder. Requires |h_i| ≤ 1/2 (step
      rejects otherwise — this TIGHTENS the accept condition from
      |t| ≤ 1 to |h| ≤ 1/2; lemma_series_unit_interval + mirror already
      cover exactly that range for the Some-guarantee).
      and `post.angle_err[i] ≡ pre.angle_err[i] + cert.angle_entries[i]`
      (accumulated totals update correctly).
  Verus proves only the ARITHMETIC; the semantic anchoring (A_k brackets
  arctan; tan remainder ≤ R·h⁷ on [0,1/2]) is Lean G0, which grows the
  tan-remainder theorem (D9). Record the dependency in the ledger
  module docs.

### 8.2 Checker structure (mirror 05d exactly)

per-check exec fns with `ok == spec` ensures:
`check_c1_rows`, `check_c2_rows`, `check_c3_rows`, `check_c4_world`,
`check_c5_joints`, `check_c6_ledger` (06c), composed in `check_step`.
Keep each fn ≤ ~80 lines; fold lemmas (impulse sum, all-rows-bounds,
etc.) in proofs/solver.rs and proofs/cert.rs. Extract proof helpers
EARLY — the 05d rlimit failure mode was inline proof blocks in exec
fns (memory: certificate-design-lessons §6).

## 9. Position projection (06b)

After integration, re-run broadphase+narrowphase; for each pair with
max-sep < 0 (penetrating): translate both bodies along the (unnormalized)
normal, split by inverse mass:
  `Δ_a = −β · (sep / |n|²) · (inv_m_a / (inv_m_a + inv_m_b)) · n`
  `Δ_b = +β · (sep / |n|²) · (inv_m_b / (inv_m_a + inv_m_b)) · n`
with β = 1/2, M = 4 rounds. All rational (|n|² fold — no sqrt,
standing rule). Statics don't move (inv_m = 0 ⇒ share 0; guard the
sum ≢ 0 — if both static, skip). Untrusted (C4 guards), wf-only proofs
+ position deltas recorded into cert.snaps if snapped (06c).

## 10. Velocity/position snap + canonicalize (06c)

- canonicalize (D10): untrusted reducer proposes (num', den'),
  constructor CHECKS num'·den == num·den' (one exact multiply, nlsat
  pattern). Value-preserving: eqv bridge only, NO ledger entry. Use
  freely (between PGS iterations, step boundaries).
- snap (D3/E5): round a velocity/position component to denominator
  bound 2^K (K = 64): snapped = round(value · 2^K) / 2^K — the
  value-CHANGING primitive, |delta| ≤ 2^(−K), recorded as SnapEntry
  with declared bound; C6(a) re-checks |actual| ≤ declared.
  Snap ONLY when a denominator exceeds 2^K (checked via bit-length) —
  most steps snap nothing (S5's steady state should be snap-free after
  settle; entries stay vacuous).

## 11. Increments & acceptance scenes

- **06a** (the big one): datatype batch (§4) + manifold (§6) + PGS (§7)
  + pipeline steps 1–4 + cert C1–C5 (C6 vacuous: snaps == [], angle
  check deferred) + scene **S5a**: one side-2 box dropped from height 1
  onto a static ground box, gravity (0,−10), dt = 1/240, ~150 steps:
  every step certifies (ok == true statically), box comes to rest on
  the ground, penetration ≤ tol_p = 1/1000 throughout. (Without
  projection, steady-state penetration is g·dt²-ish per step — compute
  the exact bound for the scene proof: pen ≡ g·dt² per SPEC's impulse
  model; confirm it's < tol_p, else raise tol_p — record the choice.)
- **06b**: position projection (§9) + scene **S5b**: 2-box stack,
  100 steps, penetration driven back to ≈ 0 by projection.
- **06c**: canonicalize + snaps + C6 (two-source) + driver reject/retry
  + scene **S5 (full SPEC §8)**: 3-box stack, 2000 steps, no Reject,
  final penetration ≤ tol_p, |v| < 1/1000 on all boxes.

Scene design rules (memory: certificate-design-lessons §5): integral
anchors (side-2 boxes, integer positions), gravity/dt chosen so h =
ω·dt/2 stays ≤ 1/2 (C6), closed forms structural where possible;
discharge via abstract lemmas before ANY closed eval.

## 12. Proof-engineering field guide (hard-won, apply throughout)

1. **Bidirectional checker ensures** (`ok == checks_pass`) — without
   them scenes cannot prove acceptance.
2. **∃-spec vacuity check** — read every existential spec twice; the
   bound direction must be the non-vacuous one (A11).
3. **new_checked is the convexity gate** — the checker never needs
   convexity of solver-produced polys trusted; it re-checks (nlsat
   pattern). Preservation lemma (proofs/world.rs) supplies the proof
   side that the gate passes.
4. **Abstract lemmas > closed eval** (lemma_solve_row_c3 discharged
   S4's C3 with zero closed evaluation).
5. **Structural scene constants** — integral anchors keep den == 0 and
   final values structurally pinned (eq claims become reflexive).
6. **rlimit discipline** — per-check exec fns ≤ ~80 lines; proof
   helpers in proofs/*.rs; no inline proof blocks > ~15 asserts in exec
   fns; closed goals stated FIRST in a context (R5).
7. **NLA opacity** — `by(nonlinear_arith)` only on fully-unfolded int
   terms; never on spec-fn applications (memory: module-checks).
8. **eqv-chain order** — micro-rewrites → per-term chains → congruence
   → transitive; every 3-node chain its own transitive call; proof-fn
   call order matters (facts available only AFTER the call).
9. **Module checks iterate; full-crate decides** — dependency lemmas
   are trusted under module scope.
10. **Batch datatype changes** — one invalidation per card (§4).
11. **calc! for eqv chains** (D11) — house style for the long folds in
    C1's impulse sum.

## 13. Risks & open questions

- **Exec feasibility of S5 (2000 steps)** — exact BigInt arithmetic with
  canonicalize should hold; measure at 06a (pre-flight 2). Fallback:
  canonicalize more aggressively (every PGS iteration).
- **C3 tol for multi-row stacks** — exact-zero post v_rel is NOT
  guaranteed by finite PGS; S5 likely needs tol_v = 1/1000. If the
  DESIGN wants tol_v = 0 as the phase-1 headline, that's a solver-
  convergence question, not a checker question — flag early.
- **C6 tightens accept to |h| ≤ 1/2** — scenes must respect it
  (rotation speeds); step rejects faster spins (driver halves dt).
- **Manifold edge cases** — vertex-vertex contacts produce 1-point
  manifolds; degenerate clips (empty) drop the pair. Both fine under
  D8 but note C4 then does all the safety work.
- **G0 dependency** — the ledger's semantic reading (arctan bracketing
  + tan remainder R·h⁷) is Lean-side; Verus C6 is arithmetic-only.
  The engine can ship without G0 but the "within N·ε of ideal" headline
  waits on it (D9 fallback: demote ledger to monitored).

## 14. Suggested sub-commits (each full-crate green)

1. pre-work: bak deletion + angle_enclosure_signed swap (+ h/oists if
   cheap).
2. datatype batch (§4) — one invalidation.
3. manifold construction + proofs.
4. PGS + pipeline 1–4 + cert C1–C5 + S5a green.
5. projection + S5b.
6. canonicalize + snaps + C6 + driver + S5 full.
