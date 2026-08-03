# HANDOFF — verus-physics2d / physics-gears

Written 2026-07-29, after phys-05 completed. Read this first; it should be
the only orientation you need.

## Mission

A formally verified 2D rigid-body engine in Verus (exact rationals, no
f32/f64, no `external_body`/`assume`/`admit` anywhere), aimed at certified
gear-mechanism demos. The engine's safety claims rest on a **proven
certificate checker** (D8): the solver is untrusted, every step is
re-checked (momentum bookkeeping, contact bounds, non-penetration,
ledgers, exact energy accounting) and rejected on any mismatch.

## Repo layout (READ THIS — it changed mid-flight)

- `verus-physics2d/` — the crate. **Now a standalone git repo** (has its
  own `.git`). Commit inside it freely:
  `cd verus-physics2d && git add -A && git commit -m "..."`.
- `physics-gears/` — plan/docs, tracked by the OUTER repo
  (`/home/bepis/prog/verus-cad`). Commit with EXPLICIT paths only —
  the outer repo has many unrelated dirty submodules; never `git add -A`
  there:
  `git add physics-gears/X.md && git commit -m "..."`.
- `verus-physics2df/` — a STALE full copy of the crate that got committed
  to the outer repo by accident. Ignore it; do not edit, do not build,
  do not "fix" it (user said leave it).
- Docs: `physics-gears/DESIGN.md` (v1.5, master design + board),
  `SPEC-phase1.md` (phase-1 spec + addenda A1–A11),
  `SPEC-phys06.md` (**the phys-06 execution plan — your bible**),
  `memory/` (dated hard-won lessons; README indexes them).

## Current state

- **phys-01 .. phys-05 COMPLETE; phys-06a engine COMPLETE** (manifolds,
  solver, full C1–C5+C7 certificate, pipeline), exec-validated on the
  full S5a trajectory (140 steps, all certify). **S5a's static
  acceptance proof is in flight** — the velocity-bookkeeping piece is
  ~95% done with 2 remaining errors at the end of pgs_sweep_exec.
- **READ `verus-physics2d/HANDOFF.md` NEXT** (2026-08-03) — it has the
  current state, the in-flight uncommitted work with the exact failure
  point, and this session's design decisions (C7 D13 resolution,
  PGS-internal canonicalize, tol_p = 1/100).
- The rest of this file is accurate for phys-01..05 and repo layout.
- Landed: RotQ + angle ledger (signed enclosures, |t| ≤ 1), free-flight
  step with exact momentum conservation (S1/S2), ConvexPoly global
  convexity + checked constructor (S3), exact mass props (M1), world
  transforms/AABBs/broadphase, Compound/Joint/StepResult datatypes,
  the E1 Row type + single-contact impulse (J·v′ ≡ J·v + λ·mEff exact,
  ΔP exchange ≡ 0, C3 restitution), the C1–C4 single-contact certificate
  checker (bidirectional ensures), rigid-transform preservation
  (cross(Ru,Rv) ≡ (c²+s²)·cross(u,v), convexity preserved), and **S4**:
  head-on equal-mass squares, post velocities EXACTLY (−1/2, 0),
  certificate accepts.

## Your task: phys-06

Execute `physics-gears/SPEC-phys06.md` — it is self-contained: current
state inventory, pre-flight checks (§3, DO THESE FIRST), one datatype
batch commit (§4), pipeline (§5), manifold clipping (§6), PGS (§7),
the C1–C7 checker spec (§8), projection (§9), snaps (§10), increments
06a/06b/06c with scenes (§11), lessons field guide (§12), risks (§13),
sub-commit order (§14).

Headline: sequential-impulse solver + full certificate (C1 momentum, C2
bounds, C3 no-suck, C4 non-penetration re-derived, C5 joints (vacuous),
C6 ledgers (D9 two-source angle bound), **C7 exact energy ledger —
dissipation nonnegative and exactly computed, no tolerance**), reject-
and-retry driver, scene S5 (3-box stack, 2000 steps).

## Workflow

- **Verify:** `./check.sh verus-physics2d` (workspace root) or the MCP
  tools `verus_check` / `verus_lookup` / `verus_search` (activate a
  context first: `verus_context_list` → `verus_context_activate(
  "physics-gears-phase1")`). MCP checks have a ~10 min client timeout —
  **the server keeps running and caches; a timeout is not a failure**,
  just retry and you'll get cached results.
- **Module checks iterate; full-crate decides.** Module-scoped
  `verus_check(crate, module)` TRUSTS dependency lemmas — a broken lemma
  in another module passes module checks and only fails the full run.
  Commit only on full-crate green.
- **Cache:** `-V cache` is on. Datatype/trait/base changes invalidate the
  whole crate — batch them (§4 of SPEC-phys06 is one commit). Never
  `cargo clean`.
- **Commits:** small and frequent. Crate repo: `git add -A` is fine.
  Outer repo: explicit paths only.

## Hard-won rules (details in physics-gears/memory/)

1. Real-valued `by(nonlinear_arith)` DIVERGES Z3 here. Integer
   cross-multiplication only (eqv_spec unfolds). NLA also ignores local
   asserts AND treats spec-fn applications as opaque — restate hypotheses
   as implication antecedents, NLA only on fully-unfolded int terms.
2. Checker ensures must be BIDIRECTIONAL (`ok == checks_pass`) or scenes
   can't prove acceptance. Every per-check exec fn: `ok == its spec`.
3. Read every ∃-spec twice for vacuity (the exists-ms C4 form was
   vacuous; exists-EDGE-witness is the right shape).
4. Abstract lemmas > closed eval (lemma_solve_row_c3 discharged S4's C3
   with zero closed evaluation). Closed eval: `*_closed_int` helpers +
   state closed goals FIRST in a context (R5).
5. Design scene constants for the proof: integral anchors (side-2 boxes)
   keep den == 0 and final values structurally pinned.
6. rlimit: exec fns ≤ ~80 lines, proof helpers in `proofs/*.rs`, no
   inline proof blocks > ~15 asserts. Closed-goal poisoning is real.
7. eqv-chain discipline: micro-rewrites → per-term chains → congruence →
   transitive; a proof fn's facts are available only AFTER the call;
   every 3-node chain needs its own `lemma_eqv_transitive(a,b,c)`;
   congruence takes FACTORS, not sums/products.
8. Solver is untrusted (D8): wf-only proofs for solver/pipeline code;
   all deep content in the checker + its lemmas. Weak solver ⇒ Reject,
   never wrong-accept.
9. `new_checked` is the convexity gate — never trust solver-produced
   polys; re-verify the invariant at runtime.
10. Raw `*_spec` discipline: trait ops canonicalize (unfold-proof);
    raw ops unfold to integer polynomials. Structural mirrors beat eqv
    mirrors (the sign-blind `den` made the odd-series mirror nearly
    free — D11's symmetry rule).

Memory files (newest first): certificate-design-lessons,
module-checks-and-nla-opacity, design-review-2026-07-28,
closed-eval-discipline, mirror-proofs-and-perturbation.

## Key APIs you'll use constantly

- `row.rs`: Row, BoundQ, eff_mass_exec, row_vel_exec, apply_impulse_exec,
  contact_row_exec, solve_row_lambda_exec, clamp_spec.
- `proofs/row.rs`: lemma_row_vel_after_impulse (J·v′ ≡ J·v + λ·mEff),
  lemma_contact_momentum_exchange, lemma_solve_row_c3,
  lemma_eff_mass_pos_linear_a, lemma_add_pair_swap.
- `certificate.rs`: the 05d checker — the structural template for
  check_step (per-check exec fns, c4_touch_witness, body_world_verts).
- `proofs/world.rs`: lemma_convex_poly_inv_world, lemma_orient_world,
  lemma_vcross2_vrot, bilinearity pack.
- `narrowphase.rs`: sat_classify, classify_side (max-sep + max property
  + value, bounds on reported edge), min_axis_sep_exec.
- `broadphase.rs`: world_verts_exec, broadphase_pairs (== spec filter).
- `step.rs`: step_free_flight (integration + ledger template),
  StepResult, body_step_rel, lemma_series_(neg_)unit_interval.
- `angle_ledger.rs`: angle_enclosure_signed, arctan_term_exec,
  ledger_increment (in step.rs).
- `proofs/rational_raw.rs`: R1–R5 discipline header + raw bridges
  (neg_mul_*, neg_sub, neg_one_mul, neg_div, add/mul zero).
- verus-rational: full eqv/le/lt lemma library (algebra, ordering,
  ring_algebra, division, applications — lemma_from_int_preserves_lt/le,
  lemma_square_le_nonneg, lemma_pos_mul_pos, lemma_sub_add_distributes,
  lemma_div_cancel/div_mul_cancel, lemma_reciprocal_spec_inverse).

## First actions (from SPEC-phys06 §3)

1. Check canonicalize feasibility: gcd/exact-div availability in
   verus-bigint + verus-rational runtime (D10's untrusted-reducer
   canonicalize hinges on it; affects 06c).
2. Time a compiled S1 run for exec-feasibility of 2000 certified steps.
3. Pre-work commit: delete verus-rational `applications.rs.bak`,
   swap `angle_enclosure_signed` to the standard API (A9(g)).
4. Then the datatype batch commit (SPEC-phys06 §4) — one invalidation.

## Gotchas

- `verus-physics2df/` — stale copy, ignore (see Repo layout).
- Outer-repo `index.lock` appeared once after a killed task; verify no
  git process is running, then it can be removed/retried.
- scenes.rs holds the `*_closed_int` helpers and q_* bridges (A9(e) says
  hoist them into shared modules eventually — fine to do lazily).
- C6's two-source angle bound tightens the step accept condition to
  |h| ≤ 1/2 (h = ω·dt/2); scenes must respect it (driver halves dt).
- The Lean-side G0 anchors ledger SEMANTICS (arctan bracketing, tan
  remainder R·h⁷); Verus proves arithmetic only. The engine ships
  without G0, the "within N·ε of ideal" headline waits on it (D9).
