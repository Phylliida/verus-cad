# PGS canonicalize-inside-the-sweep + the C7 drift resolution (D13)

Date: 2026-08-03 (phys-06a, S5a exec bring-up)

## 1. Canonicalize must happen INSIDE the PGS sweep, not just after it

Pre-flight (memory/exec-feasibility-and-normalize) found the RotQ
witness squaring and put canonicalize at step boundaries. Insufficient.

Live measurement at S5a's first contact step: one PGS row update took
vy's denominator from 13 to **665 limbs** (~50× per iteration). The
16-iteration sweep therefore hung for 22+ CPU-hours (killed).

`solve_row_lambda_exec` does Δ = −(v_rel + bias)/mEff and λ′ = clamp(λ+Δ):
the division cross-multiplies denominators, and each apply_impulse multiplies
again. Compounded over 16 iterations it's exponential.

Fix: normalize λ, Δλ, and the updated velocities/omegas **after every row
update** (extracted as `pgs_row_update_exec`). All witnesses pinned at
0–2 limbs; PGS ×16 = 0.5 ms. Value-preserving (eqv) per D10, no ledger
entry; the sweep's ensures never pinned λ/vel models, so verification was
unaffected (rlimit on the enriched loop required the fn extraction).

Rule of thumb: **any iterative exec arithmetic needs canonicalize inside
the iteration**, not just at its boundary.

## 2. C7: the SPEC's W_drift allowance is wrong; D = E(pre) − E(post) ≥ 0

SPEC-phys06 §8.1 defined W_drift = −(1/inv_m)·|g|²·dt²/2 per dynamic body
per step as an ALLOWANCE: E(post) ≤ E(pre) + W_drift. Measured: this
**rejects honest resting contact**. The negative allowance assumes the
body descends with the gravity-updated velocity (free flight, where the
drift is real); at rest the contact solver zeroes v before integration,
so ΔE = 0 — which a negative allowance forbids.

Resolution (the actual D13 form): **no drift allowance anywhere** —
D = E(pre) + W_proj + W_snaps − E(post) ≥ 0, exactly computed.
Justification: the symplectic drift is itself dissipative (free flight:
D = g²dt²/2·(1/inv_m) > 0, computed in closed form), so it needs no
allowance; e = 0 contacts dissipate; nothing positive can appear from
nowhere (that remains the anti-exploit guarantee). The exact KE/PE folds
account every Joule; "dissipation nonnegative and exactly computed" is
the headline, and it holds.

Consequence for scene proofs: at resting contact the PGS residual sign
matters for D ≥ 0 — but S5a's resting state has v ≡ 0 EXACTLY (measured),
a clean fixed point, so D ≥ 0 is structural there.

## 3. S5a numbers (exec-verified, 140 steps all Ok)

- Drop: side-2 box from gap 1 onto static side-2 ground, g = (0,−10),
  dt = 1/240, 2 contact rows from the face-face manifold.
- Impact: step 106 (pre-state gap 89/5760, incoming vy = −107/24).
  Impact penetration is EXACTLY 1/320 = 0.003125 (rows form the step
  AFTER impact — row building is pre-integration by design).
- **tol_p = 1/100** (SPEC §11's "raise tol_p — record the choice"):
  covers the 1/320 impact transient (~3× margin); steady state pen would
  be g·dt² = 1/5760 (~57× margin). tol_v = 1/1000.
- Absorption (step 107): λ = 9/8 per row, vy → 0 EXACTLY, ω → 0.
- Resting (108+): exact fixed point — vy ≡ 0, positions frozen at
  pen = 1/320, λ = 1/96 per row per step (fresh rows each step).
  Per-step cost ~1.6 ms with all witnesses ≤ 2 limbs.
