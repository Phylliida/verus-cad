# Design review 2026-07-28 (after signed-enclosure + phys-05a/b)

Full design review of the physics engine, two rounds: initial findings,
then a "find even better options" pass that revised two recommendations.
Folded into the plan documents as DESIGN v1.5 §3.7 (D9–D12) and SPEC
addendum A9. This file is the narrative record.

## The top finding: the angle ledger understated the true angle error

`|applied − target| = |2·arctan(t) − ω·dt|` has TWO parts: the arctan
series-truncation (enclosure width, k-tunable) and the tan chooser's own
truncation (`tan(h) − series₅(h) ≈ 17h⁷/315`, NOT k-tunable). The old
SPEC reading — accumulated enclosure width bounds the angle error — is
false once k pushes the width below the fixed tan remainder (at h = 1/2,
~4·10⁻⁴ remainder vs ~10⁻⁶ width at k = 8). At S2's h = 1/160 the
discrepancy is astronomically small, but the certificate's semantic
reading breaks at the accept-range boundary.

Chosen fix (D9): enclose tan FIRST (rational `[t_lo, t_hi]` with
certified remainder `R·h⁷`, R ≈ 1/16), then the arctan enclosure of the
endpoints contains the target by construction (arctan is 1-Lipschitz).
Ledger increment = width + R·h⁷. G0 grows the tan-remainder theorem.
Fallback: demote the ledger to D8's monitored category and drop the
"within N·ε of ideal" headline.

Alternatives considered: demote-to-monitored (cheap but loses the
headline); higher-order tan series (couples k to chooser order,
fragile); chord-space error (can't name the ideal δ in Verus — E3);
exact-target angles (forces irrational dt). The tan-interval framing
dominates.

## Revised on reflection (do NOT implement the first versions)

- **Normalize-on-write rationals — REJECTED.** Flips every
  `out@ == op_spec` ensures to eqv-form and destroys the structural-`==`
  discipline that makes mirror/closed proofs cheap. Instead D10:
  explicit `canonicalize()` via checked constructor (untrusted reducer,
  exact check `num'·den == num·den'`, no gcd proof), eqv seams only at
  rare call sites, no ledger entry. Fixed-point solver core (global 2^K,
  verus-fixed-point) is a phys-06+ evaluation.
- **Computable-normalize spec ops (eqv → ==) — REJECTED.** Recursive
  euclid unfold at every op in every proof + a verus-rational refactor.
  The eqv discipline is right for this toolchain. Ergonomic fix instead
  (D11): `calc!` for eqv chains as house style; hoist the q_* bridge
  pack and closed-eval `*_closed_int` helpers into shared modules. The
  standing rule: design spec fns whose symmetry laws hold STRUCTURALLY.
- **Fan-positivity as a cheaper convexity invariant — REJECTED.** It's
  star-shapedness, weaker than convexity; SAT is unsound for non-convex
  inputs. Instead D12: local→global lemma (consecutive turns ⇒ global,
  sweep argument) before phys-10a; the profile generator emits
  turn-signs as a convexity certificate.

## Straightforwardly adopted

- Triple datatype change in ONE phys-05c invalidation: `Body.shape`,
  `World.joints`, `StepResult = Ok | Reject(Reason)` (Option→Result was
  coming at phys-06 anyway).
- S4 goes through the certificate (run one impulse step, verify C1–C4
  on the produced state) — cheaper than a static exec-chain proof AND
  de-risks the phys-06 checker early. That IS D8.
- Inertia nonnegativity via the fan decomposition before phys-06
  (per-triangle dot-sum is a sum-of-squares form; edge≡fan telescoping
  is the same shape as area).
- `angle_enclosure_signed` standard API; parity `angle_enclosure`
  becomes internal. Delete `verus-rational/src/rational/applications.rs.bak`.
- A `take(i).push(w[i]) =~= take(i+1)` shared lemma is worth having.

## What was judged right and left alone

Certificate architecture (D8), no-reals discipline (E3) with G0 as the
single ℝ anchor, scenes-as-static-proofs, structural-mirror-friendly
spec style (raw `*_spec`, sign-blind den), E1 one-row-type, PGS with
e = 0 and reject-retry.

## Final priority order

1. phys-05c (triple datatype change + Row + single-contact impulse) and
   05d (S4 through the certificate)
2. Ledger two-source bound (D9) before phys-06's C6 ossifies
3. `canonicalize()` (D10)
4. `calc!` house style + helper hoisting (D11)
5. Local→global convexity before phys-10a (D12)
6. Fixed-point solver core as a phys-06+ evaluation
