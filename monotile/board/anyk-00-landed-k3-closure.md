---
title: "K=3 closure landed (no_aperiodic_wang_cube) — context anchor"
status: done
claimed_by: fable
created: 2026-07-16T17:27:36Z
updated: 2026-07-16T17:27:36Z
---

## Description

Anchor entry: what's already done before the any-K queue starts. Not a task —
a checkpoint.

## Writeup

**Theorem (Lean 4, machine-checked):** `no_aperiodic_wang_cube` — every
space-tiling K=3 binary-face Wang cube admits a fully periodic tiling
(`spacetiler_periodic_le864`: fundamental domain ≤ 864 cells). Trust base =
Lean kernel + `native_decide` (finite geometric data only) + one external
axiom `ConcreteTree.perCubeUnsat` (1457 cube certs, each cadical→LRAT→
cake_lpr-verified; the SAT solver is not in the trust base). See `RESULT.md`.

**The reading:** all 33 forbidden patterns are screws; a finite rotation group
only permits rational screws, which close into periods (`SCREW_STRUCTURE.md`).

**Mining facts already established** (`NOTES_FOR_AGENT.md`):
- Pattern set has no small core: 30/33 individually load-bearing, 0 redundant,
  3 undetermined (→ anyk-05).
- Box threshold sharp: 3³ SAT, 4³ UNSAT; candidate minimal box 4×3×3
  unresolved (→ anyk-04). Exclusion at 4³ = geometry ∪ patterns, neither alone.
- Balance is droppable for the final UNSAT (sound-but-unnecessary pruning).
- L2 soundness validated 33/33: per-pattern periodic witnesses using only the
  pattern's own pairs (`l2_witnesses.json`).

**Assets:**
- Search: `arena2.py` (K-parametric via `ARENA_K` env, default 3; run via
  `./run.sh [budget|test]`), `cube_conquer3.py`, `saturate2.py`,
  `deep_confirm.py`, `skew.py` (lattice classes), `rigidity.py` (frame-lock).
- Cert pipeline: `gen_cube_certs.py`, `run_sat.sh`, `stream_verify.py`,
  `export_tree.py`, `cube_certs/`.
- Lean ledger (in `lean-flocq/LeanFlocq/`): Coverage, BalanceLaw/Wiring/
  Instantiation, ConcreteArena, Hgeo/Hcert, SatReflection{,Gate,Block,Card,
  Verified}, SymReduce/PInv*/Htile, CubeCover. The engines (coverage, balance,
  faceDecomp_of_data, cert_admitsPeriodic, sym_reduction, CubeCover) are
  generic; only the data layer is K=3-specific.

**Standing math facts for the program:** aperiodicity is monotone under face
refinement (a K-cube block-lifts to an mK-cube with the same tilings), so
K=1 is covered by K=3; einsteins propagate to all multiples of their K; the
no-go set is divisor-closed. An all-K answer therefore cannot come from per-K
sweeps alone.

**Live loose end found while opening this board:** the K=2 arena run
(2026-07-06) budgeted out unfinished — `arena2_log_K2.json` status BUDGET,
79 iters, 0 survivors, 1 suspicious + 2 untileable8 parked. K=2 is not
implied by K=3 and is open. → anyk-01/02/03.
