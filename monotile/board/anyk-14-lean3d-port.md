---
title: "The 3D Lean port — no_aperiodic_wang_cube_anyK on the AnyK2D template"
status: in_progress
claimed_by: fable
created: 2026-07-17T09:30:00Z
updated: 2026-07-17T09:30:00Z
---

## Description

Formalize the 3D any-K theorem from the classified census (anyk-08:
66,134 canonical profiles, 9,363 periodic ≤64 / 56,771 empty ≤6³ / 0
aperiodic). Milestones:

- **M1 — geometry + factorization.** τ machinery (8 signed swaps,
  `Fin.rev`), `eqHolds` with twist, `compat` via the exported 1728-triple
  tables, `compat_factors` (K vanishes into the 84-bit profile), SFT layer
  on ℤ³/24 letters. Files: `AnyK3DGeom.lean` (generated), `AnyK3D.lean`.
- **M2 — gain-closure lemmas** (the new math): real profiles are
  implication-closed under the D4×Z2 gain algebra; realized stabilizers
  are even-feasible (fixed-cell argument, K-generic).
- **M3 — the census in Lean**: enumerate (partition, gains, subgroup)
  structures *in Lean* (native eval) so completeness is by construction;
  cross-check count 66,134/1,445,865 against Python.
- **M4 — certificates**: frontier-compressed table (monotone: emptiness
  antitone, periodicity monotone ⟹ only maximal-empty + minimal-periodic
  antichains needed); torus certs incl. the two index-64 skew ones;
  box-empty certs via LRAT + in-Lean `verifyCert` (3³ = 24^27 kills the
  2D brute-∀ trick); rotation-orbit cert transport.
- **M5 — assembly**: `no_aperiodic_wang_cube_anyK (K) (d) : Tiles K d →
  PeriodicallyTiles K d`.

**Done when:** M5 compiles with `#print axioms` = kernel + native_decide
(+ at most cake_lpr-style external axioms if verifyCert can't cover some
certs — aspire to none).

## Progress

- (2026-07-17T09:30Z) **M1 COMPLETE, first-try clean compile.**
  `anyk3d_lean_export.py` → `AnyK3DGeom.lean` (1728 triples + 84 equations,
  from the reconstruction-validated faceeq3d derivation); `AnyK3D.lean` =
  τ inverse lemmas (fin_cases + `Fin.rev_rev`), twisted `eqHolds_symm`
  (pure kernel), `tables_norm` (one native_decide: every triple matches
  its equation directly or flipped-with-inverse), `compat_factors`
  ([propext, Classical.choice, ofReduceBool, trustCompiler, Quot.sound]),
  SFT defs. The 2D dress rehearsal pre-validated every lemma shape —
  zero compile iterations needed.
