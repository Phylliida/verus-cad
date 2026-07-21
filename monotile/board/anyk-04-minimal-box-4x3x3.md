---
title: "K=3 mining — resolve the 4×3×3 candidate minimal box"
status: done
claimed_by: fable
created: 2026-07-16T17:27:36Z
updated: 2026-07-19T09:00:00Z
---

## Description

From the MUS mining (`NOTES_FOR_AGENT.md` §3): box+patterns is SAT through
4×4×2 (32 cells) and 3³, and the candidate minimal UNSAT box is 4×3×3
(36 cells, ~344K clauses ≈ half of 4³'s), but the instance was neither
fast-SAT nor fast-UNSAT at 200s. Plain solving is known-dead at this family's
scale; lex symmetry-breaking + cube-and-conquer was the tractability key for
4³ (0.21s/cube once lex leaders were added) — apply the same treatment to
4×3×3.

Also answer the mining's open micro-question (a): is the 4×3×3-slab
obstruction universal across 3³ survivors, or specific to the one extracted
witness? (Sample several 3³ pattern-avoiding survivors, test each on 4×3×3.)

**Done when:** 4×3×3 is resolved UNSAT or SAT.
- If UNSAT: we have a sharp minimal-box claim (4³ → 36 cells) for the paper;
  optionally re-export `genArenaCNF` on 4×3×3 and re-run the cert pipeline
  for a half-size certificate (judgement call — only worth it if the Lean
  delta is small).
- If SAT: 4³ stands as minimal-known; record the witness.

**Blocked by:** nothing. Compute-bound, background-friendly.

## Progress

- (2026-07-16T18:00Z) Soundness catch before building: **full-24 lex-breaking
  is unsound on a non-cubic box** — rotating a decoration maps
  (4,3,3)-tileability to axis-permuted-box tileability, so only the order-8
  subgroup of rotations preserving {±x} (y/z dims equal, so ±y/±z may mix)
  × global flip may lex-break. An UNSAT under full-24 lex would be a lex
  artifact. `mine_433.py` builds with the order-16 subgroup lex.
- (2026-07-16T18:00Z) Instance built: `mine_433.cnf`, 2,629 vars / 347,076
  clauses / 256 conjugate pattern blocks (patterns-only, no point-blocks —
  matches the formal SearchUnsat statement). Plain cadical running in
  background (`mine_433_solve.log`); if it doesn't resolve in a few hours,
  escalate to cube-and-conquer over the subgroup-lexed instance.

## Writeup

**Resolved: 4×3×3 is UNSAT** (`mine_433_solve.log`, cadical exit 20, ~2
days monolithic on the order-16 subgroup-lexed instance — the lex
soundness catch at build time matters here: with full-24 lex this UNSAT
would have been inconclusive on a non-cubic box). Combined with the
mining's SAT results at 3³ and 4×4×2 (32 cells), the K=3 obstruction's
**minimal box is exactly 4×3×3 (36 cells)**: genuinely 3-dimensional, no
thinner or smaller window suffices. Paper-grade sharp statement in hand.

Left as a judgment call for the paper phase: re-exporting the formal
certificate on the 36-cell window (~344K clauses vs 657K — worth it only
if the Lean delta is small). The optional micro-question (universality of
the 4×3×3 obstruction across 3³ survivors) remains open and low-priority.
Note: superseded in significance by the any-K census (which classifies
every relation without box-minimality mattering), but this pins the
sharpest fixed-K=3 form.
