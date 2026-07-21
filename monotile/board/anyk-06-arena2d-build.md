---
title: "2D analogue — build arena2d (single square, C4 rotations, K-bit binary edges)"
status: done
claimed_by: fable
created: 2026-07-16T17:27:36Z
updated: 2026-07-16T21:30:00Z
---

## Description

Build the 2D analogue arena as the cheap evidence-gatherer for the sign of
the any-K answer. Model: one unit square, 4 edges each carrying K bump/dent
bits (edges are 1-D, so K bits per edge — 4K bits total, space 2^{4K}),
orientation group C4 (4 rotations), tilings of ℤ², matching =
bitwise complementarity on touching edges, aperiodic = no tiling invariant
under a rank-2 lattice.

Why: per-K sweeps here are orders of magnitude cheaper than 3D (K=3 is
2¹² = 4096 decorations — exhaustive; K=8 is 2³² — still sweepable with
symmetry reduction), so the 2D family can be pushed far enough in K to see
whether single-orbit aperiodicity ever switches on as decoration bits grow.
That directly calibrates the 3D question (anyk-07 interprets).

Port from `arena2.py`:
- the CEGIS loop + pattern-library persistence (lazy, per the engine
  lessons — eager preload poisons CDCL);
- the period-finder verifier: 2D period vectors (canonical orbit reps up to
  C4 and sign, |coords| small), identification constraints, torus
  confirmation. Rank structure is simpler than 3D: any single period vector
  + SFT quotient argument gives full periodicity (the 1D quotient lemma is
  already Lean-checked in `SftPeriodic.lean` — same shape);
- balance-law analogue per rotation orbit of edge positions;
- exhaustive mode for small K (canonicalize under C4 × bit-complement,
  then brute-force) alongside CEGIS mode.

Design choice to record, not agonize over: run C4 first; D4 (add
reflections) as a flagged variant later — the 3D result deliberately had no
reflections, keep the families aligned.

**Done when:** `arena2d.py` runs end-to-end; K=1 and K=2 fully closed
(exhaustive, every decoration classified periodic/non-tiler); verdicts +
pattern libraries persisted in the arena2-style json/jsonl formats.

**Blocked by:** nothing. Independent of the K=2/3D cards.

## Progress

- (2026-07-16T18:50Z) `arena2d.py` built, v1 = exhaustive classifier (no
  pattern library needed: every canonical decoration individually classified
  as unbalanced / untileable / periodic-with-witness / SUSPICIOUS, with an
  inline escalation tier). Geometry mirrors arena2 (points as coordinates,
  PERM by construction; square side 2K, face coord ±K, tangentials step 2).
- (2026-07-16T18:50Z) One real 2D-specific finding baked in: **in C4 the
  matching couples orbit(t) with orbit(−t)** — unlike the 3D 24-group where
  orbits are matching-closed — so the Balance Law prefilter uses orbit-PAIR
  unions (structurally asserted at import). Getting this wrong would have
  made "unbalanced" kills unsound.
- (2026-07-16T18:52Z) Self-tests green at K=1,2,3 (perm validity,
  equivariance on random decorations, trivial +faces decoration → periodic
  index 1; unions [4] / [8] / [8,4] as derived). Exhaustive sweeps K=1,2,3
  launched (`arena2d_sweep.log`); K=4 next after timing check; K≥6 needs the
  CEGIS mode (todo).
- (2026-07-16T19:00Z) **K=1,2,3 closed in 0.2s total, zero suspicious** —
  every 2D space-tiler at K≤3 is periodic, all indices ≤4. Verdict mix at
  K=3: 468 unbalanced / 38 untileable6 / 26 periodic (532 canonical reps).
- (2026-07-16T19:02Z) Balance-law kills audited empirically: 60 unbalanced
  decorations × all ~850 lattice classes ≤32 → zero SAT tori (a single SAT
  torus would contradict the 2D law). Theory kill corroborated. K=4,5
  sweeps launched (`arena2d_sweep45.log`).

## Writeup

Built and validated in one evening; exceeded the done-criteria (K=1..7
exhaustively closed, not just K=1,2). `arena2d.py` = geometry with
coordinates-as-ground-truth, C4 orbits, orbit-PAIR-union balance law (the
2D-specific structure: matching couples orbit(t) with orbit(−t)),
free-boundary box solver, full HNF lattice/torus sweep, exhaustive
classifier with escalation tier. Every kill is per-decoration with an
explicit witness or refutation; no pattern library needed at these K.
Empirical balance-law audit: 60 unbalanced decorations × ~850 lattice
classes → zero SAT tori. Spawned `relations2d.py`/`faceeq2d.py`/
`faceeq2d_witness.py` (see anyk-08/12 and RESULTS-2d-anyk.md), which
carried the 2D program all the way to the empirical any-K closure.
