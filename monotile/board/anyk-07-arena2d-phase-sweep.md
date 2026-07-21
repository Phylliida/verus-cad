---
title: "2D analogue — phase sweep over K: does single-orbit aperiodicity ever switch on?"
status: done
claimed_by: fable
created: 2026-07-16T17:27:36Z
updated: 2026-07-16T21:30:00Z
---

## Description

Sweep `arena2d` upward in K (3, 4, 5, … as far as tractable; exhaustive with
canonicalization while feasible, CEGIS beyond) and keep a per-K verdict
ledger. This is the phase-diagram card: the deliverable is the table
K ↦ {closed-periodic, einstein-found, open}, plus whatever structure the
kill certificates show (2D screws are just rotation-cycles along one axis —
does the all-kills-are-screws phenomenon persist as K grows? does the
pattern-library size trend flat or explode?).

Interpretation, agreed in advance so we don't rationalize afterward:
- A 2D single-orbit einstein at some finite K → strong evidence the 3D
  large-K einstein exists (bits eventually buy enough symmetry-breaking to
  host a hierarchy) → prioritize the constructive route (anyk-08/09/10).
- 2D staying periodic-only through generous K, with a visibly K-stable kill
  structure → evidence the finite-orientation-group obstruction is
  dimension-general → prioritize the cocycle obstruction (anyk-12).
- Known-math caveat: 2D aperiodic monotiles with matching rules exist in
  other models (Socolar–Taylor hexagon uses non-nearest-neighbor rules; the
  hat needs reflections). Neither settles this square edge-matching
  C4-orbit model. Do a short literature pass before sweeping — if this exact
  model is already resolved in print, record it and re-scope the card to
  reproducing + calibrating.

**Done when:** ledger covers at least K ≤ 6 with each K either closed or
einstein-found (open only with a documented tractability wall), and a short
written read of what it means for 3D. An einstein find spawns its own arc
immediately (verify aperiodicity rigorously — hand the object to anyk-13).

**Blocked by:** anyk-06.

## Progress

- (2026-07-16T19:15Z) Ledger so far (exhaustive, zero suspicious at every K):

  | K | bits | canonical reps | unbalanced | untileable6 | periodic | indices seen | wall |
  |---|-----:|---:|---:|---:|---:|---|---|
  | 1 | 4  | 4 | 2 | 0 | 2 | 1,2 | ~0s |
  | 2 | 8  | 38 | 25 | 2 | 11 | 1,2,4 | ~0s |
  | 3 | 12 | 532 | 468 | 38 | 26 | 1,2,4 | 0.2s |
  | 4 | 16 | 8,264 | 7,610 | 484 | 170 | 1,2,4 | 2.3s |
  | 5 | 20 | 131,344 | 127,524 | 3,428 | 392 | 1,2,4 | 28s |

- (2026-07-16T19:15Z) **Key structural read: every periodic index is in
  {1, 2, 4} = the element orders of C4** — the exact 2D mirror of the 3D
  screw finding (orders {1,2,3,4} = element orders of the 24-group). The
  kill structure is K-stable across five decoration sizes; per the
  pre-agreed interpretation, this is evidence for the obstruction route
  (anyk-12) — the finite-orientation-group closure looks bit-count-blind,
  at least in 2D so far.
- (2026-07-16T19:16Z) K=6 (16.7M decorations) launched
  (`arena2d_sweep6.log`). K=7 (268M) needs either a few hours of patience
  or a vectorized canon-enumeration; decide after K=6.
- (2026-07-16T19:50Z) **K=6 closed: 2,098,208 reps in 494s, zero suspicious,
  indices still exactly {1,2,4}.** Ledger now spans six K values with an
  identical kill structure. K=7 (268M decorations, ~2h) launched
  (`arena2d_sweep7.log`).

## Writeup

**Verdict: single-orbit aperiodicity never switches on in 2D — at any K.**
Exhaustive ledger K=1..7 (up to 33.5M canonical reps at K=7), zero
suspicious anywhere, every periodic index ∈ {1,2,4} = the element orders of
C4, K-stable across all seven sweeps. The sweep graduated from evidence to
theorem-shape via the relation layer: all achievable Compat relations =
exactly 116 (face-equation characterization, exact, stabilizes at K=6 —
confirmed by full 2^24 K=6 scan: 116 raw masks, novel = precisely the 17
predicted), each empty or periodic. So the 2D answer to this card's
question is settled negatively and now feeds the Lean port
(RESULTS-2d-anyk.md). Read for 3D: the finite-orientation-group obstruction
is bit-count-blind in 2D; the obstruction route (anyk-12) is the favored
horse, with the same relation-level architecture now proven out.

Bonus structural fact discovered en route: C4-conjugation acts trivially on
achievable relation masks (equations depend only on the differences
ax−o1, ax−o2), so no symmetry reduction is needed anywhere in the 2D
formalization.
