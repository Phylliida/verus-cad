---
title: "Structure theory — which Wang-cube sets arise as a single rotation orbit? (+ orbit_embed solver)"
status: in_progress
claimed_by: fable
created: 2026-07-16T17:27:36Z
updated: 2026-07-16T20:40:00Z
---

## Description

The mathematical heart of the constructive route. A decoration d at parameter
K determines the tile set orbit(d) = {g·d : g ∈ Rot24} with induced matching.
Aperiodic *sets* of ~20 unconstrained Wang cubes are known to exist
(Culik–Kari); the einstein question is whether an aperiodic set fits inside
one orbit. So: characterize the achievable orbits.

Work out the slot algebra precisely:
- Slot (g, f) (rotation g, world face f) displays base face g⁻¹f viewed
  through an in-face rotation (the C4 action on the K×K grid); two slots
  show correlated bit-patterns exactly per this action. 24 rotations × 6
  faces = 144 slots covering 6 base faces, 24 slots each.
- Stabilizer degeneracies: a decoration with nontrivial rotational stabilizer
  has |orbit| < 24 and identified slots. For K with in-face-symmetry-breaking
  bits the generic orbit is free; characterize both regimes.
- Matching is bump/dent complementarity; derive the induced axis-wise
  compatibility relation Compat(ax, o1, o2) on orientations from the face
  pair tables (this is exactly what `arena2.py` computes at K=3 — generalize
  symbolically over K).

Then pin the right notion of "orbit(d) simulates abstract cube set S"
(target: tilings of S ↔ tilings of orbit(d), both directions — a weaker
one-way simulation only transports einsteins one way; be explicit about
which direction each application needs) and implement `orbit_embed.py`:
given S (≤24 abstract cubes + matching relation) and K, a SAT instance for
"∃ decoration d whose orbit simulates S". The unknowns are the 6K² bits;
the constraints are the slot-algebra consistency + the matching-relation
match. Feasibility note: for the equivariant-SFT view of why this is the
right question, see anyk-12 — the two cards are dual and should share
notation.

**Done when:** a written note (orbit-structure.md) with the slot algebra,
stabilizer analysis, and the simulation definition; `orbit_embed.py` working
and validated on sanity targets (e.g. S = a known periodic orbit from the
K=3 pattern library → SAT; S = a deliberately geometry-violating set → UNSAT
with an explanation).

**Blocked by:** nothing hard; benefits from anyk-12's reformulation landing
first or concurrently.

## Progress

- (2026-07-16T20:40Z) **The 2D instance of this card is COMPLETE** (as the
  dress rehearsal for 3D, see `RESULTS-2d-anyk.md`): slot algebra derived
  (`faceeq2d.py` — all 10 face equations carry the mirror twist, identity
  never occurs), reconstruction validated on 500 random decorations,
  achievability characterized exactly via gain-graph closure over
  Z2(mirror)×Z2(sign) with non-implication filter: **116 canonical
  relations, all K** (99 at K≤5 + 17 witnessed at K=6 by
  class-representative sampling, 17/17 found). Prediction = reality, no
  slack either direction.
- (2026-07-16T20:40Z) Note for the 3D lift: the "17 need K=6" phenomenon
  shows the naive genericity/union bound fails when forced symmetries
  shrink the representative space — the 3D K₀ bound must be computed, not
  assumed. Remaining on this card: the 3D slot algebra (24 rotations, 6
  faces, D4 twists incl. orientation-reversing identification) +
  `orbit_embed` for arbitrary target sets (anyk-09's input).
- (2026-07-17T00:00Z) **3D slot algebra DERIVED + VALIDATED** (`faceeq3d.py`,
  census in `faceeq3d_census.json`): every one of the 1728 Compat triples is
  a face equation F_g = ¬(F_h∘τ) with τ a signed swap — **84 distinct
  equations** (21 face pairs × 4 τ's each; 24 self-equations).
  **Reconstruction passed 200/200** against arena2's real compat tables —
  the 3D twist bookkeeping is correct. Consequences: (i) 2^84 kills the
  2D certify-everything trick, so the 3D Lean route goes through gain-graph
  achievability enumeration over D4×Z2 on 6 face-nodes (as DESIGN-anyk-lean
  anticipated); (ii) unlike 2D, the equation profile is NOT
  rotation-invariant (43/50 sample) — profiles come in rotation orbits,
  cert transport needed (K=3 stack already has that machinery);
  (iii) self-gain parity table computed: identity + both swap-diagonals
  give F=-F∘τ unsat at every K (always-fixed cells); the other five are
  odd-K-unsat / even-K-ok — the raw material for the honest K₀ bound.
- (2026-07-17T01:15Z) **THE CENSUS: 1,445,865 distinct achievable 3D
  profiles** (`countclosures.py`, engine validated by reproducing 2D's 116
  exactly; artifact `anyk3d_profiles.json`, 46MB; held-set sizes peak at 6,
  max 42). Completeness insight recorded: real profiles are automatically
  implication-closed with realized (hence feasible) stabilizers, so the
  census is a structural superset at every K, both parities — the
  genericity direction is only needed for exactness/fail-forward, not the
  theorem. Compression insights for the Lean layer: (a) monotone frontier —
  emptiness is antitone, periodicity monotone in the relation, so the
  formal cert table only needs the maximal-empty + minimal-periodic
  antichains (possibly hundreds, not 1.4M); (b) 24-orbit reduction ~÷24.
  Calibration classification of a 5,000-sample now running
  (`classify3d_sample.log`) — measures the empty/periodic/stall split;
  stalls are einstein suspects.
- (2026-07-17, overnight) **THE 3D CENSUS IS FULLY CLASSIFIED — ZERO
  APERIODIC RELATIONS.** Canonical reduction 1,445,865 → 66,134 (conjugation
  action derived via constraint-pair transport after catching the
  intrinsic-equivariance trap; validated 30 decs × 24 rotations). Campaign
  (`classify3d_all.py`, 20 workers, 99 min): 9,361 periodic + 56,718 empty +
  55 stalls. Mop-up: 53 stalls die at 5³/6³ (the campaign's 4³ ceiling was
  the only thing "wrong" with them — 3 deep probes each confirmed clean
  torus-64 sweeps). **The final 2 survivors (canon 24655, 24724): PERIODIC
  at index 64** on the same skew lattice ((2,0,2),(0,4,4),(0,0,8)) — the
  deepest screws in the space. Their anatomy: fully-connected 21-equation
  profiles with mirror-antisymmetric self-equations ⟹ **even-K-only,
  unreachable by any odd-K sweep including the entire K=3 arena** — genuine
  new territory, and it still closes. Final ledger: 9,363 periodic (max
  index 64) + 56,771 empty (boxes ≤ 6³) + 0 survivors, over every
  achievable relation at every K. **The empirical 3D any-K answer is NO —
  no aperiodic single-orbit Wang cube exists at any K.** Remaining: the
  Lean formalization (completeness lemmas + certificate table w/ frontier
  compression + assembly) — a bounded program with no mathematical
  unknowns left.
