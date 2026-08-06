# PLAN: corner-marked Wang cubes — the next dial (2026-08-04)

**Motivation.** The two face tracks prove: NO face-only decoration of a
cube — bump/dent or equal-color, any grid K, any palette — is an
aperiodic einstein. A 3D-printable monotile einstein therefore NEEDS a
new constraint location. Corners are the natural next dial (and the
most printable: corner tabs/notches are easy geometry). Reflections are
excluded on purpose — a physical tile has no mirror image, and our 24
orientations are the rotation group, which stays.

**The arity jump (why this is a new theory, not a clone).** On the
cubic lattice a face is shared by exactly 2 cubes (all our machinery is
a 2-body nearest-neighbor SFT), but a lattice VERTEX is shared by 8
cubes and an EDGE by 4. Corner/edge markings are 8-/4-ary constraints.
The gain-group census structure does not obviously port; see "any-K"
below for where it does.

## The models (increasing ambition)

**M-corner (K=1, beachhead).** Each cube corner carries one of T
colors. A tiling is an orientation field ω : ℤ³ → Fin 24 such that at
every lattice vertex, the 8 incident corner colors are all equal.
Decoration count is TINY (Burnside, rotation orbits of T^8 colorings):
**23 orbits at T=2, 333 at T=3**. Mixed face+corner at K=1: 776 orbits
at T=2. No census machinery needed — brute-force enumeration.

**M-corner-anyK.** Each corner carries a K×K×K octant pattern; matching
at a vertex = all 8 patterns identical through the corner twists (the
vertex isotropy group C3, order 3 — cyclic axis permutations). This one
DOES have the equality/gain structure: "identical through a twist" is
transitive, so classes/gains/stabilizers exist and the color-track
proof skeleton ports. Equation table = pairs of corner-positions that
can meet at a vertex × twist — the analogue of the 84 face equations,
derivable from the same arena geometry that produced
`faceeq3d_census.json`.

**M-mixed-anyK.** Faces AND corners marked. The richest model (and the
one where an einstein is most likely to hide if pure corners are too
weak). Census = face classes × corner classes.

**Rule variants for K=1 (physically motivated).** Instead of all-equal
at a vertex, packing rules: "exactly one bump per vertex", "≤ k bumps",
etc. No gain structure (counting, not equality) — but at K=1 the
decoration space is so small it doesn't matter. These are also the most
3D-printable: a vertex where 8 corner shapes must physically pack.

## Phase 0 — Python probe (hours; do FIRST, decides everything)

- Generate the 24-rotation action on the 8 corners (and the
  corner-incidence geometry: for each lattice vertex, which
  (cell-offset, corner) pairs meet). Reuse the arena/geometry code that
  generated the face tables.
- Enumerate the 23 (T=2) / 333 (T=3) corner-only canonical decorations;
  optionally the 776 mixed ones.
- Per decoration, classify: box-UNSAT (no tiling) vs torus witness
  (periodic) vs *suspicious* (neither found). Infrastructure exists:
  the CNF encoding is again pairwise exclusion — at each vertex, for
  each pair of incident cells, forbid orientation pairs whose corner
  colors differ (or that violate the packing rule). Box CNF + cadical +
  torus solver from the face tracks carry over with a new encoder.
- Sanity checks on the way: the empty decoration tiles (trivial), the
  all-marked decoration tiles, single-marked-corner decoration: tilings
  correspond to "marked vertices come in complete 8-clusters" — a good
  correctness puzzle for the encoder (no period-2 orientation map
  exists; find what the solver finds).

**Decision point.** If a suspicious/aperiodic decoration appears at
K=1 → Phase A. If everything is clean periodic/empty and boring → the
interesting question is whether corners are PROVABLY too weak (Phase B)
or whether any-K resolution unlocks aperiodicity (Phase C).

## Phase A — an einstein found (days)

- Confirm aperiodicity rigorously (no torus of any size; hierarchical
  substitution structure if it exists — look for it in the solver
  output).
- Lean: at K=1 the census is 23–776 decorations — plausibly a
  self-contained `native_decide`-scale formalization, much smaller than
  the face tracks.
- 3D print: corner tabs/notches per the winning decoration.

## Phase B — corners provably too weak (unknown; research-flavored)

- Try to prove: every corner-only decoration that tiles, tiles
  periodically — for ALL K at once, combinatorially (corner constraints
  only link diagonally adjacent cells; product/lift constructions may
  give periodic tilings cheaply). If true, a beautiful theorem and it
  kills the corner search space in one stroke.

## Phase C — any-K campaign (days-to-weeks; the color-track clone)

- Corner equation tables + `shownTable`-style cross-checks.
- M1/M2/M3b clone with gain group = C3 corner twists (order 3 — much
  smaller than 8/16; the census may be correspondingly gentler).
- Classification: density lemma (the counting argument is arity-
  agnostic — check), box-UNSAT frontier + cadical/cake_lpr (the whole
  R2 pipeline reuses verbatim), torus witnesses.
- Same trust profile as the face tracks.

## Open questions to settle in Phase 0

1. Exact constraint semantics at a vertex: all-8-equal vs pairwise
   equality through twists (they coincide for K=1; for any-K the twist
   matters).
2. Whether edge markings (4-ary) are worth folding into the probe —
   same machinery, another dial.
3. The mixed model's equation table size (face equations + corner
   equations + do faces and corners interact? — physically NO, they're
   independent constraint sets; the decoration just has both parts).

## What transfers from the face tracks (free)

- Rotation/transport algebra, torus witness format + solvers, box-CNF
  + cadical + cake_lpr pipeline (`gen_color_empty_certs.py` /
  `gen_bumpdent_certs.py`), the density-lemma counting argument shape,
  and the Lean SFT layer pattern (`IsTiling` over orientation fields).
- The hard-won operational lessons (see HANDOFF.md): chunked
  native_decide, big-data hygiene, 4-job batching, cert delete-after-
  check discipline.

## Honest effort estimate

- Phase 0: hours to a day.
- Phase A: days (mostly rigor + print).
- Phase B: unknown (a real theorem, would be the elegant outcome).
- Phase C: ~a week with the clone infrastructure, more if the corner
  census surprises.
