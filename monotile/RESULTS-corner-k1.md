# RESULTS: corner-marked Wang cubes, Phase 0 (2026-08-06)

Phase 0 of `PLAN-corner-cubes.md` is **complete**. Verdict: **no
aperiodic decoration at K=1 in any of the models** — corner-only equal
(T=2 and T=3), corner-only packing rules, and mixed face+corner (T=2).
Everything that tiles, tiles with a small torus; everything else is
box-UNSAT. The decision point resolves to: corners at K=1 are boring,
and there is now strong evidence + a concrete strategy for Phase B
("corners provably too weak, all K").

All code: `corner3d.py` (corner-only), `corner_mixed3d.py` (mixed).
Checkpoint data (gitignored): `corner3d_T{2,3}_results.jsonl`,
`corner_mixed3d_T2_results.jsonl`. Helper probes: `corner3d_inspect.py`,
`corner3d_empties.py`, `corner_mixed_late.py`.

## Headline numbers

| model | decorations | periodic | empty (box) | SUSPICIOUS |
|---|---|---|---|---|
| corner equal, T=2 | 23 | 21 | 2 (@4³) | 0 |
| corner equal, T=3 | 333 | 201 | 132 (120 @3³, 12 @4³) | 0 |
| corner exact1, T=2 | 23 | 1 | 21 | 2 → resolved (density, below) |
| mixed face+corner, T=2 | 776 | **432 (2 late)** | **344 (100 @3³, 112 @4³, 132 @5³)** | 0 |

**ERRATUM (2026-08-07).** The original version of this document
reported the mixed row as 394 periodic / 382 empty. That run had a
numbering bug: `CORNERS` was in `itertools.product` (z-fastest) order
while the encoder indexed corner slots with `cidx` (x-fastest), so the
corner part of each decoration was effectively mirrored (x↔z) while the
face part was not — not a lattice symmetry of the mixed model, so the
old mixed campaign classified a different (corners-mirrored) model.
Fixed by making `CORNERS` x-fastest (position == cidx) and regenerating
all checkpoints; the table above is the corrected mixed model. The
corner-only rows are unchanged: mirroring a decoration never changes
its verdict (lattice reflections map tilings to tilings), so the
corner-only verdicts were correct even with the swapped numbering.
The same bug also silently affected nothing else: `edge3d.py` and
`corner2d.py` use self-consistent numberings (verified: position ==
index there).

Encoder: Glucose3 CNF, one-hot orientations per cell + one-hot color
vars per vertex/interface with binary channeling. Tiers per decoration:
torus sweep cap 4 → box 3³ → box 4³ → torus cap 8 → box 5³ → SUSPICIOUS.
All torus witnesses re-verified by a pure-python checker before
recording (house self-check discipline).

**Every periodic witness found has period ≤ 2 per axis** in the
corner-only models (T=2: two at (1,1,1), rest ≤ (2,2,2); T=3: all ≤
(2,2,2)). In the mixed model (corrected run): 364 at period ≤ 2, 64 at
(2,4,4), and two at **(2,6,6)** — both have tetrahedral corner parts
(one even tetrahedron, one odd) plus 3 marked faces. This uniformity of
tiny periods was the strongest Phase-B signal — and has now (2026-08-07)
crystallized into the chirality conjecture; see
`DESIGN-corner-chirality.md`.

## The packing-rule collapse (kills the "rule variants" bullet)

The two exact1 SUSPICIOUS decorations (#2 edge pair, #3 face-diagonal
pair, both 2-marked) are **not** aperiodic candidates — they cannot tile
at all, by counting:

**Density lemma.** Under rule "exactly k bumps per vertex", a decoration
with m marked corners tiles ℤ³ only if m = k. Proof: in a d×d×d box the
cells carry m·d³ bumps; the (d−1)³ interior vertices require exactly
k(d−1)³; boundary vertices absorb at most 8((d+1)³−(d−1)³) = 48d²+16.
So m·d³ ≤ k(d−1)³ + 48d² + 16 and m·d³ ≥ k(d−1)³; d→∞ gives m = k.
(For exact1 with m = 2 the inequality first fails at d = 46 — far beyond
SAT reach at box 5³, which is why they read as SUSPICIOUS.)

**All-identity witness.** If m = k, the constant orientation field
ω ≡ id is a valid exact-k tiling: at vertex v the 8 incident corners are
exactly the 8 corner-positions μ ∈ {0,1}³ of the cells v−μ, so the bump
count at v is m, independent of v. Period 1. (The same holds verbatim
for ≥k / ≤k rules with m ≥ k / m ≤ k, and the density lemma gives the
m < k / m > k obstructions.)

**Corollary: no counting rule (exact-k, ≥k, ≤k on vertex bumps) can
force aperiodicity — whenever it tiles, it tiles at period 1.** This
closes the plan's "rule variants for K=1" section entirely, at any
palette. With the natural any-K semantics (bumps at sub-positions of the
8 incident octants), all-identity still witnesses period 1 whenever the
count matches, so counting rules stay trivial at every K.

exact1 at T=2 is thereby fully classified: only the single-mark orbit
(m = 1) tiles, and it does so at period 1 (found by the sweep; the
period-2 2ℤ³ construction of the sanity check is an alternative
witness).

## Equal-rule details

- T=2: 21 periodic, 2 empty at box 4³: decorations #10 and #11, the two
  4-mark orbits that are 3-edge paths joining antipodal corners.
- T=3: 201 periodic, 120 empty at box 3³, 12 empty at box 4³. 9 s total.
- No decoration needed torus > (2,2,2). Period-1 tilings are rare (2 at
  T=2: empty and full decorations; 3 at T=3).

## Sanity / validation performed (all passing)

- Rotation group: 24 distinct signed permutation matrices, closed,
  faithful on corners; face action cross-checked against faceeq3d's
  convention.
- Census counts by direct orbit enumeration: 23 (T=2 corner), 333 (T=3
  corner), 776 (mixed) — all match the Burnside numbers in the plan
  (re-derived independently).
- empty/full decorations tile at period 1 in every model.
- single-marked corner: explicit period-2 tiling from S = 2ℤ³
  (construction verified) + solver independently finds it. **This
  corrects the plan's parenthetical** ("no period-2 orientation map
  exists") — one does exist; fixed in the plan.
- single-marked exact1: period-2 via a GL(3,2) shift σ(c) = Ac; empty
  and full decorations UNSAT at 1×1×1 under exact1.
- box 2³ (single constrained vertex) cross-checked against exact brute
  force for all 23 T=2 corner decorations.
- mixed encoder cross-checked against brute force on the (1,1,2) torus
  (576 orientation pairs, includes self- and double-adjacency) on 200
  random decorations.

## Consequences for the plan

- **Phase A (einstein at K=1): dead** for corner-only and mixed K=1.
- **Phase B (corners provably too weak, all K) is now the recommended
  next step**, with three concrete leads:
  1. Empirical: every tileable K=1 decoration — 216 corner-only +
     394 mixed — has period ≤ 2 (corner part). A theorem of the form
     "corner-tileable ⇒ period-2 witness exists" would not be surprised
     by any data point we have.
  2. Structural: the corner slots split by vertex parity into two
     tetrahedra; the rotation group acts as S4 on the 4 body diagonals,
     with A4 preserving and odd permutations swapping the tetrahedra.
     Vertex constraints at even vertices read only even slots, so the
     model is two FCC-sublattice equality systems coupled only through
     the shared per-cell permutation — a strong handle for a
     combinatorial proof.
  3. The counting-rule collapse (above) is already a first theorem of
     exactly this flavor.
- **Phase C (any-K corner census)** should wait on Phase B: if corners
  are provably periodic-forcing-free at all K, Phase C is unnecessary;
  if Phase B stalls on a specific configuration, that configuration is
  the targeted Phase-C search space.
- Open question 1 (twist semantics) is settled for any-K work: pairwise
  equality through the C3 corner twist is the only physically meaningful
  reading and the one with gain structure. Open question 3 answered
  empirically: faces and corners do not interact (independent constraint
  sets), and the mixed census classifies with zero friction (776/776,
  3 min).
- Edge markings (open question 2, 4-ary) remain unexplored — but note
  edges inherit the same parity-split suspicion: worth a one-afternoon
  probe in the same style before committing to Phase B/C.

## Trust profile

Probe-level only (Phase 0 standard): Glucose3 results are uncertified;
torus witnesses are machine-checked by an independent pure-python
verifier; box-UNSAT verdicts rest on the solver. The density lemma and
all-identity witness are hand-proven in this document. Nothing here is
Lean-backed yet; if Phase B goes ahead, the K=1 census is small enough
(23 + 333 + 776) for native_decide-scale formalization, far cheaper
than the face tracks.
