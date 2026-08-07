# RESULTS: edge-marked Wang cubes, K=1 probe (2026-08-06)

Follow-up to `RESULTS-corner-k1.md`, settling open question 2 of
`PLAN-corner-cubes.md`: are edge markings (4-ary constraints, 12 edges
per cube) worth folding in? Answer from the K=1 probe: **they are
strictly stronger than corners — but still not aperiodic at T=2/T=3.**

Code: `edge3d.py` (same encoder/tier design as `corner3d.py`).
Analysis helpers: `edge3d_late.py`, `edge3d_period3.py`.
Checkpoint data: `edge3d_T{2,3}_results.jsonl` (committed; small).

## Model

Each of the cube's 12 edges carries one of T colors; at every lattice
edge the 4 incident cube-edge colors match (rule `equal`), or pack with
exactly one bump (rule `exact1`). Edge index (a,u,v): axis a, fixed
coords (u,v) on the other two axes. Canonical under the 24 rotations.

## Structural facts (probe-relevant, Phase-B-relevant)

- **Parity decoupling.** Edge-adjacent cubes differ by (0,±1,±1)-type
  vectors — even parity. The constraint graph has TWO fully decoupled
  components: even cells and odd cells, each an FCC lattice with 12
  nearest neighbors. An edge tiling is exactly two independent FCC
  tilings. (Corner constraints decoupled by corner-slot parity; edges
  decouple by CELL parity — stronger.)
- **Counting rules are not trivially dead here** (unlike corners): a
  d³ box has 3d(d−1)² interior lattice edges, so exact-k density forces
  m = 3k marks per cube; the all-identity period-1 witness needs the
  marks additionally balanced k per axis direction. Unbalanced m=3
  decorations are not covered by the corner counting-collapse theorem.

## Census (Burnside, orbit-enumeration asserted in `sanity`)

Cycle structures on 12 edges: identity 2¹²; six 90° face rotations 2³;
three 180° face rotations 2⁶; eight 120° diagonal rotations 2⁴; six
180° edge rotations 2⁷.
- T=2: (4096 + 48 + 192 + 128 + 768)/24 = **218** canonical.
- T=3: (531441 + 162 + 2187 + 648 + 13122)/24 = **22,815** canonical.
- exact1 density-viable (m=3): C(12,3)=220 subsets → **13** canonical.

## Headline numbers (zero SUSPICIOUS everywhere)

| model | decorations | periodic | empty | SUSPICIOUS |
|---|---|---|---|---|
| edge equal, T=2 | 218 | 116 | 102 (90 @3³, 12 @4³) | 0 |
| edge exact1 m=3, T=2 | 13 | 13 | 0 | 0 |
| edge equal, T=3 | 22,815 | 2,187 | 20,628 (20,556 @3³, 60 @4³, 12 @5³) | 0 |

Runtime: T=2 in 14 s; T=3 in 33 min (8 workers).

## Edges are strictly stronger than corners (calibration for Phase B/C)

Corner witnesses never needed period > 2. Edges do:

- 4 decorations at T=2 have **no 2-power torus at all** (UNSAT at
  (1,2,2), (2,2,2), (2,2,4)) but tile at **(3,3,3)** — the first
  genuine period-3 requirements of the corner/edge campaign
  (decorations #61, #109 with 4 marks; #200, #203 with 8).
- 16 decorations at T=2 and 324 at T=3 tile only at period
  **(2,2,8)** — the torus cap-4 sweep misses them entirely.
- 6 decorations at T=3 needed **(6,6,6)** — the largest periods seen.
- exact1 m=3: the 6 axis-balanced decorations tile at period 1
  (all-identity, as the witness theorem predicts); unbalanced ones
  ({1:1, 2:2} splits) at (1,1,2)/(1,2,2); the fully unbalanced
  {2:3} decoration at (2,3,3).

So: edge equality constraints can force period 8 (and 3, and 6) — real
combinatorial content — yet every one of 23,046 decorations is periodic
or empty. Aperiodicity continues to hide nowhere at K=1.

## Sanity / validation (all passing)

- Rotation action on the 12 edges faithful; distinct per orientation.
- Census counts 218 / 22,815 match Burnside exactly.
- empty/full decorations: period-1 under equal; UNSAT at 1×1×1 under
  exact1 (m ≠ 3).
- single-marked edge under equal: explicit period-2 construction
  (S = x-parallel lattice edges at even y,z — every cube has exactly
  one) + solver independently finds the 2×2×2 torus.
- axis-balanced 3-mark exact1: all-identity witness verified + solver
  finds period 1.
- Encoder brute-force cross-checks: (1,1,1) torus for ALL canonicals
  (218/218 at T=2), (1,1,2) torus vs 576-pair enumeration on 60 random
  decorations.
- All recorded torus witnesses re-verified by the pure-python checker.

## Consequences for the plan

- Open question 2 (edges worth folding in?): **yes as a constraint
  location** — they carry real forcing power (period 3/6/8 appear) —
  but not as an easy win: no aperiodic candidate at K=1.
- The parity decoupling cuts both ways: it makes the edge model easier
  to analyze (two independent FCC problems), and it gives Phase B a
  second structural handle; a "tileable ⇒ periodic" theorem for edges
  may be provable componentwise on FCC.
- If any-K work (Phase C) ever starts, edges should be folded into the
  corner census from the start: the equation-table machinery (pairs of
  edge-positions × twists, 4-ary) is the same shape as corners, and the
  stronger forcing suggests edges+corners mixed is where an einstein
  would hide if K=1 ever has one.
- Priority remains: **Phase B** (corners — and now plausibly edges —
  provably periodic-forcing-free at all K).

## Trust profile

Same as the corner probe: Glucose3 verdicts uncertified; all torus
witnesses machine-checked by an independent pure-python verifier; the
density/identity arguments are hand-proven in
`RESULTS-corner-k1.md` and here. Probe standard, no Lean yet.
