# monotile HANDOFF (2026-08-07, corner track)

For whoever picks this up next. The short version: **the 3D corner
chirality conjecture cracked open this week**. The easy half is
formalized in Lean, and the hard direction for the chiral T=2 pair
#10/#11 is solved mathematically — the obstruction is *four cubes
around a single lattice edge*. What remains is (a) kernel-certifying
that finite fact in Lean, (b) the reduction lemma, (c) generalizing to
all chiral decorations, (d) K=2. Read `DESIGN-corner-chirality.md`
first (it is current); this file is the operational summary.

## Where the tracks stand

1. **Bump/dent Wang cubes (any K)** — COMPLETE. `no_aperiodic_wang_cube_anyK`
   proven in lean-flocq (`AnyK3DMain.lean`), modulo the cake_lpr-evidenced
   axiom `frontierEmptyFacts`. See `RESULT.md`, `DESIGN-anyk-lean.md`.
2. **Equal-color Wang cubes (any K, any T)** — COMPLETE.
   `no_aperiodic_equal_color_wang_cube` proven (`AnyK3DColorMain.lean`),
   all 414,079 canonical profiles covered. See `PLAN-color-lean.md` and
   the 2026-08-04 revision of this file (git history) for details.
3. **Corner-marked Wang cubes (Phase B)** — ACTIVE. Conjecture C
   (`DESIGN-corner-chirality.md`): a K=1 corner decoration tiles ℤ³ ⟺
   it is achiral ⟺ it admits a period-(2,2,2) tiling. Status below.
4. **Mixed faces+corners** — probed only (776 T=2 canonicals, 100
   chiral-but-tileable exist here, so the chirality theorem does NOT
   extend to mixed). See `corner_mixed3d.py`.

## Corner track — what's DONE

| piece | status | where |
|---|---|---|
| 2D theorem (tileable ⟺ achiral ⟺ period-2), full proof | **in Lean, kernel-clean** | lean-flocq `Corner2D.lean` (commit 012109f) |
| 3D easy half (achiral ⟺ period-(2,2,2) ⟹ tileable) | **in Lean, kernel-clean** | lean-flocq `Corner3D.lean` (commit a4c14ed) |
| 3D census cross-check (23/21 @ T=2, 333/201 @ T=3) | native_decide, matches Python | `Corner3D.lean` census section |
| Reduced dimer model for #10/#11, EXACT | verified vs orientation encoding, all shapes MATCH | `corner3d_dimer.py` part 3 (commit 161bf40) |
| Transfer-graph localization (4×4 dies at L=3; 3×4/4×3 at L=4) | verified, cross-checked | `corner3d_transfer.py` (commit 94747be) |
| **The one-edge obstruction**: 4 cubes around one lattice edge, UNSAT | SAT-core + brute force (12⁴, 0 survivors, both parities, all 3 edge orientations) | `corner3d_core_hunt.py`, `corner3d_edge.py` (commit 94747be) |
| **Kernel certificate of the edge UNSAT** | **in Lean, `decide`, axioms [propext]** | lean-flocq `Corner3DEdge.lean` (commit 3ff52b6) |
| **Reduction: #10/#11 don't tile ℤ³** | **in Lean, kernel-clean** | lean-flocq `Corner3DDec10.lean` (commit 87cdf47) |
| **THE T=2 THEOREM: tileable ⟺ achiral, both directions** | **in Lean, kernel-clean** | `corner3d_T2_iff`, `Corner3DDec10.lean` (commit b4b9df2) |

Trust base so far: the Lean files use only propext / Classical.choice /
Quot.sound (verified by `#print axioms`; `native_decide` only in the
census cross-check, explicitly outside the theorem trust base). The
one-edge UNSAT is currently Python-verified only — but solver-free
(pure 20736-case enumeration), so it is a *finite check*, not SAT-solver
evidence. This track is strictly cleaner than the face tracks; keep it
that way (no cake_lpr debt needed anywhere).

## The one-edge obstruction (the key new object)

In the reduced model for #10: each cube picks an ordered pair of
adjacent faces (A-face, B-face) — the faces carrying its absolute-even
resp. absolute-odd marked diagonals — with axis-cyclic class +1 at even
cubes, −1 at odd cubes (the parity flip), 12 choices per cube. Vertex
glue: incident cubes agree on marks at every lattice vertex.

**Theorem (finite, verified, not yet in Lean).** The 4 cubes around any
lattice edge, with mark agreement at every vertex shared by ≥ 2 of them
(the 4-wise vertex at each end of the edge, plus 4 pairwise vertices
per end plane — 10 shared vertices total), admit no valid assignment:
0 of 12⁴ = 20736 assignments survive, for both parity phases and all
three edge orientations. Any #10-tiling of ℤ³ restricts to such a
system around every edge ⇒ **#10 and #11 do not tile ℤ³**.

Structure for the human proof (from `corner3d_edge.py`): the obstruction
is distributed — no single agreement is individually essential.
Dropping the 4-wise central agreement leaves 84 near-misses, which can
make the central marks constant on either end plane separately (24+24)
but never both at once: **the two ends of the edge cannot
simultaneously close**. A clean case analysis (or a clever invariant)
is still wanted.

Corrections to earlier beliefs (now documented in the scripts):
- The screw-handedness determinant is NOT the rotation invariant; the
  class is purely the cyclic sign of the (axis A, axis B) pair.
- The naive ordered-pair orbit is all 24 pairs; the 12-pair orbit
  appears only after accounting for the parity-swap of 90° rotations
  (the #10 stabilizer has order 2).
- Vertex glue needs no cardinality gate: "sum ∈ {0,8}" is an all-equal
  chain.

## What REMAINS (in priority order)

### N1/N2 — DONE (2026-08-07, same day as the handoff)

The edge-system kernel certificate (`Corner3DEdge.edge_unsat`) and the
full reduction + assembly (`Corner3DDec10.corner3d_T2_iff`) are
committed. **The T=2 3D corner chirality theorem is closed.** What
remains is T ≥ 3 and K > 1.

### N3. Generalize to all chiral d (T ≥ 3) — BREAKTHROUGH (2026-08-07)

**The one-vertex system is a complete chirality detector at T=2 and
T=3** (commit 36b1084): the 8 cubes around one lattice vertex, any
rotation of d each, colors agreeing at shared vertices — UNSAT exactly
for the chiral canonicals (2/2 and 132/132, zero false positives among
the 222 achiral). The full K=1 theorem at any T now reduces to:

1. **One GENERIC reduction lemma in Lean** (decoration-independent):
   `VertexSystemUnsat d → ¬ ∃ ℓ, IsTiling d ℓ`. No per-type dimer
   machinery — IsTiling gives an orientation per cube and shared
   vertices agree because ℓ is a function. Straightforward adaptation
   of `dec10_not_tileable`'s assembly.
2. **132 finite certificates** (T=3): 102 edge-4 cores (n⁴, the
   `edge_unsat` pattern — n = orbit size ≤ 24), 6 tetrahedral-4 cores,
   24 genuine 6-cube cores (24⁶ too big for kernel `decide` directly —
   use pattern projection: patterns agreeing on all shared vertices are
   interchangeable, collapsing n; or `native_decide` as an explicitly
   declared trust step like the color track's batch checks).
3. **Chirality classification** at T=3: `decide` over 3⁸ = 6561
   decorations (the `chiral_T2_cases` analog).
4. Transport: already proven (`isTiling_of_comp_rot/mirror`).

The uniform conjecture (any T: chiral ⟺ one-vertex-UNSAT) is now the
headline open problem — if true, the K=1 corner chirality theorem is
one generic lemma + finite checks for every T.

### N4. K=2 probe — CHEAP, worth doing before N3 hardens beliefs

`PLAN-corner-cubes.md` item: corners carry 2×2×2 patterns, twist = C3
per vertex. The design doc warns the any-K corner theorem is untested
even empirically. A K=2 census + chirality probe with the existing
encoder pattern settles whether "tileable ⟹ achiral" plausibly
survives K>1.

## Operational notes (corner track)

- Python: run everything via `./runpy.sh <script.py>` (NixOS
  LD_LIBRARY_PATH dance for the venv's numpy/python-sat wheels).
- `import corner3d` needs `sys.argv` patched (`sys.argv = ["corner3d.py"]`)
  before import — it reads argv at module level. `corner3d_transfer.py`
  has a `main()` guard; `corner3d_edge.py`/`corner3d_core_hunt.py` run
  their analysis on import.
- Lean builds: `cd lean-flocq && lake env lean LeanFlocq/<Module>.lean`
  for standalone modules (Corner2D/Corner3D are NOT in the lib import
  graph — build directly). ~2 min for Corner3D (Mathlib import +
  kernel decides). Parallel `lake build` across modules max 4 jobs
  (machine crashes above that).
- Kernel `decide` over `Fin 24`-indexed tables: ∃-search formulations
  time out (whnf heartbeats); use exported certificate tables +
  pointwise checks (the `rotCompTab` pattern in `Corner3D.lean`).
  `∀ a b : Fin 24, ∃ c, ...` = ~55k point-evals is too much;
  `∀ a b p, f a b p = table a b p` with a 24×24 table is fine.
- Python closure pitfall that cost an hour: SAT variable-block
  numbering via a mutated `top` accumulator captured in closures
  silently ALIASES the blocks (bottom/top interface bits became the
  same variables). Compute block offsets as separate names; never
  close over a mutated counter. (Fixed in
  `corner3d_transfer.SliceSolver`; `corner3d_dimer.dimer_sat` never had
  it.)
- Box vs torus in the transfer decomposition: box-end slices have one
  plane unchanneled (boundary vertices aren't glue-constrained — the
  Phase-0 box convention constrains only fully-interior vertices).
  Getting this wrong makes every cross-section die at L=2.

## File map (corner track)

- `monotile/DESIGN-corner-chirality.md` — THE doc: conjecture C, 2D
  proof template, 3D mechanism, the one-edge obstruction, Lean plan.
- `monotile/PLAN-corner-cubes.md`, `monotile/RESULTS-corner-k1.md` —
  Phase 0 campaign (all K=1 models resolved, zero aperiodic candidates).
- `monotile/corner3d.py` — Phase 0 encoder/census (source of truth for
  CORNERS/SIG tables; sanity checks run on import via corner3d.py main).
- `monotile/corner3d_chiral.py` — chirality census cross-checks
  (T=2, T=3, mixed).
- `monotile/corner3d_dimer.py` — reduction exactness, rigidity probe,
  and the EXACT reduced-model SAT encoding (part 3) with lift-checks.
- `monotile/corner3d_transfer.py` — slice/interface transfer machinery
  (`SliceSolver`, `Cylinder`), death table, cross-checks vs corner_sat.
- `monotile/corner3d_core_hunt.py` — assumption-based UNSAT core +
  greedy deletion (found the 4-cube core).
- `monotile/corner3d_edge.py` — solver-free brute force of the edge
  system + near-miss dissection (84 near-misses, both planes can't
  close).
- lean-flocq: `LeanFlocq/Corner2D.lean` (2D theorem, done),
  `LeanFlocq/Corner3D.lean` (easy half + spec layer + census, done).
  Next module: `LeanFlocq/Corner3DEdge.lean` (N1), then the reduction
  (N2).
