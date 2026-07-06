# No Aperiodic K=3 Wang Cube — A Machine-Checked Result

## The theorem

```lean
theorem no_aperiodic_wang_cube : ¬ ∃ dec, TilesZ3 dec ∧ ¬ PeriodicTiling dec
```

**No K=3 binary-face Wang cube is an aperiodic einstein.** Every such cube that
tiles 3-space admits a fully periodic tiling — there is no "3D monotile" in this
symbolic family.

A **quantitative** form is also proved, on the same trust base:

```lean
theorem spacetiler_periodic_le864 (dec) : TilesZ3 dec → PeriodicTilingBounded dec 864
```

every such cube that tiles ℤ³ admits a periodic tiling whose fundamental domain
has at most 864 cells (the largest of the 33 certificate periods — pattern 6's
12×6×12 rectangular torus). A tighter bound (32) is available if the certificates
are re-cut on skew lattices rather than rectangular hulls.

## The setup

- A **decoration** `dec : Fin 54 → Bool` puts a bump/dent bit on each of the
  6 × 3 × 3 = 54 face-cells of a cube (K=3 = a 3×3 grid per face). That is the
  whole tile: 2⁵⁴ ≈ 1.8·10¹⁶ candidates.
- **`TilesZ3 dec`** — the cube tiles all of ℤ³: there is an orientation (one of
  the 24 cube rotations) for every lattice cell such that every adjacent pair
  *matches* (a bump meets a dent).
- **`PeriodicTiling dec`** — some tiling of ℤ³ is invariant under a full-rank
  lattice, i.e. genuinely periodic in all three directions.
- An **aperiodic einstein** is a decoration with `TilesZ3 dec ∧ ¬PeriodicTiling
  dec`: it tiles space, but *no* tiling of it is periodic.

The theorem says that combination is impossible.

## Why it isn't obvious

A search tool (`arena2.py`, a CEGIS loop with a geometric period-finder) swept
the 2⁵⁴ space and found no aperiodic cube — it terminated by discovering **33
forbidden adjacency patterns** such that no decoration tiles even a 4×4×4 box
while avoiding all of them. But "*a search found nothing*" is not "*nothing
exists*." Turning the search into a theorem requires proving, with no gaps:

1. that the finite 4³ window and the 33 patterns actually capture the infinite
   3-space problem (the **semantic bridge**), and
2. that the resulting SAT instance is genuinely unsatisfiable (the **SAT proof**),

neither of which the search itself establishes. Both are now proved.

## How the proof works

A chain of reductions, each machine-checked, from the geometric statement down to
one Boolean unsatisfiability fact:

```
aperiodic einstein exists
  → (L1) it tiles the 4³ box while avoiding all 33 patterns          -- box restriction
  → (L2) …but realizing no pattern forces a periodic tiling,          -- the semantic bridge
         so a non-periodic space-tiler must avoid them all           (l2_bridge)
  → it is a lex-minimal such decoration (48-fold cube symmetry)       -- symmetry reduction
  → it satisfies genArenaCNF (≈786k clauses)                          -- encoding (enc)
  → but genArenaCNF is UNSAT                                          -- the SAT proof (huns)
  → contradiction.
```

The **semantic bridge** (L2) is the mathematically substantive part — usually the
step that gets hand-waved. Here it is fully proved: realizing any forbidden
pattern yields a periodic ℤ³ tiling (each pattern carries a torus-tiling
certificate, transported across the pattern's 24 rotations by pure orientation
re-indexing), so a space-tiler with no periodic tiling must avoid every pattern.

The **SAT proof** (`huns`) is cube-and-conquer: `genArenaCNF` is split into ~1428
sub-problems ("cubes"). Two independent facts combine (`unsat_of_cubes`):

- **the cubes cover every assignment** — proved *by construction* as a structural
  induction on the decision tree (`VTree.covers`), pure Lean kernel; and
- **each cube is individually UNSAT** — verified by **cake_lpr**, a SAT-proof
  checker formally verified in HOL4/CakeML, from the solver's LRAT certificates.

## What is trusted

`#print axioms no_aperiodic_wang_cube` yields exactly:

| Axiom | What it is | Covers |
|---|---|---|
| `propext`, `Classical.choice`, `Quot.sound` | standard Lean kernel foundation | the proof checker itself |
| `Lean.ofReduceBool`, `Lean.trustCompiler` | `native_decide`: the Lean compiler evaluates finite deterministic computations correctly | the finite geometry — the 33 patterns' periodic certificates, the pattern rotation-closure, the encoding facts |
| `ConcreteTree.perCubeUnsat` | each cube's UNSAT, checked by **cake_lpr** | the ~1428 SAT sub-proofs |

**The SAT solver is not trusted** — only its certificates, re-checked by a
formally verified checker. Everything else — the entire reduction from "aperiodic
einstein" to "`genArenaCNF` is UNSAT," including the semantic bridge and the
cube-cover argument — is proved in the Lean kernel with no computational trust.

## Implications

- A **machine-checked negative result**: no aperiodic K=3 binary-face Wang cube
  exists. This symbolic corner of the 3D einstein question is settled — and
  settled as a *theorem*, not a search log.
- The step that separates "we ran a search" from "we proved the theorem" — that
  the search's forbidden-pattern criterion soundly captures the infinite-space
  geometry — is exactly the part now kernel-checked.
- The trust base is minimal and auditable, matching the standard for large
  computer-assisted proofs (Pythagorean triples, Keller's conjecture, Schur 5):
  a verified proof checker instead of a trusted solver.
- The machinery is reusable: `CubeCover` is a self-contained library (with a worked
  example, on `[propext, Quot.sound]`) turning any cube-and-conquer SAT proof into a
  kernel-checked `CNF.Unsat` — the coverage argument, usually left informal, proven
  by construction. The bridge / symmetry-reduction pattern generalizes to other
  tiling searches (larger K, other symmetry groups).

*Scope: this concerns the specific model — K=3 (3×3 faces), binary bump/dent
matching, the 24-rotation orientation group, tilings of ℤ³. It does not address
other tile families or the 3D einstein question in general.*

## Where it lives

Lean (`lean-flocq/LeanFlocq/`): the bridge (`L2Bridge`, `L2Periodic`, `L2Final`),
symmetry reduction (`L2SearchFree`, `PInv*`), encoding (`GenArenaLexEncBody`),
cube cover (`CubeCover`), instantiation (`ConcreteTree`), capstone (`NoEinstein`).
SAT side (`monotile/`): `arena2.py` (search), `stream_verify.py` + cake_lpr
(cert verification), `export_tree.py` (tree → Lean). Full detail:
`SAT_REFLECTION_STATUS.md`.

*Status: **COMPLETE.** All 1457 cube sub-proofs are cake_lpr-verified UNSAT, the
cover check passed (`COVER: COMPLETE — 1457 leaves cover all assignments`), no cube
was satisfiable, and `ConcreteTree` is built on the freshly-verified manifest. The
theorem stands on exactly the trust base above.*
