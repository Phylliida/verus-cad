# A completed einstein result — request for next-step advice (self-contained)

This is a briefing for a proof/research advisor. It assumes **no prior context**.
It describes a finished, machine-checked result, its structure, and a set of open
directions, and asks which to pursue next. Full detail lives in `RESULT.md` (result
+ trust base), `SCREW_STRUCTURE.md` (the human-legible structure), and
`SAT_REFLECTION_STATUS.md` (the Lean/SAT internals), but this doc stands alone.

---

## 1. The problem

An **einstein** (or aperiodic monotile) is a single tile that tiles space, but *only*
aperiodically — no tiling of it is periodic. In 2-D this was resolved in 2023 (the hat /
spectre). In **3-D it is open**. This project attacks a symbolic corner of the 3-D
question: **Wang cubes**.

- A **K=3 Wang cube** is a cube whose 6 faces each carry a 3×3 grid of bump/dent bits — so
  a "tile" is a decoration `dec : Fin 54 → Bool` (6·3·3 = 54 bits). The space of tiles is
  2⁵⁴ ≈ 1.8·10¹⁶.
- Cubes **tile** ℤ³ if you can place a rotated copy (one of the 24 cube rotations) in each
  lattice cell so that every pair of touching faces *matches* — a bump meets a dent.
- A decoration is an **aperiodic einstein** if it tiles ℤ³ but **no** tiling of it is
  invariant under a full-rank translation lattice.

**Question:** does any K=3 Wang cube achieve this?

## 2. What was proven (Lean 4, machine-checked)

**No.** Formalized as:

```lean
no_aperiodic_wang_cube     : ¬∃ dec, TilesZ3 dec ∧ ¬ PeriodicTiling dec
spacetiler_periodic_le864  : ∀ dec, TilesZ3 dec → PeriodicTilingBounded dec 864
```

i.e. every K=3 Wang cube that tiles ℤ³ admits a fully periodic tiling — with, in the
second theorem, a fundamental domain of at most 864 cells. No 3-D "monotile" exists in
this symbolic family.

**Trust base** (`#print axioms`, both theorems): `propext, Classical.choice, Quot.sound`
(Lean kernel) + `Lean.ofReduceBool, Lean.trustCompiler` (`native_decide`, used only on
finite geometric data) + one external-input axiom `ConcreteTree.perCubeUnsat` (see §4).
**The SAT solver is not in the trust base** — only re-checked certificates are.

*Scope caveat:* this is the specific model — K=3, binary bump/dent matching, the
24-rotation orientation group, tilings of ℤ³. It does not address other tile families or
the general 3-D einstein question.

## 3. How the proof is structured

A chain of reductions, each machine-checked, from the geometric statement to one Boolean
unsatisfiability fact. The search tool `arena2.py` (a CEGIS loop with a geometric
period-finder) had swept the 2⁵⁴ space and terminated by discovering **33 forbidden
patterns** — local adjacency configurations — such that no decoration tiles even a 4×4×4
box while avoiding all of them. The formalization turns "the search found nothing" into a
theorem:

```
an aperiodic einstein exists
  → (L1) it tiles the 4³ box while avoiding all 33 patterns           [box restriction]
  → (L2) but realizing any pattern forces a periodic tiling,           [the semantic bridge]
         so a non-periodic space-tiler must avoid them all            (l2_bridge, kernel-proven)
  → it is lex-minimal under the 48-elt symmetry group                 [symmetry reduction]
  → it satisfies genArenaCNF (785,686 clauses)                        [encoding, enc]
  → but genArenaCNF is UNSAT                                          [the SAT proof]
  → contradiction.
```

The **semantic bridge (L2)** is the mathematically substantive part — usually the step
left informal. Here it is fully kernel-proven: each forbidden pattern carries an explicit
torus-tiling certificate, transported across the pattern's 24 rotations by pure
orientation re-indexing, so realizing a pattern yields a genuinely periodic ℤ³ tiling.

*Note on the symmetry group:* the 48 elements are **24 rotations × {identity, global
bit-complement}** — there are **no spatial reflections**. The bit-complement acts
trivially on orientations and requires no pattern-closure. (Audited in the Lean source, in
case a referee asks.)

## 4. The SAT proof (`genArenaCNF.Unsat`)

Cube-and-conquer, fully discharged:

- `genArenaCNF` was split into **1457 "cubes"** (partial assignments). Each `genArenaCNF ∧
  cube` was proved UNSAT by cadical and the LRAT certificate re-checked by **cake_lpr** (a
  SAT-proof checker formally verified in HOL4/CakeML). All 1457 verified; **none was
  satisfiable**.
- The cubes are the leaves of a binary decision tree; that they **cover every assignment**
  is proved *by construction* in Lean (`CubeCover.VTree.covers`, on the minimal axioms
  `[propext, Quot.sound]`, no `native_decide`), and the leaf set passed a completeness
  check.
- `unsat_of_cubes` composes cover + per-cube UNSAT ⟹ `genArenaCNF.Unsat`. The single
  external axiom `perCubeUnsat` asserts the 1457 per-cube UNSAT facts, each discharged by
  cake_lpr. Everything else — cover, composition, the whole reduction — is Lean-kernel.

(An honest field-standard trust profile, matching Pythagorean-triples / Keller / Schur-5.
An attempt to internalize LRAT checking via `native_decide` fails on scale: the raw certs
were ~87 GB and you cannot compile GB-scale literals; streaming an external verified
checker is the only viable route at this size.)

## 5. The key structural insight (what the 33 patterns *are*)

Decoding the 33 forbidden patterns: **every one is a screw.** The cube translates in two
directions and *rotates as it translates* in the third (a screw motion), or a 2-D
combination. The rotation-cycle length equals the period. Of the 33: **7 are axis-aligned**
— pure screws about a coordinate axis, with orders exactly **{1, 2, 3, 4}, the element
orders of the cube's rotation group** — and **26 are skew** (tilted-axis screws, longer
hull-cycles). (The skew hulls are why the *formal* period bound is 864 rather than the
intrinsic-skew max of 32.)

This gives a one-sentence reading of the whole 785,686-clause proof:

> **You cannot build an irrational screw out of a finite group.** A cube tiles by screw
> motions; its orientations form a finite group (24 rotations), so any screw must *close*
> (finite order) — and a closed screw is exactly a translation period. So every space-tiler
> is periodic.

This is precisely the symbolic obstruction that separates this family from a real 3-D
einstein: the **Schmitt–Conway–Danzer** tile achieves aperiodicity via an *irrational*
screw that never closes; a finite symbolic rotation group only permits rational screws,
which always close. This is a *reading* of the machine proof, not a second proof (the SAT
half is what rigorously establishes that *every* space-tiler realizes such a screw).

## 6. Status

**Complete.** The theorem compiles on the trust base in §2; the SAT verification finished
(1457 cubes verified, cover complete, no satisfiable cube); `ConcreteTree` is built on the
fresh verified manifest. Nothing is left running.

## 7. Open directions — please advise which to pursue

1. **Finish a hand-proof.** The screw decode makes *"every valid K=3 screw closes ⟹
   periodic"* an elementary finite-group statement (and the L2 bridge already proves the
   analogue in Lean). The only gap to a solver-free paper-proof is *"every space-tiler must
   contain a screw"* — currently the SAT content. **Is there a clean structural argument for
   that half?** It would remove the solver from the result entirely.
2. **Cover all K.** A K-cube under 24 rotations is a Wang-cube *set* constrained to a single
   symmetry orbit. Culik–Kari-style aperiodic 3-D sets exist with ~20 unconstrained cubes;
   the einstein question here is: *can an aperiodic set fit inside one rotation orbit?* A
   symmetry obstruction valid for all K would beat any per-K SAT sweep. (Note: aperiodicity
   is monotone under face refinement — a K-cube lifts to an mK-cube by block-copying bits —
   so K=3 already covers K=1; K=2 is 24 bits and empirically cheap.)
3. **Minimal certificate.** Are all 33 patterns necessary (UNSAT-core minimization)? Is 4³
   the minimal window, or does 3³ suffice? Both are cheap SAT experiments; a smaller,
   minimal certificate is more elegant and more likely to be human-interpretable.
4. **Tighter bound.** Reduce the 864 fundamental-domain bound to the intrinsic 32 by
   re-cutting certificates on skew lattices (needs a `reduce_vec` + lattice-lemma engine).
5. **Phase diagram / undecidability.** Map where aperiodicity first appears across
   (K, alphabet size, orientation subgroup, matching relation); and whether the single-cube
   tiling problem becomes undecidable for large K.
6. **Packaging.** The `CubeCover` library ("cube-and-conquer SAT proof → kernel theorem")
   and the screw characterization are each plausibly independently publishable.

**The specific question:** given the screw structure is now explicit, is (1) reachable —
is there a clean argument that every space-tiler contains a screw? — or is (2) the better
bet for a statement covering all K? And is anything in (3) worth doing first as a quick,
high-legibility win?
