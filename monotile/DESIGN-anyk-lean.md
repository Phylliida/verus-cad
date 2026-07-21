# DESIGN: formalizing "no aperiodic Wang cube at any K" (v0.1)

Danielle's question (2026-07-16): can Lean prove, assuming enough SAT results,
that *no* K admits an aperiodic Wang cube? Answer: plausibly yes — the
orientation-SFT reduction makes the SAT layer K-independent. This note is the
anyk-12 deliverable, architecture level; proofs and enumerations to follow.

## 1. The reduction (K vanishes)

Fix a decoration d at parameter K with free rotation orbit. A tiling of ℤ³ by
orbit(d) is exactly an orientation field ω : ℤ³ → Rot24 subject to
nearest-neighbor constraints

    Compat_d(ax, ω(c), ω(c + e_ax))     for all c, ax ∈ {x,y,z},

because the tile in cell c is determined by ω(c) (tile = ω(c)·d). Periodicity
of the tiling = periodicity of ω. **Compat_d ⊆ {x,y,z} × 24 × 24 is a finite
object on a fixed alphabet regardless of K.** Two decorations with equal
Compat have the same tilings up to relabeling. So:

> An aperiodic Wang cube exists at some K
> ⟺ some *achievable* equivariant relation R has a nonempty, aperiodic SFT.

Structural facts to prove in Lean:
- (R1) the ≅ above, both directions, periodicity transported. The hard
  geometric core is already proven at K=3: rotation acts by pure orientation
  re-indexing (`PInvFinish.lean`, `pairs_equiv`, κ = identity). Needs
  restating K-parametrically.
- (R2) stabilizers: a decoration with rotational self-symmetry S ≤ Rot24 has
  orbit of size 24/|S| and the tiling ≅ a coset-SFT on Rot24/S. Finitely many
  S up to conjugacy (the subgroup lattice of the rotation group). Alternative:
  prove tilability/periodicity transfers to a free-orbit refinement and treat
  only the free case (check whether symmetric decorations always lift to
  free ones at larger K with the same tilings — likely via a
  symmetry-breaking block-copy perturbation; if messy, do the coset cases).
- (R3) equivariance of Compat_d (the 48-group acts; flip fixes Compat, so
  only the 24 rotations act on relations) — the `check_equivariance` fact,
  already native_decide'd at K=3.

## 2. Achievability (the new math)

Which equivariant relations arise as Compat_d for some d at some K?

Compat_d is determined by which *face equations* hold. For faces g, h of the
base cube and a grid isometry τ ∈ D4 (the touching-face identification
includes an orientation-reversing map — bookkeep carefully, coordinates as
ground truth like arena2):

    E(g, h, τ):   F_g = ¬ (F_h ∘ τ)

where F_1..F_6 : [K]² → {±1} are the face grids. Each Compat(ax, o1, o2) is
one instance E(g(o1,ax), h(o2,ax), τ(o1,o2,ax)) with the finite index data
computable from the rotation action. So a relation R is achievable at K iff
the constraint system {E(...) : R says compat} ∪ {¬E(...) : R says incompat}
has a solution in face-functions.

Shape of the characterization (to prove):
- The equalities generate a gain graph over D4 × Z2 (twist τ, negation) on
  the 6 faces. Consistency = no cycle forces F = -F ∘ σ where σ has a fixed
  cell (fixed-point analysis brings in K's parity — e.g. axis reflections fix
  a column iff K odd). Union over all K = accept either parity.
- Required inequalities are satisfiable whenever not forced by the equality
  closure (enough freedom for K ≥ 2 or 3 — prove a concrete bound; then
  achievable-at-some-K = achievable-at-K₀ for a fixed small K₀, making the
  whole set enumerable by native_decide).
- Refinement lifting (K | mK preserves Compat exactly) gives monotonicity:
  achievable(K) ⊆ achievable(mK); with the K₀ bound the union stabilizes.

Deliverable: `achievable : Rel → Prop` with a decidable characterization +
`enumAchievable : List Rel` + completeness (`∀ K d, Compat_d ∈
enumAchievable`). Expected size: thousands (parameterized by face-equation
patterns, not the 2^72 raw equivariant relations). If it explodes, the SAT
layer still scales (instances tiny) but the data layer gets bulky.

## 3. Per-relation certificates (tiny SAT)

For each R ∈ enumAchievable, one of:
- **periodic:** an explicit torus tiling of the 24-letter SFT (index
  empirically ≤ ~32) — reuse `cert_admitsPeriodic` shape, alphabet 24.
- **empty:** box UNSAT (n³ cells × 24 one-hots; 6³ ≈ 5k vars, ~100k clauses,
  *no* decoration vars / e-vars / balance) — certificates small enough for
  the **in-Lean verified checker** (`Std.Sat verifyCert` + native_decide,
  validated 2026-06-18 to 400k proof steps). Plausibly NO external cake_lpr
  axiom needed: trust base = kernel + native_decide only, *stronger* than
  the K=3 result's.

Fail-forward property: an R that stalls (box-SAT at every tried size, no
torus found) is either a hard instance or an einstein-bearing relation — and
achievability then *constructs* the candidate decoration. The pipeline
cannot silently lose: it terminates in the theorem or in a tile.

(Undecidability note: 3D SFT emptiness is undecidable in general, so
termination has no a priori guarantee — only the strong empirical pattern:
3D K≤3 and 2D K≤5 all close at element-order indices.)

## 4. Assembly

    ∀ K, ∀ dec, TilesZ3 dec →
      Compat dec ∈ enumAchievable        (2, completeness)
      → SFT (Compat dec) nonempty        (1, forward)
      → periodic config exists           (3, that R's certificate)
      → periodic tiling of dec           (1, backward)

Same shape as `no_einstein_concrete`, quantified over relations instead of
decorations. Symmetry reduction (`sym_reduction`) applies in relation space
(enumerate R up to the 24-rotation action, transport certs by conjugation —
the existing RotSym machinery).

## 5. Dress rehearsal: do it in 2D first

Same reduction with C4 and 4-letter SFTs; relations live on {x,y} × 4 × 4 =
32 triples; achievability over 4 edge-functions [K] → {±1} with twist group
Z2 × Z2. Everything is small enough to:
- check the achievability characterization against brute force,
- validate the per-relation pipeline end-to-end,
- cross-check the final theorem against arena2d's exhaustive per-K sweeps
  (K ≤ 5 closed 2026-07-16, all periods with index ∈ {1,2,4} = element
  orders of C4 — the kill structure the reduction predicts).

Then lift to 3D with the same file structure.

## 6. Risk register

| risk | exposure | mitigation |
|---|---|---|
| τ/twist bookkeeping error in face equations | wrong achievable set (soundness of step 2 completeness) | coordinates-as-ground-truth; brute-force cross-check at K=2,3 vs arena2's actual Compat tables |
| stabilizer cases messy (R2) | more Lean case work | try free-orbit refinement lemma first |
| enumAchievable explodes | data-layer bulk | still fine for SAT; batch native_decide; symmetry-reduce first |
| some R stalls | can't finish assembly | it's the research frontier then — that R is the object to study; possibly the einstein |
| achievability bound K₀ wrong | completeness gap | prove the bound, don't assume; parity handled explicitly |
