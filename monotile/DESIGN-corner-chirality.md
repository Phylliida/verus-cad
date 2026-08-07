# DESIGN: the corner chirality theorem (Phase B, 2026-08-07)

Discovered during Phase 0 follow-up analysis. This is the candidate
Phase-B theorem, in the sharpest form the data supports.

## The conjecture

**Corner model (K=1, any palette T).** A decoration is a coloring
d: {0,1}³ → [T] of the cube's 8 corners. A tiling is a vertex coloring
ℓ: ℤ³ → [T] such that every unit cube's 8-corner pattern
χ_c(p) := ℓ(c+p) lies in the rotation orbit O(d) (24 rotations, no
reflections). (This vertex-coloring form is *equivalent* to the
orientation-field form: each corner of each cube sits at exactly one
lattice vertex, so "all 8 incident corners equal at every vertex" ⟺
"ℓ well-defined and every cube pattern ∈ O(d)".)

**Conjecture C.**  TFAE:
1. d tiles ℤ³;
2. d is **achiral**: its mirror image (any axis reflection of the corner
   cube) lies in O(d);
3. d admits a period-(2,2,2) tiling.

**Status: (2) ⟺ (3) proven (below); (3) ⟹ (1) trivial; (1) ⟹ (2) is
the open hard direction.** Empirically exact wherever checked:

- 3D T=2: 23 canonicals, 21 achiral = exactly the 21 periodic (0 mism).
- 3D T=3: 333 canonicals, 201 achiral = exactly the 201 periodic (0 mism).
  (Cross-check by Burnside: #rotation-orbits = A + 2C, #O_h-orbits =
  A + C; at T=3: 333 = 201 + 2·66 ✓, empties = 132 = 2·66 = exactly
  the chiral pairs.)
- 2D analog (vertex-marked Wang squares, C4): T=2 (6), T=3 (24),
  T=4 (70): achiral ⟺ periodic ⟺ period-(2,2), **zero mismatches**,
  and the 2D theorem is fully proved (below).

Verification scripts: `corner3d_chiral.py` (3D cross-check),
`corner2d.py` (2D probe with achirality recorded per verdict).

## Proof of (2) ⟺ (3)

Let r be the corner reflection x ↦ 1−x and τ_c (c ∈ {0,1}³) the corner
relabeling p ↦ p⊕c induced by translating a cube by c. τ_c is a proper
rotation of the cube iff |c| is even (τ with two flips = 180° rotation);
the odd-weight τ_c are improper.

(2) ⟹ (3): if O(d) is closed under one axis reflection, it is closed
under all 48 octahedral symmetries (conjugate by rotations: the orbit is
rotation-invariant, so closure under r_x gives r_y = ρ r_x ρ⁻¹ etc.).
Then ℓ(v) := d(v mod 2) is a valid tiling: cube c shows
d∘τ_{c mod 2} ∈ O(d). ∎

(3) ⟹ (2): a period-(2,2,2) tiling ℓ has ℓ(v) = χ(v mod 2) for some
χ ∈ O(d); the cube at c = (1,0,0) shows χ∘τ_{100} = χ∘r_x =
mirror(χ), which must lie in O(d) since ℓ is valid. So χ (hence d) is
achiral. ∎

Both directions are finite group theory + one explicit construction —
very Lean-friendly.

## The 2D theorem (complete proof — the template)

Model: d: {0,1}² → [T]; tiling ℓ: ℤ² → [T], every unit square's pattern
(read clockwise 00,10,11,01) in the C4-orbit O(d).

**Theorem.** tileable ⟺ achiral ⟺ period-(2,2) witness.

Proof of the hard direction (tileable ⟹ achiral):
1. Every square of the tiling realizes the directed adjacent-pair
   multiset P(d) on its four edges (clockwise).
2. Each lattice edge is read in *opposite* directions by its two
   incident squares (both read clockwise around themselves). Hence for
   every directed pair (u,v) realized on any edge, the reverse (v,u)
   also lies in supp P(d).
3. Every pair in supp P(d) is realized on some edge (each square
   realizes P(d) on its edges). Hence supp P(d) is reversal-closed.
4. **Length-4 necklace lemma:** a length-4 cyclic sequence whose
   directed adjacent-pair support is reversal-closed is achiral (mirror
   = rotation). Finite case analysis (the pair multigraph must be a
   single Eulerian 4-circuit; the cases force a palindromic rotation).
5. Therefore d is achiral. ∎

The converse is the same construction as 3D: achiral ⟹ ℓ(v) = d(v mod 2)
valid ⟹ tileable.

**Why the argument does not directly port to 3D:** in 2D the two squares
incident to an edge read it in opposite cyclic directions. In 3D the 4
cubes around a lattice edge all read it in the *same* canonical (+axis)
direction, and the 2 cubes sharing a face read the face in the *same*
(ε₂,ε₃) frame — the reversal has nowhere to enter. (Face *necklaces*
with boundary orientation do read oppositely, giving: supp of the
face-necklace family is reversal-closed — but for T=2 every 4-cycle is
achiral, so this yields nothing, while chiral T=2 decorations are empty.
The 3D obstruction lives deeper than faces.)

## 3D hard direction — the mechanism, caught in the act (2026-08-07)

Worked example: the T=2 chiral pair #10/#11 (the two empty decorations):
4 marks = an edge of the even tetrahedron + an edge of the odd
tetrahedron. Verified facts (`corner3d_dimer.py`):

- A #10-type pattern is **determined by its (E-face, O-face) ordered
  pair** (the even marks are the even diagonal of the E-face, the odd
  marks the odd diagonal of the O-face), and the rotation orbit covers
  exactly **12 of the 24 adjacent ordered face pairs**, one decoration
  per pair. The class invariant is purely the **cyclic orientation of
  the axis pair**: (x,y), (y,z), (z,x) = #10's class; (y,x), (z,y),
  (x,z) = #11's. (An earlier "screw handedness" attempt with
  lexicographically-directed diagonals was NOT rotation-invariant —
  wrong concept, superseded by the axis-cyclic class.)
- **The parity flip — the actual obstruction.** The decoration's local
  E-part sits on local-even corner positions. For an even cube these
  land on absolute-even vertices, but for an odd cube the local-even
  positions land on absolute-ODD vertices: the local class constraint
  becomes, in absolute terms, "(even-mark-face axis, odd-mark-face
  axis) positive" at even cubes but NEGATIVE at odd cubes. Explicit
  witness of the failure mode: X = {x = even} faces, Y = {y = even}
  faces satisfies every vertex-glue constraint and puts every even cube
  in the #10 class — but every odd cube in the #11 class. A chiral
  tiling would need the axis-class to alternate with cube parity.
- **Rigidity is FALSE**: "2-per-tetrahedron" vertex subsets of the FCC
  lattice are abundant (3000+ solutions on the (4,4,4) torus, mostly
  non-layered) — the even side alone has huge freedom; the obstruction
  needs the coupling.

**Reduced model (exact for #10/#11).** Per cube c: an E-face and an
O-face, adjacent, with axis class positive iff c even (for #10). Global
consistency: face-marking is shared across adjacent cubes (follows from
vertex glue), and at every vertex the faces through it sum to 0 or 4
(all 8 incident cubes mark it or none). Axis-level propagation along
dimers is deterministic: following the alternating E/O-dimer path from
an even cube cycles (x,y)→(x,z)→(y,z)→(y,x)→(z,x)→(z,y)→(x,y) with
period 6 — consistent, so the final contradiction must come from the
vertex glue and/or the side (±) choices.

**SOLVED for #10/#11 (2026-08-07): the one-edge obstruction.** The
reduced model is now encoded exactly (`corner3d_dimer.py` part 3: 12
ordered (A-face, B-face) pairs per cube, class ±1 by cube parity,
vertex glue as all-equal chains) — it reproduces #10's full verdict
profile against the orientation encoding (box 3³ SAT, 4×4×3 UNSAT,
small tori UNSAT, every shape MATCH). Transfer-graph analysis on
cylinders (`corner3d_transfer.py`) localizes the contradiction, and an
assumption-based UNSAT core + greedy deletion
(`corner3d_core_hunt.py`) shrinks it to **four cubes: the ones around
a single lattice edge**. Precisely: the 4 cubes around any lattice
edge, with mark agreement at every vertex shared by ≥ 2 of them (the
4-wise central vertex at each end of the edge, plus 4 pairwise
edge vertices per end plane), admit NO assignment of their 12 allowed
face pairs — brute-force verified over all 12⁴ = 20736 assignments for
both layer parities (`corner3d_edge.py`, zero survivors; solver-free).
Any #10 tiling of ℤ³ would restrict to such a 4-cube system around
every lattice edge (vertex glue implies the agreements), so #10 and
#11 cannot tile ℤ³. ∎ (modulo the reduction, which is exact and
cross-checked). The obstruction is distributed: no single agreement is
individually essential; dropping the central 4-wise agreement leaves
84 near-misses, which can make the central marks constant on either
end plane separately (24+24) but never both at once — the two ends of
the edge cannot simultaneously close. Remaining work: a human/Lean
proof of the 4-cube UNSAT (12⁴ case analysis, very `decide`-friendly),
and the formal reduction (pattern → (A,B) pair + class by parity —
the stabilizer/orbit group theory).

**Why this should generalize to all chiral d:** chirality ⟹ Stab(d) ⊆ A4
(an odd-diagonal-permutation symmetry makes d achiral), so every cube in
a tiling has a well-defined tet-parity bit ε_c (which diagonal coset
its orientation lies in), and the same absolute-parity flip applies to
the ε-propagation: the local chirality class becomes an alternating
absolute constraint. The case work is in how the decoration's E/O
patterns interact with the glue; the #10 class is the cleanest instance.
General chiral decorations (T≥3, e.g. tet parts with 3–4 distinct
colors) need the same treatment per "chirality type" — or a uniform
invariant subsuming them.

Small-scale data point: chiral #10/#11 are UNSAT on every torus up to
(3,3,3) (all 27 shapes probed) and box-UNSAT at 4³; box 3³ is SAT, so
the obstruction needs at least one full period of room.

## Lean formalization plan (lean-flocq, house style)

Ordered by risk/reward:

1. **2D theorem, end-to-end** ✅ **DONE (2026-08-07)** —
   `lean-flocq/LeanFlocq/Corner2D.lean`, ~260 lines, single module:
   `corner2d_tileable_iff_achiral` and
   `corner2d_tileable_iff_period2` (tileable ⟺ achiral ⟺ period-(2,2)
   witness), for decorations `Fin 4 → α` over an arbitrary `DecidableEq`
   palette. The necklace lemma reduces via `normPat` (first-occurrence
   equality patterns) to `necklaceFin`, a kernel `decide` over all 256
   `Fin 4 → Fin 4` patterns. Trust base: **propext, Classical.choice,
   Quot.sound only** (verified by `#print axioms`) — no native_decide,
   no external evidence, strictly cleaner than the face tracks.
2. **3D easy half** (`corner3d_achiral_periodic`): ✅ **DONE
   (2026-08-07)** — `lean-flocq/LeanFlocq/Corner3D.lean` (commit
   a4c14ed): achiral ⟺ period-(2,2,2) witness ⟹ tileable, for
   decorations `Fin 8 → α` over an arbitrary type. Rotation/mirror as
   exported `Fin 8` permutation tables + composition table (kernel
   `decide`); witness ℓ(v) = d(v mod 2); the τ_c parity argument via
   `xorTab_cases`; kernel checks that #10/#11 are chiral mirror
   partners; census cross-check (23/21, 333/201) by `native_decide`
   (outside the trust base). Trust base: propext, Classical.choice,
   Quot.sound only.
3. **3D hard half** (`corner3d_tileable_achiral`): the math for #10/#11
   is now DONE modulo formalization (the one-edge obstruction, above).
   Lean path: (a) formalize the 4-cube edge system over `Fin` types and
   prove its UNSAT by `decide` (12⁴ assignments — cheap); (b) the
   reduction lemma: any tiling restricts to the edge system (needs the
   orbit/stabilizer group theory: a cube's pattern determines its
   (A,B) pair with class sign by cube parity); (c) generalize from
   #10/#11 to all chiral d (per chirality type, or a uniform
   invariant).
4. **Any-K corner theorem** (the plan's original Phase B statement):
   revisit after K=1. The K×K×K-octant model with C3 twists has the
   gain structure; whether "tileable ⟹ achiral-through-twists" holds is
   untested even empirically. A K=2 probe is cheap with the existing
   encoder pattern (corners carry 2×2×2 patterns; twist = C3 per vertex)
   — worth doing before attempting the general proof.

## What this buys the einstein hunt

If the full theorem (any K) holds: **corners alone can never give an
aperiodic monotile** — closing the pure-corner search space in one
stroke, exactly the plan's "elegant outcome". The einstein search then
concentrates on faces+corners (mixed, where chiral-but-tileable
decorations already exist at K=1 — 100 of the 776) and faces+edges, the
only models with demonstrated nontrivial forcing (period 3/6/8).
The 2D theorem is a genuine standalone result regardless: a complete
characterization of vertex-transitive corner SFTs on ℤ².
