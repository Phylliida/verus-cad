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

## 3D hard direction — analysis so far (mechanism candidate)

Worked example: the T=2 chiral pair #10/#11 (the two empty decorations):
4 marks forming a 3-edge path between antipodal corners; equivalently an
edge of the even tetrahedron + an edge of the odd tetrahedron in a
fixed (right- or left-handed) screw arrangement.

For such decorations the constraint reduces exactly to a **face-dimer
problem**: mark a lattice face E (resp. O) if its even-parity (odd)
diagonal corners are marked. Consistency forces:
- each cube has exactly one E-face and one O-face, and they are adjacent
  (opposite-face choices give parallel diagonals = degenerate screw);
- E/O-marking is consistent across the two cubes sharing a face;
- the screw handedness of the (E-diagonal, O-diagonal) pair at each cube
  must equal the decoration's chirality.
E-faces form an exact cover (each cube incident to exactly one E-face);
likewise O. Explicit covers (e.g., E = x-normal faces at even x,
O = y-normal faces at even y) yield handedness alternating with cube
parity — never constant. **Conjectured mechanism:** for any E/O exact
covers, the screw handedness cannot be constant over ℤ³ (a
dimer/height-function type invariant forces both signs), so chiral
decorations admit no tiling. General T/chiral decorations need the
general form of this argument — the current analysis is specific to
the 4-mark path decorations.

Small-scale data point: chiral #10/#11 are UNSAT on every torus up to
(3,3,3) (all 27 shapes probed) and box-UNSAT at 4³; box 3³ is SAT, so
the obstruction needs at least one full period of room.

## Lean formalization plan (lean-flocq, house style)

Ordered by risk/reward:

1. **2D theorem, end-to-end** (days; self-contained; validates the whole
   approach). New module family `Corner2D*`: vertex colorings, square
   patterns, `IsTiling`, mirror/rotation group C4/D4 (fin 4 tuples),
   the necklace lemma by `decide`-scale finite case analysis (length-4
   sequences over an arbitrary finite palette — state via `Fin 4 → α`
   with the reversal-closure hypothesis; the case analysis is
   case-splitting on equality patterns), the pair-reversal argument
   (infinite part: from IsTiling to reversal-closure — clean, no
   compactness needed since every pair occurs in every square), and the
   period-2 construction. No external evidence needed — fully
   kernel-checkable. Target: `corner2d_tileable_iff_achiral`.
2. **3D easy half** (`corner3d_achiral_periodic`): achiral ⟺ period-2
   witness ⟹ tileable. The rotation/mirror action on corners as
   `Fin 8` permutations (export the 24×8 table + reflection), the
   τ_c/parity argument, the explicit witness ℓ(v) = d(v mod 2), and the
   K=1 census cross-check (333 canonicals, achiral count 201 by
   native_decide — matches the Python census).
3. **3D hard half** (`corner3d_tileable_achiral`): blocked on the math
   (mechanism above). If the dimer-cover argument generalizes, its
   formalization is a finite-per-cube case analysis + a global invariant
   — the global part is the risk.
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
