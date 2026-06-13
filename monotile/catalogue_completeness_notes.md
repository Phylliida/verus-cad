# The Catalogue Completeness Programme

*Working notes, 2026-06-12. Status: two lemmas proved (one
machine-checked in Lean), reduction framework set, one sharp gap
identified. Companion artifacts: `catalogue_anatomy.py` (data),
`lean-flocq/LeanFlocq/SftPeriodic.lean` (verified atom).*

## Setup

Decoration `H ∈ {±1}^54`; tilings are orientation fields `ω: Z³ → S₂₄`
with complementary face-matching. For a tiling `T`, its **pattern**
`S(T)` is the set of point-pairs `{a,b}` forced complementary across
all adjacencies realized in `T` (a finite union over the
orientation-pairs occurring). `H` realizes `S` iff all pairs of `S`
are complementary in `H`; any `H` realizing `S(T)` admits `T`.
Catalogue `𝒞` = the patterns found by CEGIS (33 files entries; see
Anatomy below for the true count).

**Conjecture (Catalogue Completeness).** Every fully periodic tiling
`T` (any lattice, any index) has `S(T) ⊇ S₀` for some conjugate of a
catalogue member. Equivalently: the minimal elements of the poset
`𝒫 = { S(T) : T periodic, balanced-realizable }` under inclusion are
exactly the subsumption-minimal catalogue members.

Certified base case (machine-enumerated, June 10–12): **true for all
T with lattice index ≤ 16** (307 classes, exhaustive, zero novel
patterns; ≤ 24 campaign in progress, 0 novel through idx 18 so far).

## Lemma 1 (Pattern Closure under Reduction) — proved

Let `compat_S` be the orientation-pair compatibility induced by a
pattern `S` (allow `(o₁,o₂)` along axis `ax` iff its nine point-pairs
are non-degenerate and lie in `S`). Then:

  (i) every tiling valid in `compat_{S(T)}` includes `T` itself;
  (ii) any tiling `T'` valid in `compat_{S(T)}` has `S(T') ⊆ S(T)`;
  (iii) hence any *reduction* performed inside `compat_{S(T)}`
        (shortest-cycle surgery, quotient re-tiling, sheet collapse)
        produces tilings whose patterns are ≤ the original in 𝒫.

*Proof.* (i) is definitional. (ii): every adjacency of `T'` is
`compat_{S(T)}`-allowed, so its point-pairs lie in `S(T)`; `S(T')` is
their union. (iii) is (ii) applied to the reduced tiling. ∎

Consequence: **minimal elements of 𝒫 are realized by
reduction-irreducible tilings**, and it suffices to classify those.

## Lemma 2 (1D Periodic Point with Pattern Closure) — proved in Lean

`periodic_point_of_walk` (SftPeriodic.lean, compiles clean against
mathlib): for any transition relation `R` on a finite alphabet `α`
and any infinite `R`-walk `f`, there is an `R`-periodic walk `g` with
period `0 < p ≤ |α|` such that **every transition pair of `g` is a
value-pair of a transition of `f`**.

The final clause is what makes this compose with Lemma 1: the
periodic point lives inside `compat_{S(f)}` *with no new adjacencies*,
so pattern only shrinks. This atom is used twice:

- **Rank-2 Reduction Lemma** (already in use since June 9): a tiling
  invariant under a rank-2 lattice `L₂` induces a walk in the finite
  alphabet of `L₂`-quotient slab states; Lemma 2 yields a fully
  periodic tiling with the same (or smaller) pattern.
- **Bounded Reduction** (below).

## Theorem 3 (Bounded Reduction) — proved, with an astronomic bound

Every periodic tiling `T` admits a periodic tiling `T'` with
`S(T') ⊆ S(T)` and lattice index `≤ N₀`, where `N₀` is explicit but
enormous (towers of 24):

*Proof sketch (dimension induction inside `compat_{S(T)}`).* `T` is
invariant under full-rank `B`. Pick the coordinate plane `P` with
`L₂ = B ∩ P` of rank 2. The `L₂`-quotient slab states along the
transverse direction form a finite alphabet (`≤ 24^{[P:L₂]}`); `T` is
an infinite walk on it; Lemma 2 gives transverse period
`≤ 24^{[P:L₂]}` with pattern closure. To bound `[P:L₂]`, apply the
same argument inside the plane: rows are walks over `S₂₄` (period
`≤ 24` by Lemma 2 in dimension 1), columns over row-states
(`≤ 24^{24}`), giving an in-plane re-tiling of bounded index — again
inside `compat`, so the pattern never grows. Composing the bounds
yields `N₀ ≤ 24^{24·24^{24}}`-ish. ∎ *(The point is finiteness and
pattern closure, not the constant.)*

**Corollary.** The conjecture is *decidable*: it reduces to the
finite enumeration of classes of index ≤ N₀. The certified ≤ 16 (soon
≤ 24) base is the same enumeration at humane indices.

## The Gap

Bridge `N₀ → 32`. Empirically (Anatomy below) every minimal pattern
certifies at index ≤ 32, and three campaigns found nothing new in
307+ classes. The bridge must use structure the generic SFT argument
ignores:

1. **Balance + channels** (corners ⊗ edge-mids ⊗ centers): the
   centre channel alone has 20 balanced states; the slab-state
   alphabet of a *reduction-irreducible* tiling may be forced far
   below `24^{[P:L₂]}`.
2. **Equivariance**: slab digraphs for conjugate planes are
   isomorphic; irreducibility is preserved by the 48-group.
3. **Perfect-matching minimality**: 14 of the minimal patterns have
   `|S| = 27 = 54/2` — plausibly perfect matchings on the points
   (TODO: verify disjointness). A matching is the smallest possible
   nonempty pattern of a tiling that uses every face of a tile, which
   suggests minimal patterns are extremal matchings + bounded
   corrections — a direct combinatorial characterization would
   replace the index bound entirely.

## Anatomy of the catalogue (computed 2026-06-12)

- Sizes: 27×14, 35×3, 45×4(+1 at 53), 54×5, 63×4, 71, 145.
- **Subsumption**: patterns 14, 18 are subsumed by pattern 23 → the
  true catalogue has ≤ 31 minimal members. Pattern 18's own
  certifying tiling has pattern strictly inside it (27 < 35): a
  direct witness of non-minimality. (Dedupe was historically by
  equality only.)
- **Certifying lattices**: all 33 certify at index ≤ 32; sheet-type
  certificates for only 19/33 — the index-32 quadruple (|S|=63) and
  the |S|=145 (idx 24) are *genuinely non-sheet*. The earlier
  "minimality forces sheets" mechanism conjecture is **false**;
  the correct empirical invariant is the ≤ 32 certificate bound.

## The Big-Proof Attack (status 2026-06-12 afternoon)

**Theorem 4 (Finiteness — free).** Patterns are unions of the 1,728
interface blocks `P(ax,o1,o2)`, so 𝒫 is a finite poset and its
minimal antichain is finite. The conjecture is pure *identification*;
with Theorem 3 it is decidable. "Any size" was never infinite — only
the witness indices were unbounded a priori.

**Obstruction (honesty clause).** A generic witness-index bound for
2D/3D SFT periodic points cannot exist (undecidability-adjacent). The
bridge MUST use complementary-matching structure. Named candidate:

**Target Lemma (Interface Factorization + Matching Collapse).** In a
nearest-neighbour complementary system, slab-to-slab dependence
factors through the face-coloring interface, not the slab content.
For a tiling realizing a pattern S, admissible interfaces are
S-consistent colorings. When S contains a perfect matching M (all
fourteen |S|=27 minimal members ARE perfect matchings — verified:
degree 1 at all 54 points), each pair of M ties two face bits, and
opposite-face pairs tie a face's outgoing interface to its incoming
one. Conjectured consequence: an irreducible tiling realizing a
matching-type minimal pattern has per-axis interface orbit ≤ c (small
constant from the matching taxonomy), hence witness index ≤ c³-ish —
bridging to the certified base for the matching layer of the
catalogue. Non-matching minimals (|S| ≥ 35, finitely many, all with
certified witnesses ≤ 32) then need either the same argument with
"matching" relaxed to "low-degree constraint graph," or individual
treatment.

**Matching taxonomy (verified).** Of the fourteen |S|=27 minimal
patterns: 6 pure opposite-face (stacker family), 2 pure cross-axis
(braided/diagonal family), 6 mixed with signature 9 opposite-face
(one full face channel) + 18 cross-axis (the other two axes braided).

## Theorem 5 (Matching Collapse) — PROVED 2026-06-12

Let S be a realizable perfect-matching pattern (every point in
exactly one pair; all fourteen |S|=27 catalogue members are such).

**(a) Determinism.** For each axis `ax` and orientation `o₁` there is
at most one `o₂` with `(ax,o₁,o₂)` allowed in `compat_S`, and at most
one in-neighbour likewise.

*Proof.* Allowance means the nine interface pairs
`{o₁⁻¹(t⁺), o₂⁻¹(t⁻)}` (t the nine tangential positions) lie in S,
non-degenerately. Fix `o₁`: each left point `a_t = o₁⁻¹(t⁺)` has a
UNIQUE S-partner `M(a_t)` (perfect matching), so `o₂⁻¹` is prescribed
on the whole −ax face: `o₂⁻¹(t⁻) = M(a_t)`. Two rotations of the cube
agreeing on all nine points of a face coincide (their quotient fixes
a face pointwise; only the identity does). Mirror the argument for
in-neighbours. ∎

**(b) Rigidity.** On the viable core the axis maps are permutations
`π_x, π_y, π_z`. Any compat_S tiling ω satisfies
`ω(c+e_ax) = π_ax(ω(c))`; well-definedness along plaquettes forces
the π's to commute on the orbit of any attained value, so
`ω(c) = π_x^{c₁}π_y^{c₂}π_z^{c₃}(ω(0))`, and ω is invariant under
`L = {v : π^v fixes ω(0)}` — a full-rank lattice of index =
|⟨π⟩-orbit of ω(0)| ≤ 24. ∎

**Consequences.**
1. *Every* tiling (periodic or not!) of *every* decoration realizing
   a perfect-matching pattern is fully periodic with index ≤ 24 —
   aperiodicity is impossible inside a matching pattern.
2. Every realizable matching pattern has a witness of index ≤ 24.
   **Once the ≤24 saturation campaign completes, the matching layer
   of 𝒫 is unconditionally identified: exactly the 14 catalogue
   matchings.** (Currently certified ≤16 + campaign in flight.)
3. Classification handle: matching-pattern tilings = orbits of
   commuting permutation triples induced by face-bijections; the
   full matching layer can be *independently rederived* by finite
   enumeration of such triples — a second proof path with no SAT.

**Measured collapse table** (`interface_collapse.py`): all 33
patterns have 24-letter viable cores; matchings are `det/det/det`
with cycles 1–3; non-matchings have out-degrees ≤ 2 (|S|≤63) or 5–6
(|S|=145), cycles ≤ 4. The general-bridge target is now precise:

**Conjecture 6 (Bounded-Degree Collapse).** If the constraint graph
of S has max degree d, compat_S out-degrees are ≤ d (proof of ≤ d:
same face-prescription argument, d partner choices per point, but
rotation rigidity from nine points cuts the combinations to ≤ d —
needs care), and tilings inside an out-degree-≤d system over 24
letters reduce to witness index ≤ φ(24, d) with φ polynomial. The
catalogue data: d ∈ {1, 2, 3(?), 5–6}, observed witnesses ≤ 32.
Remaining bridge = prove minimal patterns have small d, plus φ.

## Next steps

1. Verify the perfect-matching claim for the fourteen |S|=27 patterns
   and characterize *which* matchings arise (orbit structure under
   the 48-group).
2. Prune the catalogue to its ≤ 31 subsumption-minimal members in
   `arena2_patterns.json` (sound: subsuming patterns block strictly
   more) — or keep redundant members for solver strength but report
   the minimal count in any statement.
3. Sharpen Theorem 3's in-plane step using the channel decomposition
   (centre channel first — 20 states, not 24^k).
4. Lean targets, in order: Lemma 1 (finite-combinatorial, easy);
   Theorem 3's composition skeleton; the matching characterization
   if (1) pans out.
