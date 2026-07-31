# The density lemma and the fall of canon 755 (2026-07-28)

## The lemma

Let a decoration's face types (the 6 base faces) carry an allowed-adjacency
relation induced by the rulebook. Call a face type **deficient** if its
only allowed partners belong to a proper subset of the other types.

**Lemma (density obstruction).** Suppose face types partition into
`A` (each type in `A` pairs only with types in `B`) and `B`, with
`|A| > |B|`. Then no box of side `L > 6 / (|A| - |B|)` is tileable,
and hence the decoration cannot tile space at all.

*Proof.* Every placed cube presents exactly one face of each type.
Type-`A` incidences each require a type-`B` partner; type-`B` incidences
serve at most one adjacency each. In a box of side `L` there are
`|A| L³` partner-needing incidences and only `|B| L³` partners, so at
least `(|A| - |B|) L³` type-`A` faces must go unmatched, and unmatched
faces can only sit on the boundary, which has `6 L²` outward slots.
Tileable requires `(|A| - |B|) L³ ≤ 6 L²`, i.e. `(|A| - |B|) L ≤ 6`,
i.e. `L ≤ 6 / (|A| - |B|)`. ∎

> **Erratum / sharpening (2026-07-31).** This note originally stated the
> bound as `L ≤ 6|B| / (|A| - |B|)` — a slip in the final division:
> `(|A| - |B|) L³ ≤ 6 L²` gives `L ≤ 6 / (|A| - |B|)`, with no `|B|`
> factor. The two agree at `|B| = 1` (canon 755), so every conclusion
> drawn here stands; the sharper bound only kills more boxes. The sharp
> form is now machine-proved: `density_obstruction` in
> `lean-flocq/LeanFlocq/ColorDensity.lean`, with the canon-755 instance
> in `lean-flocq/LeanFlocq/AnyK3DColorDensity.lean`
> (`color755_empty`: the relation's orientation SFT on ℤ³ is empty,
> Lean-checked, no SAT certificate involved).

## Canon 755

Its relation (computed directly, all three axes):

    blanks {0,1,2} pair freely among themselves
    face 3 pairs ONLY with face 4
    face 4 pairs ONLY with faces 3 and 5 (never itself)
    face 5 pairs ONLY with face 4

So `A = {3, 5}`, `B = {4}`: deficit 1, bound `L ≤ 6/1 = 6`.

**canon 755 cannot tile any box of side ≥ 7, hence cannot tile space —
empty, by pure counting.** No solver required. (The 7³ cube-and-conquer
still runs for the certificate; the verdict no longer depends on it.)

The borderline is exact: `L = 6` needs 216 unmatched type-3/5 faces on
the boundary — exactly the 216 outward slots a 6³ box has. So every
outward face would have to be type 3 or 5 and every type-4 matched
internally: an extraordinarily rigid patch, if it exists at all.

## Why the solver fought so long

The obstruction is *density*, not local geometry: boxes up to 6³ sit on
the feasible side of the boundary inequality (with L=6 the equality
edge), so no small window shows it, and the 7³ box is exactly where the
deficit turns positive. Every verdict in the campaign rhymes:

| stage | verdict | interpretation |
|---|---|---|
| boxes 3³–6³ | SAT / budget-out | boundary can absorb the deficit |
| tori ≤ 256 | none | no periodic escape either |
| 7³ C&C | thousands of UNSAT leaves, no SAT | the deficit turning positive |

## Scope

The density lemma fires on any rulebook with a deficient face-type
class. It is the equal-color analogue of the binary "balance lemma"
(per-axis bump/dent counting), which pruned the binary search; for
colors the count is per face *type*, not per cell color. Both say:
local complement/balance must match globally — arithmetic first, search
second.

*Credit: the structural observation (faces 3 and 5 as peg-out types
needing the single peg-in type 4) is Danielle's; the counting argument
above is its formalization.*
