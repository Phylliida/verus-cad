# The Screw Structure Behind the K=3 Result

A companion to `RESULT.md`. The theorem `no_aperiodic_wang_cube` is machine-checked
but opaque: it says a 785,686-clause CNF is unsatisfiable. This note decodes *what*
the proof is actually about — the 33 forbidden patterns it rests on turn out to have
a single, human-legible structure, and that structure explains *why* no aperiodic
K=3 Wang cube can exist.

## What a forbidden pattern is

The search (`arena2.py`) closed the space by discovering **33 patterns** such that no
decoration can tile even a 4³ box while avoiding all of them. Each pattern is a small
**periodic tiling of a torus** — a witness that any decoration realizing it admits a
fully periodic tiling of ℤ³ (that's exactly what `l2_bridge` proves in Lean). Each
torus cell carries one of the cube's 24 rotational orientations.

## The finding: every pattern is a screw

Extracting the orientation of each cell and the transition between neighbouring cells,
**every one of the 33 patterns is a screw-periodic tiling**: the cube translates freely
in two directions and *rotates as it translates* in the third (a screw motion), or a
2-D combination of two such screws. The rotation cycle length is exactly the period.

Concretely, e.g. pattern 0 stacks orientations `12 → 22 → 15 → 21 → (12)` along z — a
90°-per-step screw of order 4 — while x and y are pure translation.

### Classification of all 33

| screw type | axis-aligned | skew axis | total |
|---|---:|---:|---:|
| pure translation (order 1) | 1 | 0 | 1 |
| 1-D screw, order 2 (180°/step) | 1 | 2 | 3 |
| 1-D screw, order 3 (120°/step) | 0 | 2 | 2 |
| 1-D screw, order 4 (90°/step) | 2 | 3 | 5 |
| 2-D screw, orders (2,2) | 3 | 4 | 7 |
| 2-D screw, orders (4,2) | 0 | 7 | 7 |
| 1-D screw, order 6 (skew) | 0 | 3 | 3 |
| 2-D screw, orders (5,4) (skew) | 0 | 3 | 3 |
| 2-D screw, orders (6,4) (skew) | 0 | 2 | 2 |
| | **7** | **26** | **33** |

The **7 axis-aligned** patterns are pure screws about a coordinate axis, and their
orders are exactly **{1, 2, 3, 4} — the element orders of the cube's rotation group**.
The **26 skew** patterns are the same idea about a *tilted* axis; on the rectangular
hull that shows up as a longer cycle (orders up to 6) or a 2-D product. (The skew hulls
are also why the formalized periods reach 12×6×12 = 864 cells — the `spacetiler_periodic_le864`
bound — where the intrinsic skew tori are as small as 32.)

Patterns that share an orientation set (e.g. three of the period-4 ones all use
`{0,1,4,5}`) are the *same screw motif viewed along different axes* — distinct
rotation-orbits, one geometric object.

## The moral: you cannot build an irrational screw out of a finite group

A cube tiles 3-space by screw motions. But its orientations form a **finite** group —
the 24 rotations — so any screw the tiling runs **must close**: after 1, 2, 3, or 4
steps (or a skew multiple) the accumulated rotation returns to the identity, and a
closed screw is exactly a **translation period**. There is no screw that never repeats.

This is precisely the obstruction that separates this family from a genuine 3-D
einstein. The **Schmitt–Conway–Danzer** tile achieves aperiodicity through a screw by an
**irrational** angle — it never closes, so its tilings are translation-free forever. A
symbolic K=3 cube can only screw by the rational angles a finite rotation group permits,
and those always close up into periods.

So the one-sentence reading of the whole machine proof is:

> A K=3 Wang cube can only tile by screws, its screws all close because 24 rotations is
> a finite group, and a closed screw is a period — so every space-tiler is periodic.

The 33 patterns are just the complete enumeration of the closed screws the K=3 matching
rules allow; forbidding all of them says "no decoration can even locally begin an
unclosable screw," and screwing is the only route to would-be aperiodicity.

## Honest framing

This is a *reading* of the machine proof, not a second proof. The decode makes the
**"what" and "why"** legible — the forbidden patterns are screws, and finiteness closes
them — but the rigor still lives in the two machine-checked halves:

- **`l2_bridge`** (kernel-checked): realizing any of these screw motifs forces a periodic
  tiling. This is the "a closed screw is a period" half, and it *is* proved.
- **the SAT proof** (cake_lpr-checked): **every** box-tiling, pattern-avoiding decoration
  is impossible — i.e. every space-tiler realizes one of the screws. This "every tiler
  contains a screw" completeness is the hard half the solver establishes.

The pleasant consequence is a candidate for a fully hand-written proof: "*every valid
K=3 screw closes ⟹ periodic*" is now a clean, elementary statement (finite-group order),
and the only remaining gap to a paper-proof is showing every space-tiler must contain a
screw — which is exactly the content currently being ground out cube by cube.
