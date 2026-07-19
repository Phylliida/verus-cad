# Blown-up (exploded-but-connected) C2 congruent kit

The "shrink-wrap" version of `../c2_congruent_out/`: the 14 tiling cells are
pushed radially apart so a small gap opens between every pair of neighbours,
then each pair that used to share an internal wall is bridged by a **strut**
whose cross-section is a slightly-shrunk copy of that shared face. The strut
pokes a little way into both cells, so the crevices read as indented webbing —
like wrapping a balloon around the cluster and sucking the air out, leaving the
cells just barely separated and outlined by thin recessed grooves.

Each file is a multi-solid STL: every cell and every strut is its own closed,
watertight mesh, and each strut overlaps the two cells it joins. Any slicer
(Cura / Prusa / Bambu / OrcaSlicer) unions overlapping closed volumes, so it
prints as **one connected object**. Verified for every file below: 14/14 cells
and 28/28 struts watertight, union graph fully connected.

Two spacing sets are provided; within each, four strut widths.

### explode 1.04 — gaps ≈ 0.08–0.20, mean 0.14 (very tight)

| file                  | strut width (fraction of shared face) | look |
|-----------------------|---------------------------------------|------|
| `blownup_sh0.80.stl`  | 0.80 | struts clearly thinner; deepest grooves |
| `blownup_sh0.85.stl`  | 0.85 | struts slightly inset; clean thin grooves *(= `blownup.stl`)* |
| `blownup_sh0.90.stl`  | 0.90 | struts nearly face-width; subtle grooves |
| `blownup_sh0.95.stl`  | 0.95 | struts almost face-width; hairline seams |
| `blownup.stl`         | 0.85 | default copy |

### explode 1.02 — gaps ≈ 0.04–0.10, mean 0.07 (barely apart, faint etched seams)

| file                          | strut width |
|-------------------------------|-------------|
| `blownup_ex1.02_sh0.80.stl`   | 0.80 |
| `blownup_ex1.02_sh0.85.stl`   | 0.85 |
| `blownup_ex1.02_sh0.90.stl`   | 0.90 |
| `blownup_ex1.02_sh0.95.stl`   | 0.95 |

Previews: `prev_iso.png`, `prev_top.png` (1.04), `prev_ex1.02_iso.png` (1.02).

## Hull-core variant — `blownup_hullcore.stl`

A different way to hold the cluster together: instead of struts, the exploded
pieces (explode 1.04) are unioned with a convex hull of themselves scaled to
0.96 about the centroid. The 0.96 core fills the interior right up to ~4% below
the surface, so the pieces read as a **solid faceted associahedron with the 12
Tamari cells just barely embossed** — a cut-nugget / paperweight look rather
than separated pieces. (Unioning with a convex hull necessarily fills the
concavities between cells, so this construction is inherently subtle; the hull
scale — not the explode — is what controls how much the cells emerge. Lower it
toward ~0.85 for deeper grooves.) One watertight manifold (CGAL union).

Regenerate / retune:

    python3 ../blowup_hullcore.py <out.stl> <explode> <hull> [in_dir]   # needs openscad

Previews: `prev_hullcore_iso.png`, `prev_hullcore_top.png`.

## Regenerate / retune

    python3 ../blowup_pieces.py ../c2_congruent_out <out.stl> <explode> <shrink> <pen>

- `explode` (default 1.04) — radial spread. 1.08 ≈ hairline gaps, 1.25 ≈ 1/10
  of the bbox-diagonal (clearly separated blocks).
- `shrink`  (default 0.85) — strut cross-section as a fraction of the shared
  face. Higher = thicker struts, closer to the piece width.
- `pen`     (default 0.45) — how far each strut dives into its cells (overlap
  for a robust union). Keep ≳ 0.3.

Scale freely in the slicer.
