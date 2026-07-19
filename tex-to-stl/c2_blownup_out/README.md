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

## Files (all at explode 1.10 — gaps ≈ 0.19–0.49, mean 0.34, ~1/10 of a piece)

| file                  | strut width (fraction of shared face) | look |
|-----------------------|---------------------------------------|------|
| `blownup_sh0.80.stl`  | 0.80 | struts clearly thinner; deepest grooves |
| `blownup_sh0.85.stl`  | 0.85 | struts slightly inset; clean thin grooves *(= `blownup.stl`)* |
| `blownup_sh0.90.stl`  | 0.90 | struts nearly face-width; subtle grooves |
| `blownup_sh0.95.stl`  | 0.95 | struts almost face-width; hairline seams |
| `blownup.stl`         | 0.85 | default copy |

Previews: `prev_iso.png`, `prev_top.png` (of `blownup.stl`).

## Regenerate / retune

    python3 ../blowup_pieces.py ../c2_congruent_out <out.stl> <explode> <shrink> <pen>

- `explode` (default 1.10) — radial spread. 1.08 ≈ hairline gaps, 1.25 ≈ 1/10
  of the bbox-diagonal (clearly separated blocks).
- `shrink`  (default 0.85) — strut cross-section as a fraction of the shared
  face. Higher = thicker struts, closer to the piece width.
- `pen`     (default 0.45) — how far each strut dives into its cells (overlap
  for a robust union). Keep ≳ 0.3.

Scale freely in the slicer.
