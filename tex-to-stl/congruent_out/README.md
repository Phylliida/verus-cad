# Congruent-kit model (10 distinct shapes)

Bergeron's 14-cell 2-Tamari decomposition of the associahedron, realized so
that pieces come in congruent groups. Print counts:

| STL | print | congruent partner |
|---|---|---|
| shell_321-0.stl   | x2 works (or print partner) | shell_432-111.stl (exact translate) |
| shell_421-1.stl   | x2 works | shell_532-211.stl (exact translate) |
| shell_431-11.stl  | x2 works | shell_542-221.stl (congruent by rotation) |
| shell_521-3.stl   | x2 works | shell_632-411.stl (congruent by rotation) |
| shell_531-21.stl  | x1 | (unique, K5 cell) |
| shell_541-33.stl  | x1 | (unique, cube) |
| shell_621-5.stl   | x1 | (unique, cube) |
| shell_631-51.stl  | x1 | (unique, prism) |
| shell_641-43.stl  | x1 | (unique, prism) |
| shell_642-321.stl | x1 | (unique, K5 cell) |

All 14 individual STLs are also present (positioned for assembly), plus
shell.stl (outer boundary) and shell_assembly.stl (everything).
Every cell is convex, faces exactly planar, cubes are true parallelepipeds
and prisms true pentagon-prisms; the pieces tile the associahedron exactly.
Scale freely in the slicer — all properties are scale-invariant.
