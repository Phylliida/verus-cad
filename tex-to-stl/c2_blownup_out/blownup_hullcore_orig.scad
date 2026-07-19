// Blown-up hull-core kit, built from the ORIGINAL figure.tex dissection cells
// (../pieces_out/all_*.stl) instead of the C2-congruent shells.
//
// Same construction as the C2 hull-core variant: the 14 exploded cells emboss
// out of a solid core = hull(cells) scaled down about the center of mass,
// filling the gaps between cells with a rounded nugget (the "barely-embossed
// cut-nugget" look).
//
//   explode    = 1.0  -> original watertight tiling
//   explode    > 1.0  -> cells fly apart radially from the common centre G
//   hull_scale        -> convex-hull core shrink factor
//
// G is the true center of mass here: the mean of the 14 original cell
// centroids.  Radial explosion about G leaves the centroid fixed, so we scale
// the hull about G.  (Unlike the C2 kit, the original cells are NOT congruent
// and NOT arranged with any rotational symmetry, so G is just their centroid.)
//
// NOTE: the hull is taken over per-cell convex hulls (cellsh), not the raw
// imports.  Feeding all 14 raw imports to a single hull() trips a CGAL "mesh
// is not closed" Nef-conversion bug in OpenSCAD; wrapping each cell in its own
// hull() first sidesteps it.

explode    = 1.08;   // <-- cell spacing knob
hull_scale = 0.99;   // <-- convex-hull core shrink factor

G = [-3.98140, -3.83532, -4.23065];

module cell(f, c)  { translate((explode - 1) * (c - G)) import(f); }
module cellh(f, c) { hull() cell(f, c); }

module cells() {
    cell("../pieces_out/all_321-0.stl",   [0.01389, -3.86111, -4.27778]);
    cell("../pieces_out/all_421-1.stl",   [-1.56250, -6.18750, -4.18750]);
    cell("../pieces_out/all_431-11.stl",  [-1.75000, -1.34375, -2.53125]);
    cell("../pieces_out/all_432-111.stl", [-1.19444, -3.75000, -6.88889]);
    cell("../pieces_out/all_521-3.stl",   [-4.34375, -6.81250, -2.18750]);
    cell("../pieces_out/all_531-21.stl",  [-4.11111, -3.67361, -1.54861]);
    cell("../pieces_out/all_532-211.stl", [-2.81250, -6.02083, -6.91667]);
    cell("../pieces_out/all_541-33.stl",  [-4.00000, 0.44444, -4.05556]);
    cell("../pieces_out/all_542-221.stl", [-3.54167, -1.10417, -6.41667]);
    cell("../pieces_out/all_621-5.stl",   [-7.00000, -6.75000, -2.75000]);
    cell("../pieces_out/all_631-51.stl",  [-7.00000, -4.04167, -1.83333]);
    cell("../pieces_out/all_632-411.stl", [-6.10417, -6.50000, -6.08333]);
    cell("../pieces_out/all_641-43.stl",  [-6.37500, -1.13542, -3.55208]);
    cell("../pieces_out/all_642-321.stl", [-5.95833, -2.95833, -6.00000]);
}

module cellsh() {
    cellh("../pieces_out/all_321-0.stl",   [0.01389, -3.86111, -4.27778]);
    cellh("../pieces_out/all_421-1.stl",   [-1.56250, -6.18750, -4.18750]);
    cellh("../pieces_out/all_431-11.stl",  [-1.75000, -1.34375, -2.53125]);
    cellh("../pieces_out/all_432-111.stl", [-1.19444, -3.75000, -6.88889]);
    cellh("../pieces_out/all_521-3.stl",   [-4.34375, -6.81250, -2.18750]);
    cellh("../pieces_out/all_531-21.stl",  [-4.11111, -3.67361, -1.54861]);
    cellh("../pieces_out/all_532-211.stl", [-2.81250, -6.02083, -6.91667]);
    cellh("../pieces_out/all_541-33.stl",  [-4.00000, 0.44444, -4.05556]);
    cellh("../pieces_out/all_542-221.stl", [-3.54167, -1.10417, -6.41667]);
    cellh("../pieces_out/all_621-5.stl",   [-7.00000, -6.75000, -2.75000]);
    cellh("../pieces_out/all_631-51.stl",  [-7.00000, -4.04167, -1.83333]);
    cellh("../pieces_out/all_632-411.stl", [-6.10417, -6.50000, -6.08333]);
    cellh("../pieces_out/all_641-43.stl",  [-6.37500, -1.13542, -3.55208]);
    cellh("../pieces_out/all_642-321.stl", [-5.95833, -2.95833, -6.00000]);
}

union() {
    cellsh();
    // shrunk convex-hull core, scaled about the center of mass G
    translate(G) scale(hull_scale) translate(-G) hull() cellsh();
}
