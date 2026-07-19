// Blown-up C2 congruent kit: the 14 cells pushed radially apart,
// open gaps between them, no connectors.  Adjust `explode` and re-render.
//   explode = 1.0  -> original watertight tiling (no gaps)
//   explode > 1.0  -> cells fly apart from the common centre

explode = 1.6;   // <-- spacing knob

G = [-0.04126, 0.10202, -0.35364];   // common centre

module cell(file, c) {
    translate((explode - 1) * (c - G)) import(file);
}

cell("../c2_congruent_out/shell_321-0.stl", [0.16023, 3.47832, -0.88348]);
cell("../c2_congruent_out/shell_421-1.stl", [1.55644, 2.63588, 0.51583]);
cell("../c2_congruent_out/shell_431-11.stl", [-3.36003, 1.92420, -0.98675]);
cell("../c2_congruent_out/shell_432-111.stl", [2.21157, 1.56129, -3.61003]);
cell("../c2_congruent_out/shell_521-3.stl", [1.28339, 0.94733, 2.47436]);
cell("../c2_congruent_out/shell_531-21.stl", [-1.45965, 0.38968, 1.68466]);
cell("../c2_congruent_out/shell_532-211.stl", [3.57420, 0.70670, -2.21238]);
cell("../c2_congruent_out/shell_541-33.stl", [-4.59616, -0.39244, -2.77138]);
cell("../c2_congruent_out/shell_542-221.stl", [-2.22879, -0.52123, -3.86091]);
cell("../c2_congruent_out/shell_621-5.stl", [1.70161, -0.88950, 2.81972]);
cell("../c2_congruent_out/shell_631-51.stl", [-0.64697, -1.93286, 2.74440]);
cell("../c2_congruent_out/shell_632-411.stl", [3.44571, -1.51895, -0.12201]);
cell("../c2_congruent_out/shell_641-43.stl", [-2.30101, -2.57042, 0.25861]);
cell("../c2_congruent_out/shell_642-321.stl", [0.08181, -2.38971, -1.00163]);
