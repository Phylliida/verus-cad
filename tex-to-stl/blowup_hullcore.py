#!/usr/bin/env python3
"""Hull-core variant of the blown-up kit.

Instead of joining the exploded cells with individual struts, join them with a
shrunk convex hull: take the convex hull of the exploded pieces, scale it by
`hull` (< 1) about the centroid, and union that solid core with the pieces.
The pieces poke out past the core; the gaps between them read as grooves whose
floor is the core surface.  One manifold STL, exported via OpenSCAD's CGAL
union (needs `openscad` on PATH).

Usage:
    python3 blowup_hullcore.py <out.stl> <explode> <hull> [in_dir]

Defaults: explode=1.04  hull=0.96  in_dir=c2_congruent_out
"""
import glob
import os
import subprocess
import sys

import blowup_pieces as B


def main():
    out = sys.argv[1] if len(sys.argv) > 1 else "c2_blownup_out/blownup_hullcore.stl"
    explode = float(sys.argv[2]) if len(sys.argv) > 2 else 1.04
    hull = float(sys.argv[3]) if len(sys.argv) > 3 else 0.96
    in_dir = sys.argv[4] if len(sys.argv) > 4 else "c2_congruent_out"

    files = sorted(glob.glob(os.path.join(in_dir, "shell_[0-9]*.stl")))
    pieces = {os.path.basename(p)[6:-4]: B.read_stl(p) for p in files}
    names = list(pieces)
    centroid = {n: B.mean([v for tri in pieces[n] for v in tri]) for n in names}
    G = B.mean(list(centroid.values()))
    disp = {n: B.scl(B.sub(centroid[n], G), explode - 1.0) for n in names}

    tris = []
    for n in names:
        d = disp[n]
        for t in pieces[n]:
            tris.append(tuple(B.add(v, d) for v in t))

    outdir = os.path.dirname(out) or "."
    os.makedirs(outdir, exist_ok=True)
    piece_stl = os.path.join(outdir, "_pieces_tmp.stl")
    B.write_binary_stl(piece_stl, tris, name="pieces")
    C = B.mean([v for t in tris for v in t])

    scad = os.path.join(outdir, "_hullcore_tmp.scad")
    base = os.path.basename(piece_stl)
    with open(scad, "w") as f:
        f.write(f"C = [{C[0]:.6f}, {C[1]:.6f}, {C[2]:.6f}];\n")
        f.write("union() {\n")
        f.write(f'  import("{base}");\n')
        f.write(f"  translate(C) scale({hull}) translate([-C[0],-C[1],-C[2]])\n")
        f.write(f'    hull() import("{base}");\n')
        f.write("}\n")

    subprocess.run(["openscad", "-o", out, scad], check=True,
                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    os.remove(piece_stl)
    os.remove(scad)
    print(f"wrote {out}  (explode {explode}, hull {hull})")


if __name__ == "__main__":
    main()
