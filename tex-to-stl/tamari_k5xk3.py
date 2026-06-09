#!/usr/bin/env python3
"""K5 x K3  (3D associahedron x segment) -- the cube-containing flavor.

A prism over the associahedron. Its 11 facets are products of associahedra:
  * 2 caps  = K5 x {0,1}            (two copies of the 3-associahedron)
  * 3 sides = square x K3   = cube
  * 6 sides = pentagon x K3 = pentagon-prism
Vertices = T4 x C2  (Tamari lattice x 2-chain) = 28.

Schlegel through one K5 cap: that cap = outer 3D associahedron; the interior is
filled by the inner (scaled) K5 plus 9 frustum cells (3 cubes + 6 prisms).
"""
import os
import math
import tamari_normal_fan as N
import tamari_symmetric as S
import tamari_k6_schlegel as SC


def main():
    out = "tamari_k5xk3"; os.makedirs(out, exist_ok=True)
    V, labels, _ = S.symmetric_associahedron()           # 14 pts, the symmetric K5
    planes, faces = N.hull_facets(V)                      # 9 facets (3 sq + 6 pent)
    c = tuple(sum(v[i] for v in V)/len(V) for i in range(3))   # center ~origin

    # Schlegel of K5 x [0,1] through the bottom cap == radial nesting:
    # inner K5 is V scaled by s about the center; frustums fill the shell.
    eps = 1.0
    s = eps/(1.0+eps)                                     # inner scale (0.5)
    def scale(v): return tuple(c[i] + s*(v[i]-c[i]) for i in range(3))
    inner = [scale(v) for v in V]

    def cube_or_prism(f): return "cube" if len(f) == 4 else "prism"

    cells = []                                            # (name, 3D point list)
    cells.append(("innerK5", list(inner)))
    for fi, f in enumerate(faces):
        fl = list(f)
        pts = [V[i] for i in fl] + [inner[i] for i in fl]
        cells.append((f"{cube_or_prism(f)}{fi}", pts))

    # outer shell = the cap we projected through = the full K5 surface
    shell = SC.hull_triangles(V)
    N.write_stl(f"{out}/shell.stl", shell)
    shell_vol = SC.cell_volume(shell)

    from collections import Counter
    total = 0.0; tally = Counter()
    for name, pts in cells:
        tris = SC.hull_triangles(pts)
        ref = tuple(sum(p[i] for p in pts)/len(pts) for i in range(3))
        N.write_stl(f"{out}/cell_{name}.stl", tris, ref)
        v = SC.cell_volume(tris); total += v
        tally["cube" if name.startswith("cube") else
              "prism" if name.startswith("prism") else "K5"] += 1

    print(f"K5 x K3 prism, Schlegel through a K5 cap (inner scale s={s})")
    print(f"vertices: {2*len(V)} = T4 x C2")
    print(f"outer shell (3D associahedron): {len(shell)} tris, vol {shell_vol:.4f}")
    print(f"interior cells: {len(cells)}  {dict(tally)}")
    print(f"tiling check |sum(cells) - shell| = {abs(total-shell_vol):.2e}")
    print(f"wrote {out}/shell.stl + {len(cells)} cell STLs")


if __name__ == "__main__":
    main()
