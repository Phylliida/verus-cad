#!/usr/bin/env python3
"""Deep verification of a symmetric metric-products realization:
non-degeneracy (volumes, edge lengths), distinct facets, and the
Tamari-interval property (a linear functional orienting the 1-skeleton
exactly as the 2-Tamari Hasse diagram)."""
import json
import math
import sys
from collections import defaultdict

from symmetric_metric_feasibility import (
    edge, sub, cross, dot, norm, unit, newell,
    load_complex, boundary_structure,
)
from symmetric_metric_optimize import centroid, covariance, jacobi3


def cell_volume(flist, pos):
    """Signed volume via divergence theorem; faces oriented outward first."""
    cvs = set()
    for f in flist:
        cvs.update(f)
    cc = centroid([pos[v] for v in cvs])
    vol = 0.0
    for f in flist:
        pts = [pos[v] for v in f]
        c0 = centroid(pts)
        n = newell(pts)
        if dot(sub(c0, cc), n) < 0:
            pts = pts[::-1]
        for i in range(1, len(pts) - 1):
            a, b, c = pts[0], pts[i], pts[i + 1]
            vol += (a[0] * (b[1] * c[2] - b[2] * c[1])
                    - a[1] * (b[0] * c[2] - b[2] * c[0])
                    + a[2] * (b[0] * c[1] - b[1] * c[0])) / 6.0
    return vol


def all_primitive_edges(cells):
    es = set()
    for piece, flist in cells.items():
        for f in flist:
            m = len(f)
            for i in range(m):
                es.add(edge(f[i], f[(i + 1) % m]))
    return sorted(es)


def find_orienting_functional(edges_list, ref_pos, pos):
    """Find c with dot(c, b-a) matching the x-axis orientation in ref_pos,
    for every primitive edge. Perceptron-style; returns (c, ok)."""
    oriented = []
    for a, b in edges_list:
        s = ref_pos[b][0] - ref_pos[a][0]
        if abs(s) < 1e-9:
            raise ValueError(f"reference edge {a}-{b} not oriented by x")
        oriented.append((a, b) if s > 0 else (b, a))
    c = [1.0, 0.0, 0.0]
    for _ in range(20000):
        worst, wd = None, 0.0
        for a, b in oriented:
            d = unit(sub(pos[b], pos[a]))
            v = dot(tuple(c), d)
            if v < wd:
                wd, worst = v, d
        if worst is None:
            return unit(tuple(c)), True
        for k in range(3):
            c[k] += 0.1 * worst[k]
    return unit(tuple(c)), False


def main():
    coords_file = sys.argv[1]
    pos = {v: tuple(p) for v, p in json.load(open(coords_file)).items()}
    ref = {v: tuple(p) for v, p in
           json.load(open("convex_product_coords.json")).items()}
    _coords, _faces, cells = load_complex()
    span = max(max(p[k] for p in pos.values()) -
               min(p[k] for p in pos.values()) for k in range(3))

    print(f"=== deep verification: {coords_file} (span {span:.3f}) ===")

    # cell volumes
    vols = {piece: cell_volume(flist, pos) for piece, flist in cells.items()}
    total = sum(vols.values())
    print(f"cell volumes: min {min(vols.values()):.4f}, "
          f"max {max(vols.values()):.4f}, total {total:.4f}")
    assert min(vols.values()) > 1e-3, "degenerate cell!"

    # outer hull volume vs sum of cells (exact tiling check)
    fgroups, corners, paths = boundary_structure(
        cells, "convex_product_coords.json")
    count = defaultdict(int)
    order = {}
    for piece, flist in cells.items():
        for f in flist:
            count[frozenset(f)] += 1
            order[frozenset(f)] = f
    bfaces = [order[k] for k, v in count.items() if v == 1]
    shell_vol = cell_volume(bfaces, pos)
    print(f"shell volume {shell_vol:.4f} vs sum of cells {total:.4f} "
          f"(diff {abs(shell_vol - total):.2e})")

    # min primitive edge length
    es = all_primitive_edges(cells)
    lens = [norm(sub(pos[b], pos[a])) for a, b in es]
    print(f"primitive edges: {len(es)}, min length {min(lens):.4f} "
          f"({min(lens) / span:.4f} of span)")

    # min corner-corner distance
    dmin = min(norm(sub(pos[a], pos[b]))
               for i, a in enumerate(corners) for b in corners[i + 1:])
    print(f"min corner-corner distance: {dmin:.4f}")

    # facet normals pairwise distinct
    geo_normals = []
    for grp_faces in _facet_polys(cells, pos):
        pts = [pos[v] for f in grp_faces for v in f]
        c0 = centroid(pts)
        C = covariance(pts, c0)
        evals, evecs = jacobi3(C)
        geo_normals.append(unit(evecs[min(range(3), key=lambda i: evals[i])]))
    worst = 0.0
    for i in range(len(geo_normals)):
        for j in range(i + 1, len(geo_normals)):
            worst = max(worst, abs(dot(geo_normals[i], geo_normals[j])))
    print(f"9 facet planes: max |cos angle| between distinct normals "
          f"{worst:.4f} (must be < 1)")

    # Tamari interval property
    c, ok = find_orienting_functional(es, ref, pos)
    if ok:
        margins = []
        for a, b in es:
            s = ref[b][0] - ref[a][0]
            aa, bb = (a, b) if s > 0 else (b, a)
            margins.append(dot(c, unit(sub(pos[bb], pos[aa]))))
        print(f"Tamari orientation: functional c = "
              f"({c[0]:.3f}, {c[1]:.3f}, {c[2]:.3f}) orients ALL "
              f"{len(es)} edges as the 2-Tamari Hasse diagram "
              f"(min margin {min(margins):.4f})")
    else:
        print("Tamari orientation: NO functional found (perceptron failed)")


def _facet_polys(cells, pos):
    from symmetric_metric_optimize import facet_groups_faces
    return facet_groups_faces(cells)


if __name__ == "__main__":
    main()
