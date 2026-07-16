#!/usr/bin/env python3
"""Project the reference shape onto the metric-products variety: initialize
with corners AT the reference (interior Horn-carried from the C2 solution),
then relax with validity terms + C2 projection and measure where it lands."""
import json
import math
import sys
from collections import defaultdict

from symmetric_metric_feasibility import (
    edge, sub, dot, norm, unit,
    load_complex, forced_parallel_uf, boundary_structure,
    graph_automorphisms, perm_order)
from symmetric_metric_optimize import (
    centroid, solve3, plane_of, class_direction, sym_image,
    project_symmetry, build_constraint_data, facet_groups_faces,
    span_of, report)
from ref_match import horn_align


def main():
    iters = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
    w_face, w_par, w_facet, w_sym = 1.0, 2.0, 12.0, 30.0

    coords, faces_raw, cells = load_complex()
    uf, kinds = forced_parallel_uf(cells)
    _fg9, corners, paths = boundary_structure(
        cells, "convex_product_coords.json")
    for path in paths:
        for i in range(len(path) - 2):
            uf.union(edge(path[i], path[i + 1]),
                     edge(path[i + 1], path[i + 2]))
    faces, classes = build_constraint_data(cells, uf, paths)
    fgroups = facet_groups_faces(cells)

    edges21 = [tuple(sorted((p[0], p[-1]))) for p in paths]
    autos = graph_automorphisms(corners, edges21)
    ident = {v: v for v in corners}
    invs = [g for g in autos if g != ident and perm_order(g, corners) == 2]
    g = invs[6]
    kind = "C2"

    base = {v: tuple(p) for v, p in
            json.load(open("symmetric_metric_inv6_coords.json")).items()}
    ref = json.load(open("associahedron_ref.json"))
    rverts = [tuple(v) for v in ref["verts"]]
    iso = json.load(open("ref_best_iso.json"))["iso"]
    refP = [rverts[iso[c]] for c in corners]

    # transform CURRENT solution into the reference frame, then overwrite
    # corners with the exact reference corners
    P = [base[c] for c in corners]
    rms0, transform, refl = horn_align(P, refP)
    pos = {v: transform(p) for v, p in base.items()}
    for i, c in enumerate(corners):
        pos[c] = refP[i]

    # the ref C2 axis: find it so hard C2-projection works in this frame.
    # inv#6 is an exact isometry of ref: get its rotation via Horn on
    # (refP -> permuted refP), extract axis, change frame to axis=z.
    Q = [refP[corners.index(g[c])] for c in corners]
    _r, t2, _refl = horn_align(refP, Q)
    # rotation part: apply to unit vectors at centroid
    c0 = centroid(refP)
    def rotpart(v):
        a = t2((c0[0] + v[0], c0[1] + v[1], c0[2] + v[2]))
        b = t2(c0)
        return sub(a, b)
    R = [rotpart((1, 0, 0)), rotpart((0, 1, 0)), rotpart((0, 0, 1))]
    # axis = eigenvector for eigenvalue +1 of R (as column-applied matrix)
    # R here: columns = images of basis vectors -> R[j] is image of e_j
    M = [[R[j][i] for j in range(3)] for i in range(3)]
    # power iteration on (M + I)/2 symmetrized... simpler: axis from
    # skew part is zero for C2; use (M + M^T)/2 eigenvector with eval 1
    from ref_match import jacobiN
    S = [[(M[i][j] + M[j][i]) / 2 for j in range(3)] for i in range(3)]
    evals, evecs = jacobiN(S, 3)
    axis = unit(evecs[max(range(3), key=lambda i: evals[i])])
    print(f"ref C2 axis: ({axis[0]:.4f}, {axis[1]:.4f}, {axis[2]:.4f})")

    # frame: axis -> z, centroid path... fixed point of the C2 on the axis:
    # use centroid of ref corners (isometry fixes it)
    from symmetric_metric_optimize import orthobasis
    e1, e2, e3 = orthobasis(axis)
    def to_frame(p):
        d = sub(p, c0)
        return (dot(d, e1), dot(d, e2), dot(d, e3))
    pos = {v: to_frame(p) for v, p in pos.items()}
    refT = {c: to_frame(refP[i]) for i, c in enumerate(corners)}

    err = max(norm(sub(sym_image(pos[g[c]], kind), pos[c])) for c in corners)
    print(f"corner C2 error at init (should be ~0): {err:.2e}")

    R0 = math.sqrt(sum(dot(pos[c], pos[c]) for c in corners) / len(corners))
    def fix_scale(pos):
        R = math.sqrt(sum(dot(pos[c], pos[c]) for c in corners)
                      / len(corners))
        s = R0 / R
        for v in list(pos):
            p = pos[v]
            pos[v] = (s * p[0], s * p[1], s * p[2])

    vlist = sorted(pos)
    vfaces = defaultdict(list)
    for fi, f in enumerate(faces):
        for v in f:
            vfaces[v].append(fi)
    vedges = defaultdict(list)
    for ci, C in enumerate(classes):
        for a, b in C:
            vedges[a].append((b, ci))
            vedges[b].append((a, ci))
    vgroups = defaultdict(list)
    for gi, grp in enumerate(fgroups):
        vs = set()
        for f in grp:
            vs.update(f)
        for v in vs:
            vgroups[v].append(gi)

    for it in range(iters):
        planes = [plane_of(f, pos) for f in faces]
        dirs = [class_direction(C, pos) for C in classes]
        gplanes = []
        for grp in fgroups:
            ns, cs, ref_n = [], [], None
            for f in grp:
                cc, n0 = plane_of(f, pos)
                if ref_n is None:
                    ref_n = n0
                if dot(n0, ref_n) < 0:
                    n0 = (-n0[0], -n0[1], -n0[2])
                ns.append(n0)
                cs.append(cc)
            n = unit(tuple(sum(v[k] for v in ns) for k in range(3)))
            gplanes.append((centroid(cs), n))

        newpos = {}
        for v in vlist:
            A = [[0.0] * 3 for _ in range(3)]
            b = [0.0, 0.0, 0.0]

            def add_plane(cc, n, w):
                for i in range(3):
                    for j in range(3):
                        A[i][j] += w * n[i] * n[j]
                    b[i] += w * n[i] * dot(n, cc)

            def add_point(q, w):
                for i in range(3):
                    A[i][i] += w
                    b[i] += w * q[i]

            for fi in vfaces[v]:
                add_plane(planes[fi][0], planes[fi][1], w_face)
            for gi in vgroups[v]:
                add_plane(gplanes[gi][0], gplanes[gi][1], w_facet)
            for (u, ci) in vedges[v]:
                d = dirs[ci]
                pu = pos[u]
                for i in range(3):
                    for j in range(3):
                        A[i][j] += w_par * ((1.0 if i == j else 0.0)
                                            - d[i] * d[j])
                    b[i] += w_par * sum(((1.0 if i == j else 0.0)
                                         - d[i] * d[j]) * pu[j]
                                        for j in range(3))
            if v in g:
                add_point(sym_image(pos[g[v]], kind), w_sym)
            add_point(pos[v], 0.05)

            s = solve3(A, b)
            newpos[v] = s if s is not None else pos[v]
        pos = newpos
        project_symmetry(pos, g, corners, kind)
        fix_scale(pos)

        if it % 300 == 0 or it == iters - 1:
            Pn = [pos[c] for c in corners]
            rms, _t, _r2 = horn_align(refP, Pn)
            worst_plan = max(abs(dot(sub(pos[v], plane_of(f, pos)[0]),
                                     plane_of(f, pos)[1]))
                             for f in faces for v in f)
            print(f"  it {it:4d}  rms-to-ref={rms:.4f} "
                  f"({rms/span_of(pos):.2%})  planar={worst_plan:.2e}")

    stats = report(pos, cells, faces, classes, fgroups, g, corners, kind,
                   kinds)
    Pn = [pos[c] for c in corners]
    rms, _t, _r2 = horn_align(refP, Pn)
    print(f"\nfinal Horn rms to ref: {rms:.4f} ({rms/span_of(pos):.2%})")
    json.dump({v: list(p) for v, p in pos.items()},
              open("projected_from_ref_coords.json", "w"), indent=1)
    print("wrote projected_from_ref_coords.json")


if __name__ == "__main__":
    main()
