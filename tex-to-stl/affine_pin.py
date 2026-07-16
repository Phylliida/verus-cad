#!/usr/bin/env python3
"""Pin flow toward the reference in AFFINE gauge (the metric-products
variety is GL(3)-invariant, so the pin only penalizes non-affine shape
difference).

Usage: python3 affine_pin.py <start_coords.json> <c2:0|1> <out.json>
                             [iters] [w_pin]
"""
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


def solveN(M, b):
    n = len(M)
    A = [row[:] + [b[i]] for i, row in enumerate(M)]
    for col in range(n):
        piv = max(range(col, n), key=lambda r: abs(A[r][col]))
        A[col], A[piv] = A[piv], A[col]
        p = A[col][col]
        for r in range(n):
            if r != col and abs(A[r][col]) > 0:
                f = A[r][col] / p
                for k in range(col, n + 1):
                    A[r][k] -= f * A[col][k]
    return [A[i][n] / A[i][i] for i in range(n)]


def best_affine(P, Q):
    n = len(P)
    X = [[p[0], p[1], p[2], 1.0] for p in P]
    XtX = [[sum(X[k][i] * X[k][j] for k in range(n)) for j in range(4)]
           for i in range(4)]
    params = []
    for dim in range(3):
        Xty = [sum(X[k][i] * Q[k][dim] for k in range(n)) for i in range(4)]
        params.append(solveN([row[:] for row in XtX], Xty))

    def f(p):
        return tuple(params[d][0] * p[0] + params[d][1] * p[1]
                     + params[d][2] * p[2] + params[d][3] for d in range(3))
    rms = math.sqrt(sum(norm(sub(f(P[k]), Q[k])) ** 2
                        for k in range(n)) / n)
    return f, rms


def main():
    start_file = sys.argv[1]
    use_c2 = bool(int(sys.argv[2]))
    out_file = sys.argv[3]
    iters = int(sys.argv[4]) if len(sys.argv) > 4 else 2500
    w_pin_max = float(sys.argv[5]) if len(sys.argv) > 5 else 0.5
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

    pos = {v: tuple(p) for v, p in json.load(open(start_file)).items()}
    ref = json.load(open("associahedron_ref.json"))
    rverts = [tuple(v) for v in ref["verts"]]
    iso = json.load(open("ref_best_iso.json"))["iso"]
    refP = [rverts[iso[c]] for c in corners]

    def fit_targets(pos):
        """affine-map REF onto current corners; return rms and targets."""
        Q = [pos[c] for c in corners]
        f, rms = best_affine(refP, Q)
        targets = {c: f(refP[i]) for i, c in enumerate(corners)}
        if use_c2:
            done = set()
            for c in corners:
                if c in done:
                    continue
                gc = g[c]
                m = tuple((targets[c][k]
                           + sym_image(targets[gc], kind)[k]) / 2
                          for k in range(3))
                targets[c] = m
                targets[gc] = sym_image(m, kind)
                done.update((c, gc))
        return rms, targets

    # forward metric for reporting: our corners affine-mapped ONTO ref
    def rms_to_ref(pos):
        P = [pos[c] for c in corners]
        _f, rms = best_affine(P, refP)
        return rms

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

    ref_span = 2 * 6.407166
    print(f"start: affine rms to ref {rms_to_ref(pos):.4f} "
          f"({rms_to_ref(pos)/ref_span:.2%} of ref span), c2={use_c2}")

    for it in range(iters):
        wp = w_pin_max if it < iters - 500 else 0.0
        _r, targets = fit_targets(pos)

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
            if use_c2 and v in g:
                add_point(sym_image(pos[g[v]], kind), w_sym)
            if wp > 0 and v in targets:
                add_point(targets[v], wp)
            add_point(pos[v], 0.05)

            s = solve3(A, b)
            newpos[v] = s if s is not None else pos[v]
        pos = newpos
        if use_c2:
            project_symmetry(pos, g, corners, kind)
        fix_scale(pos)

        if it % 250 == 0 or it == iters - 1:
            worst_plan = max(abs(dot(sub(pos[v], plane_of(f, pos)[0]),
                                     plane_of(f, pos)[1]))
                             for f in faces for v in f)
            r = rms_to_ref(pos)
            print(f"  it {it:4d} wp={wp:.2f} affine-rms={r:.4f} "
                  f"({r/ref_span:.2%}) planar={worst_plan:.2e}")

    stats = report(pos, cells, faces, classes, fgroups, g, corners,
                   kind, kinds)
    r = rms_to_ref(pos)
    print(f"\nFINAL affine rms to ref: {r:.4f} ({r/ref_span:.2%} of ref span)")
    json.dump({v: list(p) for v, p in pos.items()}, open(out_file, "w"),
              indent=1)
    print(f"wrote {out_file}")


if __name__ == "__main__":
    main()
