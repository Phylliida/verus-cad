#!/usr/bin/env python3
"""Path-following on the metric-products variety toward the associahedron.fbx
reference (D3d 'typical' associahedron), keeping exact C2 symmetry and full
validity throughout.

Continuation loop: small pin pulse (drag) -> pin-free re-polish (back to the
variety) -> measure Horn RMS. Keep the best valid snapshot; stop on stall.

Usage: python3 pin_to_reference.py [n_steps] [w_pin] [pulse_iters] [polish_iters]
"""
import json
import math
import sys
from collections import defaultdict

from symmetric_metric_feasibility import (
    UF, edge, sub, dot, norm, unit, newell,
    load_complex, forced_parallel_uf, boundary_structure,
    graph_automorphisms, perm_order)
from symmetric_metric_optimize import (
    centroid, solve3, plane_of, class_direction, sym_image,
    project_symmetry, build_constraint_data, facet_groups_faces,
    span_of, report)
from ref_match import horn_align


def main():
    n_steps = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    w_pin = float(sys.argv[2]) if len(sys.argv) > 2 else 0.6
    pulse_iters = int(sys.argv[3]) if len(sys.argv) > 3 else 40
    polish_iters = int(sys.argv[4]) if len(sys.argv) > 4 else 220
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

    pos = {v: tuple(p) for v, p in
           json.load(open("symmetric_metric_inv6_coords.json")).items()}

    ref = json.load(open("associahedron_ref.json"))
    rverts = [tuple(v) for v in ref["verts"]]
    iso = json.load(open("ref_best_iso.json"))["iso"]
    refP = [rverts[iso[c]] for c in corners]

    def fit_targets(pos):
        Q = [pos[c] for c in corners]
        rms, transform, refl = horn_align(refP, Q)
        targets = {c: transform(refP[i]) for i, c in enumerate(corners)}
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

    all_prim = sorted({e for C in classes for e in C}
                      | {edge(f[i], f[(i + 1) % len(f)])
                         for f in faces for i in range(len(f))})

    def sweep(pos, wp, targets, stiff=1.0, lmin=0.0):
        w_face_s, w_par_s, w_facet_s = (w_face * stiff, w_par * stiff,
                                        w_facet * stiff)
        planes = [plane_of(f, pos) for f in faces]
        dirs = [class_direction(C, pos) for C in classes]
        gplanes = []
        for grp in fgroups:
            ns, cs, ref_n = [], [], None
            for f in grp:
                c0, n0 = plane_of(f, pos)
                if ref_n is None:
                    ref_n = n0
                if dot(n0, ref_n) < 0:
                    n0 = (-n0[0], -n0[1], -n0[2])
                ns.append(n0)
                cs.append(c0)
            n = unit(tuple(sum(v[k] for v in ns) for k in range(3)))
            gplanes.append((centroid(cs), n))

        newpos = {}
        for v in vlist:
            A = [[0.0] * 3 for _ in range(3)]
            b = [0.0, 0.0, 0.0]

            def add_plane(c0, n, w):
                for i in range(3):
                    for j in range(3):
                        A[i][j] += w * n[i] * n[j]
                    b[i] += w * n[i] * dot(n, c0)

            def add_point(q, w):
                for i in range(3):
                    A[i][i] += w
                    b[i] += w * q[i]

            for fi in vfaces[v]:
                add_plane(planes[fi][0], planes[fi][1], w_face_s)
            for gi in vgroups[v]:
                add_plane(gplanes[gi][0], gplanes[gi][1], w_facet_s)
            for (u, ci) in vedges[v]:
                d = dirs[ci]
                pu = pos[u]
                for i in range(3):
                    for j in range(3):
                        A[i][j] += w_par_s * ((1.0 if i == j else 0.0)
                                              - d[i] * d[j])
                    b[i] += w_par_s * sum(((1.0 if i == j else 0.0)
                                           - d[i] * d[j]) * pu[j]
                                          for j in range(3))
            if lmin > 0:
                for (u, ci) in vedges[v]:
                    L = norm(sub(pos[v], pos[u]))
                    if 0 < L < lmin:
                        duv = unit(sub(pos[v], pos[u]))
                        tgt = tuple(pos[u][k] + lmin * duv[k]
                                    for k in range(3))
                        add_point(tgt, 4.0 * stiff)
            if v in g:
                add_point(sym_image(pos[g[v]], kind), w_sym)
            if wp > 0 and v in targets:
                add_point(targets[v], wp)
            add_point(pos[v], 0.05)

            s = solve3(A, b)
            newpos[v] = s if s is not None else pos[v]
        project_symmetry(newpos, g, corners, kind)
        fix_scale(newpos)
        return newpos

    def validity(pos):
        worst_plan = max(abs(dot(sub(pos[v], plane_of(f, pos)[0]),
                                 plane_of(f, pos)[1]))
                         for f in faces for v in f)
        worst_ang = 0.0
        for C in classes:
            d0 = class_direction(C, pos)
            for a, b_ in C:
                d = unit(sub(pos[b_], pos[a]))
                worst_ang = max(worst_ang, math.degrees(
                    math.acos(min(1.0, abs(dot(d, d0))))))
        ncv = 0
        S = span_of(pos)
        for piece, flist in cells.items():
            cvs = set()
            for f in flist:
                cvs.update(f)
            cc = centroid([pos[v] for v in cvs])
            ok = True
            for f in flist:
                c0, n = plane_of(f, pos)
                if dot(sub(cc, c0), n) > 0:
                    n = (-n[0], -n[1], -n[2])
                for v in cvs:
                    if dot(sub(pos[v], c0), n) > 1e-4 * S:
                        ok = False
            ncv += ok
        return worst_plan, worst_ang, ncv

    rms0, _t = fit_targets(pos)
    print(f"start: Horn rms {rms0:.4f} ({rms0/span_of(pos):.3%} of span)")

    # Stiffening: constant weak pin, validity weights ramp 1 -> stiff_max,
    # so the equilibrium tracks the pin-biased point ON the variety.
    T = n_steps          # reuse argv[1] as total iters here
    stiff_max = 60.0
    lmin = 0.15
    for it in range(T):
        t = it / max(1, T - 1)
        stiff = math.exp(math.log(stiff_max) * t)
        wp = w_pin if it < T - 400 else 0.0
        _r, targets = fit_targets(pos)
        pos = sweep(pos, wp, targets, stiff=stiff, lmin=lmin)
        if it % 200 == 0 or it == T - 1:
            rms, _t2 = fit_targets(pos)
            plan, ang, ncv = validity(pos)
            print(f"  it {it:4d} stiff={stiff:6.1f} wp={wp:.2f} "
                  f"rms={rms:.4f} ({rms/span_of(pos):.2%}) "
                  f"plan={plan:.1e} ang={ang:.3f} cv={ncv}")

    # final landing: pin off, full stiffness
    for _ in range(600):
        pos = sweep(pos, 0.0, {}, stiff=stiff_max, lmin=lmin)
    stats = report(pos, cells, faces, classes, fgroups, g, corners, kind,
                   kinds)
    rms, _t = fit_targets(pos)
    print(f"final Horn rms after deep polish: {rms:.4f} "
          f"({rms/span_of(pos):.3%} of span)")
    json.dump({v: list(p) for v, p in pos.items()},
              open("pinned_reference_coords.json", "w"), indent=1)
    print("wrote pinned_reference_coords.json")


if __name__ == "__main__":
    main()
