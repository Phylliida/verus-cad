#!/usr/bin/env python3
"""Attempt an order-2-symmetric realization of Bergeron's 14-cell
decomposition with genuine metric-product cells.

Usage: python3 symmetric_metric_optimize.py [inv_index] [iters]
  inv_index in {0, 2, 6}: which passing involution (0/2 mirror, 6 = C2 rotation)

Starts from convex_product_coords.json (convex + metric products, asymmetric),
aligns to a symmetry-adapted frame, then anneals a symmetry term on the 14
outer corners alongside planarity / parallelism / shell-facet terms.
"""
import json
import math
import sys
from collections import defaultdict

from tex_to_stl import parse_tex
from symmetric_metric_feasibility import (
    UF, edge, sub, cross, dot, norm, unit, newell,
    load_complex, forced_parallel_uf, boundary_structure,
    graph_automorphisms, perm_order, apply_edge, join_partition,
    matching_violations, facet_violations, facet_edge_map, cyclic,
)


# --------------------------------------------------------- tiny linear algebra

def jacobi3(S, sweeps=60):
    """Eigen-decomposition of a symmetric 3x3. Returns (evals, evecs-cols)."""
    a = [row[:] for row in S]
    v = [[1.0 if i == j else 0.0 for j in range(3)] for i in range(3)]
    for _ in range(sweeps):
        p, q, mx = 0, 1, abs(a[0][1])
        if abs(a[0][2]) > mx:
            p, q, mx = 0, 2, abs(a[0][2])
        if abs(a[1][2]) > mx:
            p, q, mx = 1, 2, abs(a[1][2])
        if mx < 1e-15:
            break
        app, aqq, apq = a[p][p], a[q][q], a[p][q]
        theta = 0.5 * math.atan2(2 * apq, aqq - app)
        c, s = math.cos(theta), math.sin(theta)
        for k in range(3):
            akp, akq = a[k][p], a[k][q]
            a[k][p] = c * akp - s * akq
            a[k][q] = s * akp + c * akq
        for k in range(3):
            apk, aqk = a[p][k], a[q][k]
            a[p][k] = c * apk - s * aqk
            a[q][k] = s * apk + c * aqk
        for k in range(3):
            vkp, vkq = v[k][p], v[k][q]
            v[k][p] = c * vkp - s * vkq
            v[k][q] = s * vkp + c * vkq
    evals = [a[0][0], a[1][1], a[2][2]]
    evecs = [[v[i][j] for i in range(3)] for j in range(3)]  # rows = vectors
    return evals, evecs


def solve3(A, b):
    d = (A[0][0] * (A[1][1] * A[2][2] - A[1][2] * A[2][1])
         - A[0][1] * (A[1][0] * A[2][2] - A[1][2] * A[2][0])
         + A[0][2] * (A[1][0] * A[2][1] - A[1][1] * A[2][0]))
    if abs(d) < 1e-18:
        return None
    def rep(A, k, b):
        M = [row[:] for row in A]
        for i in range(3):
            M[i][k] = b[i]
        return (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1])
                - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
                + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))
    return tuple(rep(A, k, b) / d for k in range(3))


def covariance(points, center):
    C = [[0.0] * 3 for _ in range(3)]
    for p in points:
        d = sub(p, center)
        for i in range(3):
            for j in range(3):
                C[i][j] += d[i] * d[j]
    return C


def centroid(points):
    n = len(points)
    return tuple(sum(p[k] for p in points) / n for k in range(3))


def orthobasis(w):
    """Orthonormal basis (e1, e2, w) with given unit third axis."""
    a = (1.0, 0.0, 0.0) if abs(w[0]) < 0.9 else (0.0, 1.0, 0.0)
    e1 = unit(cross(a, w))
    e2 = cross(w, e1)
    return e1, e2, w


# --------------------------------------------------------- frame adaptation

def adapt_frame(geo, g, corners, kind):
    """Move coordinates into a frame where the involution's best-fit symmetry
    element is canonical: C2 -> rotation pi about z; mirror -> z=0 plane."""
    pairs = [(c, g[c]) for c in corners if c < g[c]]
    fixed = [c for c in corners if g[c] == c]
    mids = [centroid([geo[a], geo[b]]) for a, b in pairs]

    if kind == "C2":
        # midpoints of swapped pairs lie on the axis
        p0 = centroid(mids)
        C = covariance(mids, p0)
        evals, evecs = jacobi3(C)
        axis = unit(evecs[max(range(3), key=lambda i: evals[i])])
        e1, e2, e3 = orthobasis(axis)
    else:
        # midpoints + fixed corners lie on the mirror plane
        pts = mids + [geo[c] for c in fixed]
        p0 = centroid(pts)
        C = covariance(pts, p0)
        evals, evecs = jacobi3(C)
        normal = unit(evecs[min(range(3), key=lambda i: evals[i])])
        e1, e2, e3 = orthobasis(normal)

    def to_frame(p):
        d = sub(p, p0)
        return (dot(d, e1), dot(d, e2), dot(d, e3))

    return {v: to_frame(p) for v, p in geo.items()}


def sym_image(p, kind):
    if kind == "C2":
        return (-p[0], -p[1], p[2])
    return (p[0], p[1], -p[2])


# --------------------------------------------------------- optimizer

def build_constraint_data(cells, uf, paths):
    # unique faces
    seen = {}
    for piece, flist in cells.items():
        for f in flist:
            seen.setdefault(frozenset(f), list(f))
    faces = list(seen.values())

    # parallel classes over all primitive edges (>= 2 members)
    all_edges = set()
    for f in faces:
        m = len(f)
        for i in range(m):
            all_edges.add(edge(f[i], f[(i + 1) % m]))
    classes = [C for C in uf.classes(sorted(all_edges)) if len(C) >= 2]
    return faces, classes


def facet_groups_faces(cells):
    """9 shell facet groups as lists of (ordered) boundary faces."""
    geo = json.load(open("convex_product_coords.json"))
    count = defaultdict(list)
    order = {}
    for piece, flist in cells.items():
        for f in flist:
            key = frozenset(f)
            count[key].append(piece)
            order[key] = f
    bfaces = [order[k] for k, v in count.items() if len(v) == 1]
    bedge_faces = defaultdict(list)
    for f in bfaces:
        m = len(f)
        for i in range(m):
            bedge_faces[edge(f[i], f[(i + 1) % m])].append(frozenset(f))
    normals = {frozenset(f): newell([tuple(geo[v]) for v in f]) for f in bfaces}
    fuf = UF()
    for e, (f1, f2) in bedge_faces.items():
        if abs(dot(normals[f1], normals[f2])) > math.cos(math.radians(2.0)):
            fuf.union(f1, f2)
    groups = defaultdict(list)
    for f in bfaces:
        groups[fuf.find(frozenset(f))].append(f)
    return list(groups.values())


def plane_of(face, pos):
    pts = [pos[v] for v in face]
    return centroid(pts), newell(pts)


def class_direction(C, pos):
    ref = None
    acc = [0.0, 0.0, 0.0]
    for a, b in C:
        d = unit(sub(pos[b], pos[a]))
        if ref is None:
            ref = d
        if dot(d, ref) < 0:
            d = (-d[0], -d[1], -d[2])
        for k in range(3):
            acc[k] += d[k]
    return unit(tuple(acc))


def project_symmetry(pos, g, corners, kind):
    """Hard-project outer corners onto the exact symmetric configuration."""
    done = set()
    for c in corners:
        if c in done:
            continue
        gc = g[c]
        if gc == c:
            m = pos[c]
            sm = sym_image(m, kind)
            pos[c] = tuple((m[k] + sm[k]) / 2 for k in range(3))
            done.add(c)
        else:
            m = tuple((pos[c][k] + sym_image(pos[gc], kind)[k]) / 2
                      for k in range(3))
            pos[c] = m
            pos[gc] = sym_image(m, kind)
            done.update((c, gc))


def optimize(pos0, faces, classes, fgroups, g, corners, kind,
             iters=800, polish=0, w_face=1.0, w_par=2.0, verbose=True):
    pos = dict(pos0)
    init = dict(pos0)
    vlist = sorted(pos)
    vfaces = defaultdict(list)
    for fi, f in enumerate(faces):
        for v in f:
            vfaces[v].append(fi)
    vedges = defaultdict(list)   # v -> (other, class_idx)
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
    gpair = dict(g)

    total = iters + polish
    for it in range(total):
        t = min(1.0, it / max(1, iters - 1))
        w_facet = 3.0 + 9.0 * t
        w_sym = 0.5 + 29.5 * t
        lam = 0.05
        lam0 = 0.01 * (1.0 - t)  # release the initial anchor during polish

        planes = [plane_of(f, pos) for f in faces]
        dirs = [class_direction(C, pos) for C in classes]
        gplanes = []
        for grp in fgroups:
            ns = []
            cs = []
            ref = None
            for f in grp:
                c0, n0 = plane_of(f, pos)
                if ref is None:
                    ref = n0
                if dot(n0, ref) < 0:
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
                add_plane(planes[fi][0], planes[fi][1], w_face)
            for gi in vgroups[v]:
                add_plane(gplanes[gi][0], gplanes[gi][1], w_facet)
            for (u, ci) in vedges[v]:
                d = dirs[ci]
                # (I - d d^T)(v - u) = 0
                P = [[(1.0 if i == j else 0.0) - d[i] * d[j]
                      for j in range(3)] for i in range(3)]
                pu = pos[u]
                for i in range(3):
                    for j in range(3):
                        A[i][j] += w_par * P[i][j]
                    b[i] += w_par * sum(P[i][j] * pu[j] for j in range(3))
            if v in gpair:
                add_point(sym_image(pos[gpair[v]], kind), w_sym)
            add_point(pos[v], lam)
            add_point(init[v], lam0)

            s = solve3(A, b)
            newpos[v] = s if s is not None else pos[v]
        pos = newpos
        project_symmetry(pos, gpair, corners, kind)

        if verbose and (it % 200 == 0 or it == total - 1):
            worst_plan = 0.0
            for f in faces:
                c0, n = plane_of(f, pos)
                for v in f:
                    worst_plan = max(worst_plan,
                                     abs(dot(sub(pos[v], c0), n)))
            worst_ang = 0.0
            for C in classes:
                d0 = class_direction(C, pos)
                for a, b_ in C:
                    d = unit(sub(pos[b_], pos[a]))
                    worst_ang = max(worst_ang, math.degrees(
                        math.acos(min(1.0, abs(dot(d, d0))))))
            print(f"  it {it:4d}  w_sym={w_sym:6.1f}  planar={worst_plan:.2e}"
                  f"  parallel={worst_ang:.4f}deg")
    return pos


# --------------------------------------------------------- verification

def span_of(pos):
    vs = list(pos.values())
    lo = [min(p[k] for p in vs) for k in range(3)]
    hi = [max(p[k] for p in vs) for k in range(3)]
    return max(hi[k] - lo[k] for k in range(3))


def report(pos, cells, faces, classes, fgroups, g, corners, kind, kinds):
    S = span_of(pos)
    print(f"\n=== verification (span {S:.3f}) ===")

    # 1. face planarity
    worst = 0.0
    for f in faces:
        c0, n = plane_of(f, pos)
        for v in f:
            worst = max(worst, abs(dot(sub(pos[v], c0), n)))
    print(f"face planarity: max dev {worst:.2e} ({worst / S:.2e} of span)")

    # 2. parallelism within classes
    worst_ang = 0.0
    for C in classes:
        d0 = class_direction(C, pos)
        for a, b in C:
            d = unit(sub(pos[b], pos[a]))
            ang = math.degrees(math.acos(min(1.0, abs(dot(d, d0)))))
            worst_ang = max(worst_ang, ang)
    print(f"metric products: max parallel deviation {worst_ang:.4f} deg")

    # 3. cell convexity + closedness
    nconvex = 0
    for piece, flist in cells.items():
        cvs = set()
        for f in flist:
            cvs.update(f)
        cc = centroid([pos[v] for v in cvs])
        ok = True
        depth = 0.0
        for f in flist:
            c0, n = plane_of(f, pos)
            if dot(sub(cc, c0), n) > 0:
                n = (-n[0], -n[1], -n[2])
            for v in cvs:
                d = dot(sub(pos[v], c0), n)
                depth = max(depth, d)
                if d > 1e-4 * S:
                    ok = False
        ecount = defaultdict(int)
        for f in flist:
            m = len(f)
            for i in range(m):
                ecount[edge(f[i], f[(i + 1) % m])] += 1
        closed = all(c == 2 for c in ecount.values())
        nconvex += ok
        if not (ok and closed):
            print(f"  cell {piece}: convex={ok} closed={closed} "
                  f"violation depth {depth:.2e} ({depth / S:.2e} of span)")
    print(f"cells convex: {nconvex}/{len(cells)}")

    # 4. outer shell: facet planarity + global convexity over boundary verts
    bverts = set()
    for grp in fgroups:
        for f in grp:
            bverts.update(f)
    inner = centroid([pos[v] for v in bverts])
    worst_flat, worst_poke = 0.0, 0.0
    for grp in fgroups:
        pts = []
        for f in grp:
            pts += [pos[v] for v in f]
        c0 = centroid(pts)
        C = covariance(pts, c0)
        evals, evecs = jacobi3(C)
        n = unit(evecs[min(range(3), key=lambda i: evals[i])])
        if dot(sub(inner, c0), n) > 0:
            n = (-n[0], -n[1], -n[2])
        for p in pts:
            worst_flat = max(worst_flat, abs(dot(sub(p, c0), n)))
        for v in bverts:
            worst_poke = max(worst_poke, dot(sub(pos[v], c0), n))
    print(f"outer shell: facet flatness {worst_flat:.2e}, "
          f"max poke-out {worst_poke:.2e} ({worst_poke / S:.2e} of span)")

    # 5. symmetry of the outer corners
    err = max(norm(sub(sym_image(pos[g[c]], kind), pos[c])) for c in corners)
    print(f"outer symmetry ({kind}): max corner error {err:.2e} "
          f"({err / S:.2e} of span)")

    # 6. product-cell length check (parallelogram opposite sides)
    worst_len = 0.0
    for piece, flist in cells.items():
        if kinds[piece] == "K5":
            continue
        for f in flist:
            if len(f) != 4:
                continue
            a, b_, c, d = f
            l1 = norm(sub(pos[b_], pos[a]))
            l2 = norm(sub(pos[c], pos[d]))
            l3 = norm(sub(pos[d], pos[a]))
            l4 = norm(sub(pos[c], pos[b_]))
            worst_len = max(worst_len,
                            abs(l1 - l2) / max(l1, l2),
                            abs(l3 - l4) / max(l3, l4))
    print(f"parallelogram opposite-side length mismatch: {worst_len:.2e}")

    return dict(face_planarity=worst / S, parallel_deg=worst_ang,
                convex=nconvex, facet_flat=worst_flat / S,
                poke=worst_poke / S, sym=err / S, len_mismatch=worst_len)


# --------------------------------------------------------- main

def main():
    inv_idx = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    iters = int(sys.argv[2]) if len(sys.argv) > 2 else 800

    coords, faces_raw, cells = load_complex()
    uf, kinds = forced_parallel_uf(cells)
    fgroups9, corners, paths = boundary_structure(
        cells, "convex_product_coords.json")
    for path in paths:
        for i in range(len(path) - 2):
            uf.union(edge(path[i], path[i + 1]), edge(path[i + 1], path[i + 2]))

    edges21 = [tuple(sorted((p[0], p[-1]))) for p in paths]
    autos = graph_automorphisms(corners, edges21)
    ident = {v: v for v in corners}
    invs = [g for g in autos if g != ident and perm_order(g, corners) == 2]
    g = invs[inv_idx]
    fixed = sorted(v for v in corners if g[v] == v)
    kind = "C2" if len(fixed) <= 2 else "mirror"
    print(f"involution #{inv_idx}: kind={kind}, fixed corners={fixed}")

    geo = {v: tuple(p) for v, p in
           json.load(open("convex_product_coords.json")).items()}
    pos0 = adapt_frame(geo, g, corners, kind)
    err0 = max(norm(sub(sym_image(pos0[g[c]], kind), pos0[c]))
               for c in corners)
    print(f"initial corner symmetry error after alignment: {err0:.4f} "
          f"(span {span_of(pos0):.3f})")

    faces, classes = build_constraint_data(cells, uf, paths)
    fgroups = facet_groups_faces(cells)
    print(f"{len(faces)} faces, {len(classes)} parallel classes, "
          f"{len(fgroups)} shell facets")

    polish = int(sys.argv[3]) if len(sys.argv) > 3 else 2400
    pos = optimize(pos0, faces, classes, fgroups, g, corners, kind,
                   iters=iters, polish=polish)
    stats = report(pos, cells, faces, classes, fgroups, g, corners, kind,
                   kinds)

    out = f"symmetric_metric_inv{inv_idx}_coords.json"
    json.dump({v: list(p) for v, p in pos.items()}, open(out, "w"), indent=1)
    print(f"\nwrote {out}")
    return stats


if __name__ == "__main__":
    main()
