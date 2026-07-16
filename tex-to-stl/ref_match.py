#!/usr/bin/env python3
"""Match the associahedron.fbx reference shape to our corner labels:
find the best combinatorial iso (Horn alignment), and the reference's
isometry group; check compatibility with the C2 involution inv#6."""
import json
import math
from collections import defaultdict

from symmetric_metric_feasibility import (
    edge, sub, dot, cross, norm, unit,
    load_complex, boundary_structure, graph_automorphisms, perm_order)
from symmetric_metric_optimize import centroid, jacobi3


def jacobiN(S, n, sweeps=200):
    a = [row[:] for row in S]
    v = [[1.0 if i == j else 0.0 for j in range(n)] for i in range(n)]
    for _ in range(sweeps):
        p, q, mx = 0, 1, 0.0
        for i in range(n):
            for j in range(i + 1, n):
                if abs(a[i][j]) > mx:
                    p, q, mx = i, j, abs(a[i][j])
        if mx < 1e-14:
            break
        theta = 0.5 * math.atan2(2 * a[p][q], a[q][q] - a[p][p])
        c, s = math.cos(theta), math.sin(theta)
        for k in range(n):
            akp, akq = a[k][p], a[k][q]
            a[k][p] = c * akp - s * akq
            a[k][q] = s * akp + c * akq
        for k in range(n):
            apk, aqk = a[p][k], a[q][k]
            a[p][k] = c * apk - s * aqk
            a[q][k] = s * apk + c * aqk
        for k in range(n):
            vkp, vkq = v[k][p], v[k][q]
            v[k][p] = c * vkp - s * vkq
            v[k][q] = s * vkp + c * vkq
    evals = [a[i][i] for i in range(n)]
    evecs = [[v[i][j] for i in range(n)] for j in range(n)]
    return evals, evecs


def quat_to_R(q):
    w, x, y, z = q
    return [
        [1 - 2 * (y * y + z * z), 2 * (x * y - w * z), 2 * (x * z + w * y)],
        [2 * (x * y + w * z), 1 - 2 * (x * x + z * z), 2 * (y * z - w * x)],
        [2 * (x * z - w * y), 2 * (y * z + w * x), 1 - 2 * (x * x + y * y)],
    ]


def horn_align(P, Q, allow_reflection=True):
    """Best rotation(+optional reflection)+scale+translation P -> Q.
    Returns (rms, transform_fn)."""
    n = len(P)
    cp = centroid(P)
    cq = centroid(Q)
    Pc = [sub(p, cp) for p in P]
    Qc = [sub(q, cq) for q in Q]

    def try_pts(Pc):
        M = [[sum(Pc[k][i] * Qc[k][j] for k in range(n)) for j in range(3)]
             for i in range(3)]
        Sxx, Sxy, Sxz = M[0]
        Syx, Syy, Syz = M[1]
        Szx, Szy, Szz = M[2]
        N = [
            [Sxx + Syy + Szz, Syz - Szy, Szx - Sxz, Sxy - Syx],
            [Syz - Szy, Sxx - Syy - Szz, Sxy + Syx, Szx + Sxz],
            [Szx - Sxz, Sxy + Syx, -Sxx + Syy - Szz, Syz + Szy],
            [Sxy - Syx, Szx + Sxz, Syz + Szy, -Sxx - Syy + Szz],
        ]
        evals, evecs = jacobiN(N, 4)
        q = evecs[max(range(4), key=lambda i: evals[i])]
        L = math.sqrt(sum(c * c for c in q))
        R = quat_to_R([c / L for c in q])

        def rot(p):
            return tuple(sum(R[i][j] * p[j] for j in range(3))
                         for i in range(3))
        num = sum(dot(rot(Pc[k]), Qc[k]) for k in range(n))
        den = sum(dot(Pc[k], Pc[k]) for k in range(n))
        s = num / den
        rms = math.sqrt(sum(norm(sub((s * rot(Pc[k])[0], s * rot(Pc[k])[1],
                                      s * rot(Pc[k])[2]), Qc[k])) ** 2
                            for k in range(n)) / n)
        return rms, R, s

    best = None
    for refl in ([False, True] if allow_reflection else [False]):
        Pin = [(-p[0], p[1], p[2]) for p in Pc] if refl else Pc
        rms, R, s = try_pts(Pin)
        if best is None or rms < best[0]:
            best = (rms, R, s, refl)
    rms, R, s, refl = best

    def transform(p):
        d = sub(p, cp)
        if refl:
            d = (-d[0], d[1], d[2])
        r = tuple(sum(R[i][j] * d[j] for j in range(3)) for i in range(3))
        return (s * r[0] + cq[0], s * r[1] + cq[1], s * r[2] + cq[2])

    return rms, transform, refl


def graph_isos(vertsA, edgesA, vertsB, edgesB):
    adjA = defaultdict(set)
    for a, b in edgesA:
        adjA[a].add(b); adjA[b].add(a)
    adjB = defaultdict(set)
    for a, b in edgesB:
        adjB[a].add(b); adjB[b].add(a)
    isos = []
    order = [vertsA[0]]
    placed = {vertsA[0]}
    while len(order) < len(vertsA):
        nxt = next(v for v in vertsA
                   if v not in placed and adjA[v] & placed)
        order.append(nxt); placed.add(nxt)

    def extend(i, m, used):
        if i == len(order):
            isos.append(dict(m)); return
        v = order[i]
        mapped = [m[u] for u in adjA[v] if u in m]
        cands = set(adjB[mapped[0]]) if mapped else set(vertsB)
        for u in mapped[1:]:
            cands &= adjB[u]
        cands -= used
        for c in cands:
            if all((u in adjA[v]) == (m[u] in adjB[c]) for u in m):
                m[v] = c; used.add(c)
                extend(i + 1, m, used)
                del m[v]; used.discard(c)

    extend(0, {}, set())
    return isos


def main():
    ref = json.load(open("associahedron_ref.json"))
    rverts = [tuple(v) for v in ref["verts"]]
    rpolys = ref["polys"]
    redges = set()
    for p in rpolys:
        m = len(p)
        for i in range(m):
            redges.add(edge(p[i], p[(i + 1) % m]))
    print(f"reference: {len(rverts)} verts, {len(redges)} edges, "
          f"{len(rpolys)} facets")

    _c, _f, cells = load_complex()
    _fg, corners, paths = boundary_structure(
        cells, "convex_product_coords.json")
    edges21 = [tuple(sorted((p[0], p[-1]))) for p in paths]

    isos = graph_isos(corners, edges21, list(range(14)), sorted(redges))
    print(f"combinatorial isos corner-graph -> ref: {len(isos)}")

    pos = {v: tuple(p) for v, p in
           json.load(open("symmetric_metric_inv6_coords.json")).items()}
    span = 2 * 6.407166
    results = []
    for iso in isos:
        P = [pos[c] for c in corners]
        Q = [rverts[iso[c]] for c in corners]
        rms, transform, refl = horn_align(P, Q)
        results.append((rms, iso, transform, refl))
    results.sort(key=lambda r: r[0])
    print("\nHorn RMS of current C2 solution vs ref, per iso (best 5):")
    for rms, iso, _t, refl in results[:5]:
        print(f"  rms {rms:.4f} ({rms/span:.3%} of span)  refl={refl}")

    # reference's own isometry group: which graph autos are isometries?
    autos = graph_automorphisms(list(range(14)), sorted(redges))
    iso_count = 0
    c0 = centroid(rverts)
    types = []
    for g in autos:
        P = [sub(rverts[i], c0) for i in range(14)]
        Q = [sub(rverts[g[i]], c0) for i in range(14)]
        rms, _t, refl = horn_align(
            [tuple(p) for p in P], [tuple(q) for q in Q])
        if rms < 1e-3:
            iso_count += 1
            types.append((perm_order(g, list(range(14))), refl))
    print(f"\nreference isometry group order: {iso_count} "
          f"(graph autos: {len(autos)})")
    print("element (order, is_reflection):",
          sorted(types))

    # is inv#6 an isometry of ref under the best matching?
    ident = {v: v for v in corners}
    cautos = graph_automorphisms(corners, edges21)
    invs = [g for g in cautos if g != ident
            and perm_order(g, corners) == 2]
    g6 = invs[6]
    best_rms, best_iso, _t, _r = results[0]
    perm = {best_iso[c]: best_iso[g6[c]] for c in corners}
    P = [sub(rverts[i], c0) for i in range(14)]
    Q = [sub(rverts[perm[i]], c0) for i in range(14)]
    rms, _t2, refl = horn_align([tuple(p) for p in P],
                                [tuple(q) for q in Q])
    print(f"\ninv#6 as isometry of ref (best iso): rms {rms:.5f} "
          f"refl={refl}")
    json.dump({"iso": results[0][1], "rms": results[0][0]},
              open("ref_best_iso.json", "w"))
    return results


if __name__ == "__main__":
    main()
