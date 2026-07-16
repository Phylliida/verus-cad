#!/usr/bin/env python3
"""Maximize the number of congruent (identical-shape) pieces while keeping
the full structure: 2-Tamari decomposition, convex cells, metric products,
watertight tiling.

Congruence constraints in the sweep optimizer:
- translate pairs: class+orientation-preserving correspondence, pull both
  cells toward pos +- T (T refit per iteration)
- rotated pairs: Horn-fit correspondence per iteration (direct isometry,
  optional mirror)

Usage: python3 congruent_pieces.py <stage> [iters] [start_coords] [out_coords]
  stage 1: 4 translate pairs (cube pair + 3 prism pairs)
  stage 2: stage 1 + K5 pair (rotated/mirror) + leftover prism pair (rotated)
  stage 3: all cubes congruent + prisms in 2 quads + K5 pair  (dream)
"""
import json
import math
import sys
from collections import defaultdict

from symmetric_metric_feasibility import (
    UF, edge, sub, dot, norm, unit,
    load_complex, forced_parallel_uf, boundary_structure)
from symmetric_metric_optimize import (
    centroid, solve3, plane_of, class_direction,
    build_constraint_data, facet_groups_faces, span_of, report)
from cell_congruence import build_structures, cell_edges
from ref_match import horn_align
from tamari2_order import hasse_edges


STAGES = {
    # stage: (translate pairs, rotated pairs)
    1: ([("321-0", "432-111"), ("421-1", "532-211")], []),
    2: ([("321-0", "432-111"), ("421-1", "532-211")],
        [("431-11", "542-221")]),
    3: ([("321-0", "432-111"), ("421-1", "532-211")],
        [("431-11", "542-221"), ("521-3", "632-411")]),
    4: ([("321-0", "432-111"), ("421-1", "532-211")],
        [("431-11", "542-221"), ("521-3", "632-411"),
         ("631-51", "641-43")]),
    5: ([("321-0", "432-111"), ("421-1", "532-211")],
        [("431-11", "542-221"), ("521-3", "632-411"),
         ("631-51", "641-43"), ("531-21", "642-321")]),
}


def cell_iso(cellsA, cellsB, class_id, hasse_dir, require_class=True):
    """Graph isos cell A -> cell B preserving Hasse orientation and
    (optionally) direction classes."""
    esA, esB = cell_edges(cellsA), cell_edges(cellsB)
    vsA = sorted({v for e in esA for v in e})
    vsB = sorted({v for e in esB for v in e})
    adjA, adjB = defaultdict(set), defaultdict(set)
    for a, b in esA:
        adjA[a].add(b); adjA[b].add(a)
    for a, b in esB:
        adjB[a].add(b); adjB[b].add(a)
    ups = set(hasse_dir)

    isos = []
    order = [vsA[0]]
    placed = {vsA[0]}
    while len(order) < len(vsA):
        nxt = next(v for v in vsA if v not in placed and adjA[v] & placed)
        order.append(nxt); placed.add(nxt)

    def ok_edge(a1, a2, b1, b2):
        if require_class and class_id[edge(a1, a2)] != class_id[edge(b1, b2)]:
            return False
        # orientation: (a1->a2) up iff (b1->b2) up
        au = (a1, a2) in ups
        bu = (b1, b2) in ups
        return au == bu

    def extend(i, m, used):
        if i == len(order):
            isos.append(dict(m)); return
        v = order[i]
        mapped = [(u, m[u]) for u in adjA[v] if u in m]
        cands = set(adjB[mapped[0][1]]) if mapped else set(vsB)
        for u, mu in mapped[1:]:
            cands &= adjB[mu]
        cands -= set(m.values())
        for c in cands:
            if len(adjB[c]) != len(adjA[v]):
                continue
            good = all((u in adjA[v]) == (m[u] in adjB[c]) for u in m)
            if good:
                good = all(ok_edge(v, u, c, m[u])
                           for u in adjA[v] if u in m)
            if good:
                m[v] = c
                extend(i + 1, m, used)
                del m[v]
        return

    extend(0, {}, set())
    return isos


def main():
    stage = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    iters = int(sys.argv[2]) if len(sys.argv) > 2 else 2500
    start = sys.argv[3] if len(sys.argv) > 3 else "typical_look_coords.json"
    out = sys.argv[4] if len(sys.argv) > 4 else f"congruent_stage{stage}_coords.json"
    use_c2 = len(sys.argv) > 5 and sys.argv[5] == "c2"
    w_face, w_par, w_facet, w_cong, w_sym = 1.0, 2.0, 12.0, 4.0, 30.0

    cells_all, kinds, class_id, orbit_id = build_structures()
    cells = cells_all
    _c, _f, cells_raw = load_complex()
    uf, _kinds = forced_parallel_uf(cells_raw)
    _fg, corners, paths = boundary_structure(
        cells_raw, "convex_product_coords.json")
    for path in paths:
        for i in range(len(path) - 2):
            uf.union(edge(path[i], path[i + 1]),
                     edge(path[i + 1], path[i + 2]))
    faces, classes = build_constraint_data(cells_raw, uf, paths)
    fgroups = facet_groups_faces(cells_raw)
    hasse_dir = hasse_edges()

    pos = {v: tuple(p) for v, p in json.load(open(start)).items()}

    tpairs, rpairs = STAGES[stage]
    tpairs, rpairs = list(tpairs), list(rpairs)

    g2 = None
    if use_c2:
        from symmetric_metric_feasibility import (graph_automorphisms,
                                                  perm_order)
        edges21 = [tuple(sorted((p[0], p[-1]))) for p in paths]
        autos = graph_automorphisms(corners, edges21)
        ident = {v: v for v in corners}
        invs = [gg for gg in autos if gg != ident
                and perm_order(gg, corners) == 2]
        g2 = invs[6]
        print("C2 mode: inv#6 hard projection active")

    tcorr = []
    for A, B in list(tpairs):
        isos = cell_iso(cells[A], cells[B], class_id, hasse_dir,
                        require_class=True)
        best = None
        for phi in isos:
            offs = [sub(pos[phi[v]], pos[v]) for v in phi]
            m = centroid(offs)
            var = sum(norm(sub(o, m)) ** 2 for o in offs)
            if best is None or var < best[0]:
                best = (var, phi)
        if best is None:
            print(f"translate {A} -> {B}: IMPOSSIBLE (no class+Hasse-"
                  f"preserving iso) -> falling back to rotation")
            rpairs.append((A, B))
            continue
        print(f"translate {A} -> {B}: {len(isos)} isos, "
              f"offset variance {best[0]:.3f}")
        tcorr.append((A, B, best[1]))

    rcorr = []
    for A, B in rpairs:
        # unconstrained graph isos (isometry type decided by the Horn fit)
        isos = cell_iso(cells[A], cells[B],
                        defaultdict(int), set(), require_class=False)
        best = None
        for phi in isos:
            ks = sorted(phi)
            P = [pos[v] for v in ks]
            Q = [pos[phi[v]] for v in ks]
            rms_d, _t, _r = horn_align(P, Q, allow_reflection=False)
            rms_m, _t2, _r2 = horn_align(P, Q, allow_reflection=True)
            if best is None or rms_d < best[0]:
                best = (rms_d, phi, rms_m)
        assert best, f"no graph iso {A}->{B}"
        print(f"rotated {A} -> {B}: {len(isos)} isos, best DIRECT Horn rms "
              f"{best[0]:.3f} (with mirror allowed: {best[2]:.3f})")
        rcorr.append((A, B, best[1]))

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

    R0 = math.sqrt(sum(dot(pos[c], pos[c]) for c in corners) / len(corners))

    def fix_scale(pos):
        R = math.sqrt(sum(dot(pos[c], pos[c]) for c in corners)
                      / len(corners))
        s = R0 / R
        for v in list(pos):
            p = pos[v]
            pos[v] = (s * p[0], s * p[1], s * p[2])

    def congruence_error(pos):
        errs = []
        for A, B, phi in tcorr:
            offs = [sub(pos[phi[v]], pos[v]) for v in phi]
            m = centroid(offs)
            errs.append(max(norm(sub(o, m)) for o in offs))
        for A, B, phi in rcorr:
            ks = sorted(phi)
            P = [pos[v] for v in ks]
            Q = [pos[phi[v]] for v in ks]
            rms, _t, _r = horn_align(P, Q, allow_reflection=False)
            errs.append(rms)
        return errs

    rstate = {}
    lmin = 0.3 if use_c2 else 0.6
    for it in range(iters):
        wc = w_cong * min(1.0, it / 1000)

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

        # congruence targets
        ctargets = defaultdict(list)   # v -> list of target points
        for A, B, phi in tcorr:
            offs = [sub(pos[phi[v]], pos[v]) for v in phi]
            T = centroid(offs)
            for v, w in phi.items():
                ctargets[w].append(tuple(pos[v][k] + T[k] for k in range(3)))
                ctargets[v].append(tuple(pos[w][k] - T[k] for k in range(3)))
        for pi, (A, B, phi) in enumerate(rcorr):
            ks = sorted(phi)
            P = [pos[v] for v in ks]
            Q = [pos[phi[v]] for v in ks]
            _rms, tf, _refl = horn_align(P, Q, allow_reflection=False)
            # smooth the per-pair transform: blend new image with previous
            imgs = [tf(p) for p in P]
            prev = rstate.get(pi)
            if prev is not None:
                imgs = [tuple(0.9 * pr[k] + 0.1 * im[k] for k in range(3))
                        for pr, im in zip(prev, imgs)]
            rstate[pi] = imgs
            for i, v in enumerate(ks):
                img = imgs[i]
                w = phi[v]
                ctargets[w].append(img)
                d = sub(pos[w], img)
                ctargets[v].append(tuple(pos[v][k] + 0.5 * d[k]
                                         for k in range(3)))

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
            for q in ctargets.get(v, ()):
                add_point(q, wc / max(1, len(ctargets[v])))
            for (u, ci) in vedges[v]:
                L = norm(sub(pos[v], pos[u]))
                if 0 < L < lmin:
                    duv = unit(sub(pos[v], pos[u]))
                    add_point(tuple(pos[u][k] + lmin * duv[k]
                                    for k in range(3)), 4.0)
            if g2 is not None and v in g2:
                from symmetric_metric_optimize import sym_image
                add_point(sym_image(pos[g2[v]], "C2"), w_sym)
            add_point(pos[v], 0.05)

            s = solve3(A, b)
            newpos[v] = s if s is not None else pos[v]
        pos = newpos
        if g2 is not None:
            from symmetric_metric_optimize import project_symmetry
            project_symmetry(pos, g2, corners, "C2")
        fix_scale(pos)

        if it % 250 == 0 or it == iters - 1:
            worst_plan = max(abs(dot(sub(pos[v], plane_of(f, pos)[0]),
                                     plane_of(f, pos)[1]))
                             for f in faces for v in f)
            errs = congruence_error(pos)
            print(f"  it {it:4d} planar={worst_plan:.2e} "
                  f"congruence errs={['%.4f' % e for e in errs]}")

    # final: keep congruence on, no decay (it's part of the spec now);
    # extended joint polish already happened; report
    rep_g = g2 if g2 is not None else {c: c for c in corners}
    stats = report(pos, cells_raw, faces, classes, fgroups, rep_g,
                   corners, "C2", kinds)
    errs = congruence_error(pos)
    print(f"\nfinal congruence errors: {['%.5f' % e for e in errs]}")
    json.dump({v: list(p) for v, p in pos.items()}, open(out, "w"),
              indent=1)
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
