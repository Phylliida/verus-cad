#!/usr/bin/env python3
"""Re-examine the 'symmetric outer + metric products is impossible' claim.

The old proof compared the FORCED parallel classes against ONE fixed shape
(the secondary polytope of the regular hexagon). That only rules out that
exact shape. Here we ask the right question: does there exist ANY realization
whose outer K5 has a nontrivial symmetry group and whose 14 cells are genuine
metric products?

Stage 1: recompute forced-parallel classes P on the 21 outer K5 edges
         (union-find: parallelogram constraints from cube/prism quads +
         collinearity along subdivided outer edge paths).
Stage 2: compute Aut(outer K5 skeleton) (expect order 12), and for each
         cyclic subgroup the join P* = join_g g(P). Check necessary
         geometric conditions for each candidate symmetry.

Pure python (numpy is broken in this env).
"""
import json
import math
import sys
from collections import defaultdict

from tex_to_stl import parse_tex


# ---------------------------------------------------------------- utilities

class UF:
    def __init__(self):
        self.p = {}

    def find(self, x):
        p = self.p
        if x not in p:
            p[x] = x
            return x
        while p[x] != x:
            p[x] = p[p[x]]
            x = p[x]
        return x

    def union(self, a, b):
        ra, rb = self.find(a), self.find(b)
        if ra != rb:
            self.p[ra] = rb

    def classes(self, items):
        cl = defaultdict(list)
        for it in items:
            cl[self.find(it)].append(it)
        return list(cl.values())


def edge(a, b):
    return (a, b) if a < b else (b, a)


def sub(p, q):
    return (p[0] - q[0], p[1] - q[1], p[2] - q[2])


def cross(u, v):
    return (u[1] * v[2] - u[2] * v[1],
            u[2] * v[0] - u[0] * v[2],
            u[0] * v[1] - u[1] * v[0])


def norm(v):
    return math.sqrt(v[0] * v[0] + v[1] * v[1] + v[2] * v[2])


def unit(v):
    n = norm(v)
    return (v[0] / n, v[1] / n, v[2] / n)


def dot(u, v):
    return u[0] * v[0] + u[1] * v[1] + u[2] * v[2]


def newell(pts):
    n = [0.0, 0.0, 0.0]
    m = len(pts)
    for i in range(m):
        p, q = pts[i], pts[(i + 1) % m]
        n[0] += (p[1] - q[1]) * (p[2] + q[2])
        n[1] += (p[2] - q[2]) * (p[0] + q[0])
        n[2] += (p[0] - q[0]) * (p[1] + q[1])
    return unit(tuple(n))


# ---------------------------------------------------------------- stage 1

def load_complex():
    text = open("figure.tex").read()
    coords, faces = parse_tex(text)
    cells = defaultdict(list)
    for verts, _color, piece in faces:
        cells[piece].append(list(verts))
    return coords, faces, dict(cells)


def forced_parallel_uf(cells):
    """Union-find on primitive edges from metric-product constraints."""
    uf = UF()
    kinds = {}
    for piece, flist in cells.items():
        nf = len(flist)
        kind = {6: "cube", 7: "prism", 9: "K5"}.get(nf)
        if kind is None:
            raise ValueError(f"cell {piece} has {nf} faces")
        kinds[piece] = kind
        if kind == "K5":
            continue  # trivial product: no constraints
        for f in flist:
            if len(f) != 4:
                continue  # prism pentagons: no direct constraint
            a, b, c, d = f
            uf.union(edge(a, b), edge(d, c))
            uf.union(edge(b, c), edge(a, d))
    return uf, kinds


def boundary_structure(cells, coords_json):
    """Find boundary faces, group into K5 facets, corners, and edge paths."""
    geo = json.load(open(coords_json))
    count = defaultdict(list)
    order = {}
    for piece, flist in cells.items():
        for f in flist:
            key = frozenset(f)
            count[key].append(piece)
            order[key] = f
    bfaces = [order[k] for k, v in count.items() if len(v) == 1]
    interior = [order[k] for k, v in count.items() if len(v) == 2]
    weird = {k: v for k, v in count.items() if len(v) > 2}
    assert not weird, f"faces in >2 cells: {weird}"

    # boundary edge -> the (<=2) boundary faces containing it
    bedge_faces = defaultdict(list)
    for f in bfaces:
        m = len(f)
        for i in range(m):
            bedge_faces[edge(f[i], f[(i + 1) % m])].append(frozenset(f))
    for e, fl in bedge_faces.items():
        assert len(fl) == 2, f"boundary edge {e} in {len(fl)} boundary faces"

    # group boundary faces into facets by coplanarity in the verified geometry
    normals = {}
    for f in bfaces:
        pts = [tuple(geo[v]) for v in f]
        normals[frozenset(f)] = newell(pts)
    fuf = UF()
    for e, (f1, f2) in bedge_faces.items():
        if abs(dot(normals[f1], normals[f2])) > math.cos(math.radians(2.0)):
            fuf.union(f1, f2)
    fgroups = fuf.classes([frozenset(f) for f in bfaces])
    group_of = {}
    for gi, g in enumerate(fgroups):
        for f in g:
            group_of[f] = gi

    # skeleton edges: boundary edges between two different facet groups
    skel_edges = [e for e, (f1, f2) in bedge_faces.items()
                  if group_of[f1] != group_of[f2]]
    skel_adj = defaultdict(list)
    for a, b in skel_edges:
        skel_adj[a].append(b)
        skel_adj[b].append(a)
    corners = sorted([v for v, nb in skel_adj.items() if len(nb) >= 3])
    for v, nb in skel_adj.items():
        assert len(nb) in (2, 3), f"skeleton vertex {v} degree {len(nb)}"

    # walk paths corner -> corner through degree-2 subdivision vertices
    paths = []
    seen = set()
    for c in corners:
        for nxt in skel_adj[c]:
            e0 = edge(c, nxt)
            if e0 in seen:
                continue
            path = [c, nxt]
            seen.add(e0)
            while path[-1] not in corners:
                v = path[-1]
                prev = path[-2]
                nbs = [w for w in skel_adj[v] if w != prev]
                assert len(nbs) == 1
                path.append(nbs[0])
                seen.add(edge(v, nbs[0]))
            paths.append(path)
    return fgroups, corners, paths


def stage1():
    coords, faces, cells = load_complex()
    uf, kinds = forced_parallel_uf(cells)
    print("cells:", sorted(kinds.items()))
    kc = defaultdict(int)
    for k in kinds.values():
        kc[k] += 1
    print("cell kinds:", dict(kc))

    fgroups, corners, paths = boundary_structure(cells, "convex_product_coords.json")
    print(f"\nboundary: {len(fgroups)} facet groups, {len(corners)} corners, "
          f"{len(paths)} skeleton paths")
    print("corners:", corners)

    # collinearity along each path
    for path in paths:
        for i in range(len(path) - 2):
            uf.union(edge(path[i], path[i + 1]), edge(path[i + 1], path[i + 2]))

    # forced partition P on the 21 K5 edges (represented by their paths)
    path_key = {}
    for path in paths:
        path_key[(path[0], path[-1]) if path[0] < path[-1]
                 else (path[-1], path[0])] = path
    reps = {}
    for pk, path in path_key.items():
        reps[pk] = uf.find(edge(path[0], path[1]))
    cl = defaultdict(list)
    for pk, r in reps.items():
        cl[r].append(pk)
    P = sorted(cl.values(), key=len)
    print("\nFORCED PARTITION P on the 21 outer K5 edges:")
    print("sizes:", [len(c) for c in P])
    for c in P:
        print("  ", c)
    return coords, cells, kinds, corners, paths, P


# ---------------------------------------------------------------- stage 2

def graph_automorphisms(vertices, edges):
    """All automorphisms of a simple graph, by backtracking."""
    adj = defaultdict(set)
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)
    vs = sorted(vertices)
    # order vertices so each has a previously-placed neighbor where possible
    order = [vs[0]]
    placed = {vs[0]}
    while len(order) < len(vs):
        nxt = None
        for v in vs:
            if v not in placed and adj[v] & placed:
                nxt = v
                break
        if nxt is None:
            nxt = next(v for v in vs if v not in placed)
        order.append(nxt)
        placed.add(nxt)

    autos = []

    def extend(i, mapping, used):
        if i == len(order):
            autos.append(dict(mapping))
            return
        v = order[i]
        mapped_nbs = [mapping[u] for u in adj[v] if u in mapping]
        if mapped_nbs:
            cands = set(adj[mapped_nbs[0]])
            for u in mapped_nbs[1:]:
                cands &= adj[u]
            cands -= used
        else:
            cands = set(vs) - used
        for c in sorted(cands):
            if len(adj[c]) != len(adj[v]):
                continue
            # consistency: previously mapped non-neighbors must stay non-adjacent
            ok = all((u in adj[v]) == (mapping[u] in adj[c])
                     for u in mapping)
            if ok:
                mapping[v] = c
                used.add(c)
                extend(i + 1, mapping, used)
                del mapping[v]
                used.discard(c)

    extend(0, {}, set())
    return autos


def perm_order(g, vs):
    n = 1
    cur = dict(g)
    ident = {v: v for v in vs}
    while cur != ident:
        cur = {v: g[cur[v]] for v in vs}
        n += 1
    return n


def apply_edge(g, e):
    return edge(g[e[0]], g[e[1]])


def join_partition(P, group_elems):
    uf = UF()
    for g in group_elems:
        for C in P:
            base = apply_edge(g, C[0])
            for e in C[1:]:
                uf.union(base, apply_edge(g, e))
    all_edges = [e for C in P for e in C]
    return sorted(uf.classes(all_edges), key=len)


def cyclic(g, vs):
    elems = [{v: v for v in vs}]
    cur = dict(g)
    while cur != elems[0]:
        elems.append(dict(cur))
        cur = {v: g[cur[v]] for v in vs}
    return elems


def matching_violations(P):
    bad = []
    for C in P:
        seen = defaultdict(list)
        for e in C:
            seen[e[0]].append(e)
            seen[e[1]].append(e)
        for v, es in seen.items():
            if len(es) > 1:
                bad.append((v, es))
    return bad


def facet_violations(P, facet_edges):
    """convex polygon: <=2 edges per direction class, and those non-adjacent."""
    bad = []
    cls_of = {}
    for i, C in enumerate(P):
        for e in C:
            cls_of[e] = i
    for fi, fedges in facet_edges.items():
        byc = defaultdict(list)
        for e in fedges:
            byc[cls_of[e]].append(e)
        for ci, es in byc.items():
            if len(es) > 2:
                bad.append((fi, ci, es))
            elif len(es) == 2:
                a, b = es
                if set(a) & set(b):  # adjacent edges parallel -> degenerate
                    bad.append((fi, ci, es))
    return bad


def stage2(corners, paths, P, facet_edges):
    edges21 = [tuple(sorted((p[0], p[-1]))) for p in paths]
    autos = graph_automorphisms(corners, edges21)
    print(f"\n|Aut(K5 skeleton)| = {len(autos)}")
    by_order = defaultdict(list)
    for g in autos:
        by_order[perm_order(g, corners)].append(g)
    print("element orders:", {o: len(gs) for o, gs in sorted(by_order.items())})

    print("\nbaseline check on P itself:")
    print("  matching violations:", matching_violations(P))
    print("  facet violations:", facet_violations(P, facet_edges))

    results = {}
    for o, gs in sorted(by_order.items()):
        if o == 1:
            continue
        for gi, g in enumerate(gs):
            sub_elems = cyclic(g, corners)
            Pstar = join_partition(P, sub_elems)
            sizes = [len(c) for c in Pstar]
            mv = matching_violations(Pstar)
            fv = facet_violations(Pstar, facet_edges)
            # fixed classes under g
            fixed = []
            for C in Pstar:
                img = sorted(apply_edge(g, e) for e in C)
                if img == sorted(C):
                    fixed.append(C)
            fixed_edges = [e for C in fixed for e in C
                           if apply_edge(g, e) == e]
            key = (o, gi)
            results[key] = (g, Pstar, fixed)
            print(f"\n-- element of order {o} (#{gi}): "
                  f"P* sizes {sizes}")
            print(f"   fixed classes: {[len(c) for c in fixed]} "
                  f"(edges fixed individually: {len(fixed_edges)})")
            print(f"   matching violations: {len(mv)}, "
                  f"facet violations: {len(fv)}")
            if o == 3:
                for C in fixed:
                    print(f"   order-3 fixed class size {len(C)} "
                          f"(mod 3 = {len(C) % 3}): {C}")
                nonfixed = [C for C in Pstar if C not in fixed]
                print(f"   non-fixed classes: {[len(c) for c in nonfixed]}")
                if mv or fv:
                    print("   VIOLATIONS:", mv, fv)
    return autos, results


def facet_edge_map(cells, paths):
    """facet group index -> set of K5 edges (paths) on its boundary."""
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
    normals = {}
    for f in bfaces:
        normals[frozenset(f)] = newell([tuple(geo[v]) for v in f])
    fuf = UF()
    for e, (f1, f2) in bedge_faces.items():
        if abs(dot(normals[f1], normals[f2])) > math.cos(math.radians(2.0)):
            fuf.union(f1, f2)
    group_of = {}
    for f in bfaces:
        group_of[frozenset(f)] = fuf.find(frozenset(f))
    fmap = defaultdict(set)
    for path in paths:
        e0 = edge(path[0], path[1])
        f1, f2 = bedge_faces[e0]
        pk = tuple(sorted((path[0], path[-1])))
        fmap[group_of[f1]].add(pk)
        fmap[group_of[f2]].add(pk)
    return {i: sorted(v) for i, (k, v) in enumerate(sorted(
        fmap.items(), key=lambda kv: (len(kv[1]), sorted(kv[1]))))}


def compose(g, h, vs):
    return {v: g[h[v]] for v in vs}


def stage3(corners, paths, P, facet_edges, autos):
    """Detail passing involutions; test V4 (Klein) subgroups."""
    vs = corners
    ident = {v: v for v in vs}
    invs = [g for g in autos if g != ident and perm_order(g, vs) == 2]

    print("\n=== involution details ===")
    passing = []
    for gi, g in enumerate(invs):
        Pstar = join_partition(P, [ident, g])
        mv = matching_violations(Pstar)
        fv = facet_violations(Pstar, facet_edges)
        fixed_c = sorted(v for v in vs if g[v] == v)
        edges21 = [tuple(sorted((p[0], p[-1]))) for p in paths]
        fixed_e = [e for e in edges21 if apply_edge(g, e) == e]
        status = "PASS" if not mv and not fv else "fail"
        print(f"inv #{gi}: {status}  fixed corners={fixed_c} "
              f"fixed edges={fixed_e}")
        if status == "PASS":
            print(f"   P* sizes: {[len(c) for c in Pstar]}")
            for C in Pstar:
                img = sorted(apply_edge(g, e) for e in C)
                tag = "fixed" if img == sorted(C) else "swapped-with-partner"
                print(f"     {tag}: {C}")
            passing.append((gi, g, Pstar))

    print("\n=== V4 subgroups ===")
    n = len(invs)
    for i in range(n):
        for j in range(i + 1, n):
            a, b = invs[i], invs[j]
            ab = compose(a, b, vs)
            ba = compose(b, a, vs)
            if ab != ba or perm_order(ab, vs) != 2:
                continue
            Pstar = join_partition(P, [ident, a, b, ab])
            mv = matching_violations(Pstar)
            fv = facet_violations(Pstar, facet_edges)
            k = next(k for k, g in enumerate(invs) if g == ab)
            status = "PASS" if not mv and not fv else "fail"
            print(f"V4 = <inv#{i}, inv#{j}> (product = inv#{k}): {status}  "
                  f"P* sizes {[len(c) for c in Pstar]}  "
                  f"violations m={len(mv)} f={len(fv)}")
    return passing


# ---------------------------------------------------------------- stage 4

def facet_corner_cycles(cells, paths):
    """The 9 K5 facets as cyclic sequences of corners, consistently oriented."""
    geo = json.load(open("convex_product_coords.json"))
    corners = set()
    for p in paths:
        corners.add(p[0])
        corners.add(p[-1])
    fmap = facet_edge_map(cells, paths)
    cycles = []
    for fi, fedges in fmap.items():
        adj = defaultdict(list)
        for a, b in fedges:
            adj[a].append(b)
            adj[b].append(a)
        start = sorted(adj)[0]
        cyc = [start, sorted(adj[start])[0]]
        while len(cyc) < len(adj):
            nxt = [w for w in adj[cyc[-1]] if w != cyc[-2]]
            cyc.append(nxt[0])
        # orient outward via geometry (consistent global orientation)
        pts = [tuple(geo[v]) for v in cyc]
        n = newell(pts)
        centroid = [sum(geo[v][k] for v in corners) / len(corners)
                    for k in range(3)]
        mid = [sum(p[k] for p in pts) / len(pts) for k in range(3)]
        out = sub(mid, tuple(centroid))
        if dot(n, out) < 0:
            cyc.reverse()
        cycles.append(cyc)
    return cycles


def orientation_behavior(g, cycles):
    """+1 if g preserves the sphere orientation, -1 if it reverses."""
    keyed = {frozenset(c): c for c in cycles}
    votes = set()
    for c in cycles:
        img = [g[v] for v in c]
        tgt = keyed[frozenset(img)]
        # find rotation offset matching img to tgt forward or reversed
        k = len(tgt)
        fwd = any(all(img[(i + s) % k] == tgt[i] for i in range(k))
                  for s in range(k))
        rev = any(all(img[(i + s) % k] == tgt[k - 1 - i] for i in range(k))
                  for s in range(k))
        assert fwd != rev, (c, img, tgt)
        votes.add(+1 if fwd else -1)
    assert len(votes) == 1, votes
    return votes.pop()


def full_complex_extension(cells, corner_inv):
    """Try to extend a corner involution to an automorphism of the whole
    55-vertex cell complex (mapping cells to cells, faces to faces)."""
    all_faces = []
    for piece, flist in cells.items():
        for f in flist:
            all_faces.append(frozenset(f))
    face_set = set(all_faces)
    edges = set()
    verts = set()
    for piece, flist in cells.items():
        for f in flist:
            m = len(f)
            verts.update(f)
            for i in range(m):
                edges.add(edge(f[i], f[(i + 1) % m]))
    adj = defaultdict(set)
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)

    mapping = dict(corner_inv)  # corners already assigned
    # iterative propagation: a vertex is determined if it is the unique
    # common neighbor (outside assigned) completing some mapped face
    # simpler: backtracking over vertices ordered by mapped-neighbor count
    vs = sorted(verts)

    def extend(mapping, used):
        # pick unassigned vertex with most assigned neighbors
        best, bestn = None, -1
        for v in vs:
            if v in mapping:
                continue
            n = sum(1 for u in adj[v] if u in mapping)
            if n > bestn:
                best, bestn = v, n
        if best is None:
            # full assignment: verify faces map to faces
            for f in face_set:
                if frozenset(mapping[v] for v in f) not in face_set:
                    return None
            return dict(mapping)
        v = best
        mapped_nbs = [mapping[u] for u in adj[v] if u in mapping]
        if mapped_nbs:
            cands = set(adj[mapped_nbs[0]])
            for u in mapped_nbs[1:]:
                cands &= adj[u]
            cands -= used
        else:
            cands = set(vs) - used
        for c in sorted(cands):
            if len(adj[c]) != len(adj[v]):
                continue
            ok = all((u in adj[v]) == (mapping[u] in adj[c])
                     for u in mapping if u in adj or True
                     for u in [u] if u in mapping)
            # (adjacency consistency against all assigned)
            ok = all((u in adj[v]) == (mapping[u] in adj[c])
                     for u in mapping)
            if not ok:
                continue
            mapping[v] = c
            used.add(c)
            r = extend(mapping, used)
            if r is not None:
                return r
            del mapping[v]
            used.discard(c)
        return None

    used = set(corner_inv.values())
    return extend(mapping, used)


if __name__ == "__main__":
    coords, cells, kinds, corners, paths, P = stage1()
    fmap = facet_edge_map(cells, paths)
    print("\nfacet sizes:", [len(v) for v in fmap.values()])
    autos, _results = stage2(corners, paths, P, fmap)
    passing = stage3(corners, paths, P, fmap, autos)

    print("\n=== orientation behavior of passing involutions ===")
    cycles = facet_corner_cycles(cells, paths)
    for gi, g, Pstar in passing:
        ob = orientation_behavior(g, cycles)
        kind = ("orientation-PRESERVING (C2 rotation ok)" if ob > 0
                else "orientation-REVERSING (mirror ok)")
        print(f"inv #{gi}: {kind}")

    print("\n=== full 55-vertex complex extension ===")
    for gi, g, Pstar in passing:
        ext = full_complex_extension(cells, g)
        if ext is None:
            print(f"inv #{gi}: does NOT extend to the full dissection")
        else:
            nfix = sum(1 for v in ext if ext[v] == v)
            print(f"inv #{gi}: EXTENDS to whole complex! "
                  f"({nfix} of {len(ext)} vertices fixed)")
