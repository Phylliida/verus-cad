#!/usr/bin/env python3
"""
Five polytopes for Hugh Thomas (the T of Hohlweg-Lange-Thomas), exported as
watertight binary STL files.

Associahedron K5 (four affinely distinct realizations)
------------------------------------------------------
secondary_hexagon : secondary polytope (GKZ) of the REGULAR hexagon.
                    Carries the full dihedral symmetry (order 12).
cfz_typeA3        : Chapoton-Fomin-Zelevinsky, type A_3.  Facet normals are
                    the almost positive roots; the script certifies that the
                    normal fan is the cluster fan.
hohlweg_lange     : a c-associahedron for a non-linear Coxeter element,
                    obtained by deleting 5 facets of the S_4 permutahedron.
                    Found by exhaustive search over all C(14,9)=2002 facet
                    subsets, then filtered up to congruence so it is NOT
                    congruent to Loday's.
loday_reference   : Loday's realization, cross-checked against the classical
                    x_i = a_i * b_i formula (included as a sanity anchor).

Cyclohedron W3 (type B_3 generalized associahedron)
---------------------------------------------------
cyclohedron_W3    : Reiner's equivariant fiber polytope = convex hull of the
                    GKZ area-vectors of the 20 centrally symmetric
                    triangulations of the regular octagon.

Verification
------------
Associahedra: 14 vertices, 9 facets, 21 edges, simple; 3 quadrilaterals +
6 pentagons; quads pairwise non-adjacent; each pentagon touches exactly 2
quads; pentagon graph = triangular prism.

Cyclohedron: 20 vertices, 12 facets, 30 edges, simple; 4 squares +
4 pentagons + 4 hexagons; squares pairwise non-adjacent; pentagons pairwise
non-adjacent; hexagons pairwise adjacent in a perfect matching; each hexagon
adjacent to 2 squares and 3 pentagons; each square to 2 pentagons and 2
hexagons; each pentagon to 2 squares and 3 hexagons.

Requires: numpy, scipy.   Run:  python associahedra_stl.py
"""

import itertools
import struct

import numpy as np
from scipy.spatial import ConvexHull

TARGET_SIZE_MM = 60.0   # longest bounding-box side of each printed model


# ----------------------------------------------------------------- utilities

def polygon_triangulations(verts):
    """All triangulations of a convex polygon (vertex labels in cyclic order),
    each returned as a list of triangles."""
    if len(verts) < 3:
        return [[]]
    out = []
    for j in range(1, len(verts) - 1):
        for L in polygon_triangulations(verts[:j + 1]):
            for R in polygon_triangulations(verts[j:]):
                out.append(L + R + [(verts[0], verts[j], verts[-1])])
    return out


def facet_data(points):
    """Convex hull with coplanar triangles merged into genuine facets."""
    P = np.asarray(points, dtype=float)
    P = (P - P.mean(axis=0)) / np.abs(P - P.mean(axis=0)).max()
    hull = ConvexHull(P)
    reps, groups = [], []
    for simplex, eq in zip(hull.simplices, hull.equations):
        for r, g in zip(reps, groups):
            if np.allclose(eq, r, atol=1e-6):
                g.update(simplex)
                break
        else:
            reps.append(eq)
            groups.append(set(simplex))
    return hull, [frozenset(g) for g in groups]


def verify_associahedron(points, name="polytope"):
    P = np.asarray(points, dtype=float)
    assert P.shape[0] == 14, f"{name}: expected 14 points, got {P.shape[0]}"
    hull, facets = facet_data(P)
    assert len(hull.vertices) == 14, f"{name}: not all points are vertices"
    assert len(facets) == 9, f"{name}: {len(facets)} facets, expected 9"
    sizes = sorted(len(f) for f in facets)
    assert sizes == [4, 4, 4, 5, 5, 5, 5, 5, 5], f"{name}: facet sizes {sizes}"
    for v in range(14):
        assert sum(v in f for f in facets) == 3, f"{name}: not simple"

    def adjacent(i, j):
        return len(facets[i] & facets[j]) == 2

    quads = [i for i in range(9) if len(facets[i]) == 4]
    pents = [i for i in range(9) if len(facets[i]) == 5]
    for i, j in itertools.combinations(quads, 2):
        assert not adjacent(i, j), f"{name}: adjacent quadrilaterals"
    for p in pents:
        assert sum(adjacent(p, q) for q in quads) == 2, \
            f"{name}: pentagon/quad adjacency wrong"
    nbrs = {p: {q for q in pents if q != p and adjacent(p, q)} for p in pents}
    assert all(len(s) == 3 for s in nbrs.values()), f"{name}: pentagon graph"
    tri = sum(1 for a, b, c in itertools.combinations(pents, 3)
              if b in nbrs[a] and c in nbrs[a] and c in nbrs[b])
    assert tri == 2, f"{name}: pentagon graph is not the triangular prism"
    return facets


def verify_cyclohedron(points, name="cyclohedron"):
    P = np.asarray(points, dtype=float)
    assert P.shape[0] == 20, f"{name}: expected 20 points, got {P.shape[0]}"
    hull, facets = facet_data(P)
    assert len(hull.vertices) == 20, f"{name}: not all points are vertices"
    assert len(facets) == 12, f"{name}: {len(facets)} facets, expected 12"
    sizes = sorted(len(f) for f in facets)
    assert sizes == [4] * 4 + [5] * 4 + [6] * 4, f"{name}: facet sizes {sizes}"
    for v in range(20):
        assert sum(v in f for f in facets) == 3, f"{name}: not simple"

    def adjacent(i, j):
        return len(facets[i] & facets[j]) == 2

    quads = [i for i in range(12) if len(facets[i]) == 4]
    pents = [i for i in range(12) if len(facets[i]) == 5]
    hexes = [i for i in range(12) if len(facets[i]) == 6]
    for i, j in itertools.combinations(quads, 2):
        assert not adjacent(i, j), f"{name}: adjacent squares"
    for i, j in itertools.combinations(pents, 2):
        assert not adjacent(i, j), f"{name}: adjacent pentagons"
    for h in hexes:
        assert sum(adjacent(h, h2) for h2 in hexes if h2 != h) == 1, \
            f"{name}: hexagon matching wrong"
        assert sum(adjacent(h, q) for q in quads) == 2, \
            f"{name}: hexagon/square adjacency wrong"
        assert sum(adjacent(h, p) for p in pents) == 3, \
            f"{name}: hexagon/pentagon adjacency wrong"
    for q in quads:
        assert sum(adjacent(q, p) for p in pents) == 2, \
            f"{name}: square/pentagon adjacency wrong"
        assert sum(adjacent(q, h) for h in hexes) == 2, \
            f"{name}: square/hexagon adjacency wrong"
    for p in pents:
        assert sum(adjacent(p, q) for q in quads) == 2, \
            f"{name}: pentagon/square adjacency wrong"
        assert sum(adjacent(p, h) for h in hexes) == 3, \
            f"{name}: pentagon/hexagon adjacency wrong"
    return facets


def isometry_group_order(points):
    """Order of the group of isometries of R^3 preserving the vertex set
    (= distance-preserving vertex permutations, since the vertices span R^3)."""
    P = np.asarray(points, dtype=float)
    n = len(P)
    D = np.round(np.linalg.norm(P[:, None, :] - P[None, :, :], axis=-1), 6)
    fp = [tuple(sorted(row)) for row in D]
    cand = [[j for j in range(n) if fp[j] == fp[i]] for i in range(n)]
    perm, count = [-1] * n, 0

    def extend(i):
        nonlocal count
        if i == n:
            count += 1
            return
        for j in cand[i]:
            if j in perm[:i]:
                continue
            if all(abs(D[i, k] - D[j, perm[k]]) < 1e-5 for k in range(i)):
                perm[i] = j
                extend(i + 1)
                perm[i] = -1

    extend(0)
    return count


def same_point_set(P, Q, tol=1e-5):
    P, Q = np.asarray(P), np.asarray(Q)
    if len(P) != len(Q):
        return False
    used = [False] * len(Q)
    for p in P:
        hit = next((k for k in range(len(Q))
                    if not used[k] and np.linalg.norm(p - Q[k]) < tol), None)
        if hit is None:
            return False
        used[hit] = True
    return True


def write_stl(points, filename, size=TARGET_SIZE_MM):
    P = np.asarray(points, dtype=float)
    P = P - P.mean(axis=0)
    P *= size / (P.max(axis=0) - P.min(axis=0)).max()
    hull = ConvexHull(P)
    tris = []
    for s in hull.simplices:
        a, b, c = P[s]
        nrm = np.cross(b - a, c - a)
        if np.dot(nrm, a) < 0:            # centroid is at the origin
            b, c = c, b
            nrm = -nrm
        tris.append((nrm / np.linalg.norm(nrm), a, b, c))
    with open(filename, "wb") as fh:
        fh.write(b"\0" * 80)
        fh.write(struct.pack("<I", len(tris)))
        for nrm, a, b, c in tris:
            fh.write(struct.pack("<12f", *nrm, *a, *b, *c))
            fh.write(struct.pack("<H", 0))


# ------------------------------------------- 1. secondary polytope (hexagon)

def secondary_polytope_regular_hexagon():
    N = 6
    ang = 2 * np.pi * np.arange(N) / N
    P2 = np.stack([np.cos(ang), np.sin(ang)], axis=1)
    tris = polygon_triangulations(list(range(N)))
    assert len(tris) == 14                       # Catalan number C_4
    gkz = np.zeros((14, N))
    for t, T in enumerate(tris):
        for a, b, c in T:
            area = 0.5 * abs(np.cross(P2[b] - P2[a], P2[c] - P2[a]))
            gkz[t, [a, b, c]] += area
    centered = gkz - gkz.mean(axis=0)
    _, S, Vt = np.linalg.svd(centered, full_matrices=False)
    assert S[3] < 1e-9 * S[0], "GKZ vectors should span a 3-dim affine space"
    return centered @ Vt[:3].T                   # isometric copy in R^3


# --------------------------------------------------- 2. CFZ, type A_3

def cfz_associahedron():
    """Facet normals = almost positive roots of A_3 (hexagon diagonals via the
    snake); support function tau-invariant: z=3 on short diagonals, z=4 on
    long ones.  Each vertex is built from its triangulation and every other
    inequality is checked STRICTLY, certifying normal fan = cluster fan."""
    hexagon = list(range(1, 7))

    def is_edge(i, j):
        return j - i == 1 or (i, j) == (1, 6)

    diagonals = [d for d in itertools.combinations(hexagon, 2)
                 if not is_edge(*d)]
    assert len(diagonals) == 9
    snake = [(2, 6), (3, 6), (3, 5)]             # -> -alpha_1, -alpha_2, -alpha_3

    def crosses(d, e):
        a, b = d
        c, f = e
        if len({a, b, c, f}) < 4:
            return False
        return (a < c < b) != (a < f < b)

    root, z = {}, {}
    for d in diagonals:
        if d in snake:
            v = np.zeros(3)
            v[snake.index(d)] = -1.0
        else:                                    # positive root: sum of alpha_i
            v = np.array([1.0 if crosses(d, s) else 0.0 for s in snake])
        root[d] = v
        z[d] = float(sum(crosses(d, e) for e in diagonals))   # 3 or 4

    edges = {tuple(sorted(e)) for e in zip(hexagon, hexagon[1:] + hexagon[:1])}
    verts = []
    for T in polygon_triangulations(hexagon):
        diags = sorted({tuple(sorted(e)) for tri in T
                        for e in itertools.combinations(tri, 2)} - edges)
        assert len(diags) == 3
        A = np.array([root[d] for d in diags])
        x = np.linalg.solve(A, np.array([z[d] for d in diags]))
        for d in diagonals:
            if d not in diags:
                assert root[d] @ x < z[d] - 1e-9, "cluster-fan wall violated"
        verts.append(x)
    V = np.array(verts)
    assert len(np.unique(np.round(V, 6), axis=0)) == 14
    return V


# ------------------- 3./4. removahedra of the permutahedron (HL and Loday)

def permutahedron_removal_search():
    """Try all C(14,9)=2002 ways of keeping 9 facet inequalities
    sum_{i in S} x_i >= |S|(|S|+1)/2 of the S_4 permutahedron (on sum x = 10)
    and return every choice whose intersection is an associahedron."""
    n = 4
    subsets = [frozenset(c) for k in range(1, n)
               for c in itertools.combinations(range(n), k)]
    assert len(subsets) == 14
    x0 = np.full(n, (n + 1) / 2.0)
    _, _, Vt = np.linalg.svd(np.ones((1, n)))
    B = Vt[1:].T                                  # orthonormal basis of sum=0

    A = np.zeros((14, 3))
    b = np.zeros(14)
    for idx, S in enumerate(subsets):
        chi = np.zeros(n)
        chi[list(S)] = 1.0
        k = len(S)
        A[idx] = chi @ B
        b[idx] = k * (k + 1) / 2.0 - chi @ x0

    triples, pts, slacks = [], [], []
    for t in itertools.combinations(range(14), 3):
        M = A[list(t)]
        if abs(np.linalg.det(M)) < 1e-9:
            continue
        u = np.linalg.solve(M, b[list(t)])
        triples.append(t)
        pts.append(u)
        slacks.append(A @ u - b)
    pts = np.array(pts)
    slacks = np.array(slacks)
    masks = np.array([sum(1 << k for k in t) for t in triples])

    def bounded(idx):
        Af = A[list(idx)]
        for i, j in itertools.combinations(range(len(idx)), 2):
            r = np.cross(Af[i], Af[j])
            nr = np.linalg.norm(r)
            if nr < 1e-9:
                continue
            r = r / nr
            if (Af @ r).min() > -1e-7 or (Af @ -r).min() > -1e-7:
                return False                      # nontrivial recession cone
        return True

    found = []
    for fam in itertools.combinations(range(14), 9):
        fam_mask = sum(1 << k for k in fam)
        ok = ((masks & ~fam_mask) == 0) & (slacks[:, fam].min(axis=1) > -1e-7)
        cand = pts[ok]
        if len(cand) < 14:
            continue
        uniq = np.unique(np.round(cand, 6), axis=0)
        if len(uniq) != 14 or not bounded(fam):
            continue
        try:
            verify_associahedron(uniq, "search candidate")
        except Exception:
            continue
        found.append((fam, uniq))
    return subsets, x0, B, found


def family_canonical(famsets, n=4):
    """Canonical form of a facet family under coordinate permutations and the
    point reflection x -> 5-x (which complements every subset)."""
    full = frozenset(range(n))
    best = None
    for perm in itertools.permutations(range(n)):
        for flip in (False, True):
            imgs = []
            for S in famsets:
                T = frozenset(perm[i] for i in S)
                if flip:
                    T = full - T
                imgs.append(tuple(sorted(T)))
            key = tuple(sorted(imgs))
            if best is None or key < best:
                best = key
    return best


def loday_vertices():
    """Classical Loday coordinates via polygon duality: hexagon 0..5, triangle
    (a, m, c) with middle vertex m contributes x_m = (m-a)(c-m) = a_m * b_m."""
    verts = []
    for T in polygon_triangulations(list(range(6))):
        x = np.zeros(4)
        for tri in T:
            a, m, c = sorted(tri)
            x[m - 1] = (m - a) * (c - m)
        assert x.sum() == 10 and np.all(x > 0)
        verts.append(x)
    return np.array(verts, dtype=float)


# --------------------------- 5. cyclohedron W_3 (equivariant fiber polytope)

def cyclohedron_equivariant_octagon():
    """Reiner's equivariant fiber polytope: convex hull of the GKZ vectors of
    the centrally symmetric triangulations of the regular octagon.  This is
    the maximally symmetric realization of the 3D cyclohedron (type B_3)."""
    N = 8
    ang = 2 * np.pi * np.arange(N) / N
    P2 = np.stack([np.cos(ang), np.sin(ang)], axis=1)
    all_tris = polygon_triangulations(list(range(N)))
    assert len(all_tris) == 132                  # Catalan number C_6

    boundary = {tuple(sorted((i, (i + 1) % N))) for i in range(N)}

    def diag_set(T):
        edges = {tuple(sorted(e)) for tri in T
                 for e in itertools.combinations(tri, 2)}
        return frozenset(edges - boundary)

    def antipode(d):
        return tuple(sorted(((d[0] + 4) % N, (d[1] + 4) % N)))

    sym = []
    for T in all_tris:
        D = diag_set(T)
        if all(antipode(d) in D for d in D):
            assert len(D) == 5
            diameters = [d for d in D if (d[1] - d[0]) % N == 4]
            assert len(diameters) == 1, "symmetric => exactly one diameter"
            sym.append(T)
    assert len(sym) == 20                        # type B_3 Catalan: C(6,3)

    gkz = np.zeros((20, N))
    for t, T in enumerate(sym):
        for a, b, c in T:
            area = 0.5 * abs(np.cross(P2[b] - P2[a], P2[c] - P2[a]))
            gkz[t, [a, b, c]] += area
    # sanity: GKZ vectors of symmetric triangulations are themselves symmetric
    assert np.allclose(gkz[:, :4], gkz[:, 4:]), "phi_i = phi_{i+4} violated"
    centered = gkz - gkz.mean(axis=0)
    _, S, Vt = np.linalg.svd(centered, full_matrices=False)
    assert S[3] < 1e-9 * S[0] < S[2] / 1e-9, \
        "GKZ vectors should span a 3-dim affine space"
    return centered @ Vt[:3].T                   # isometric copy in R^3


# ---------------------------------------------------------------------- main

def main():
    models = {}   # name -> (points, verifier)

    print("building secondary polytope of the regular hexagon ...")
    models["secondary_hexagon"] = (secondary_polytope_regular_hexagon(),
                                   verify_associahedron)

    print("building Chapoton-Fomin-Zelevinsky realization (type A_3) ...")
    models["cfz_typeA3"] = (cfz_associahedron(), verify_associahedron)

    print("searching all 2002 facet removals of the S_4 permutahedron ...")
    subsets, x0, B, found = permutahedron_removal_search()
    print(f"  -> {len(found)} facet families yield an associahedron")

    classes = {}
    for fam, P in found:
        key = family_canonical(frozenset(subsets[k] for k in fam))
        classes.setdefault(key, []).append((fam, P))
    print(f"  -> {len(classes)} classes up to congruences of the permutahedron")

    # Loday = the interval family; cross-check against the a_i*b_i formula
    intervals = frozenset(frozenset(range(i, j + 1))
                          for i in range(4) for j in range(i, 4) if j - i < 3)
    loday_key = family_canonical(intervals)
    assert loday_key in classes, "Loday family not found by the search?!"
    subset_index = {S: k for k, S in enumerate(subsets)}
    interval_fam = tuple(sorted(subset_index[S] for S in intervals))
    fam_dict = {tuple(sorted(f)): P for f, P in found}
    assert interval_fam in fam_dict
    loday_plane = (loday_vertices() - x0) @ B
    assert same_point_set(loday_plane, fam_dict[interval_fam]), \
        "interval removahedron disagrees with Loday's formula?!"
    models["loday_reference"] = (fam_dict[interval_fam], verify_associahedron)

    # Hohlweg-Lange for a non-linear Coxeter element: any family whose class
    # is not Loday's (hence not congruent to Loday's polytope)
    non_loday = [(fam, P) for key, members in classes.items()
                 if key != loday_key for fam, P in members]
    assert non_loday, "no non-Loday removahedron found?!"
    non_loday.sort(key=lambda fp: tuple(sorted(fp[0])))
    fam, P = non_loday[0]
    pretty = sorted((tuple(sorted(i + 1 for i in subsets[k])) for k in fam),
                    key=lambda s: (len(s), s))
    print("  chosen Hohlweg-Lange family: keep sum_{i in S} x_i >= |S|(|S|+1)/2 for S in")
    print("   ", pretty)
    models["hohlweg_lange"] = (P, verify_associahedron)

    print("building cyclohedron W_3 (equivariant secondary polytope, octagon) ...")
    models["cyclohedron_W3"] = (cyclohedron_equivariant_octagon(),
                                verify_cyclohedron)

    print()
    for name, (P, verifier) in models.items():
        verifier(P, name)
        sym = isometry_group_order(P)
        fname = f"polytope_{name}.stl"
        write_stl(P, fname)
        n_v = len(P)
        n_f = 9 if verifier is verify_associahedron else 12
        n_e = n_v + n_f - 2
        print(f"{fname:40s}  f-vector ({n_v},{n_e},{n_f}) verified;  "
              f"isometry group order {sym}")
    print("\nAll checks passed.")


if __name__ == "__main__":
    main()
