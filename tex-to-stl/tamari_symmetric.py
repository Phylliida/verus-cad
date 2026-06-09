#!/usr/bin/env python3
"""Symmetric associahedron + its normal-fan Tamari decomposition.

Instead of Loday's (lopsided) coordinates, use the SECONDARY POLYTOPE of a
regular hexagon: each triangulation T of the hexagon maps to its GKZ vector
phi(T)_i = sum of areas of triangles of T incident to hexagon-vertex i.
Because a regular hexagon is symmetric, the secondary polytope inherits that
symmetry -> the iconic, symmetric associahedron. Vertices are triangulations,
edges are single diagonal flips (= Tamari covers).

Then the same normal-fan decomposition: cell_v = (normal cone at v) ∩ P, giving
14 convex cells whose adjacency is exactly the Tamari Hasse diagram.

Outputs in ./tamari_sym/.
"""
import math
import os
from collections import defaultdict, Counter

import tamari_normal_fan as N   # reuse geometry + decomposition helpers


# --------------------------------------------------------------------------
# triangulations of a hexagon and the secondary (GKZ) polytope
# --------------------------------------------------------------------------
def triangulations(poly):
    """All triangulations of the convex polygon with vertex-index list `poly`."""
    if len(poly) < 3:
        return [[]]
    if len(poly) == 3:
        return [[tuple(poly)]]
    out = []
    for k in range(1, len(poly) - 1):
        tri = (poly[0], poly[k], poly[-1])
        for L in triangulations(poly[:k + 1]):
            for R in triangulations(poly[k:]):
                out.append(L + [tri] + R)
    return out

def tri_area(p, t):
    a, b, c = p[t[0]], p[t[1]], p[t[2]]
    return abs((b[0]-a[0])*(c[1]-a[1]) - (b[1]-a[1])*(c[0]-a[0])) / 2.0

def diagonals(T, m):
    """Internal diagonals of triangulation T of an m-gon (as a frozenset)."""
    boundary = {frozenset((i, (i+1) % m)) for i in range(m)}
    diag = set()
    for (a, b, c) in T:
        for e in (frozenset((a, b)), frozenset((b, c)), frozenset((a, c))):
            if e not in boundary:
                diag.add(e)
    return frozenset(diag)

def project_to_3d(pts):
    """Isometrically project points (in R^d, affinely 3-dimensional) to R^3."""
    d = len(pts[0]); n = len(pts)
    mean = [sum(p[i] for p in pts)/n for i in range(d)]
    D = [[p[i]-mean[i] for i in range(d)] for p in pts]
    basis = []
    for vec in D:
        v = vec[:]
        for b in basis:
            c = sum(v[i]*b[i] for i in range(d))
            v = [v[i]-c*b[i] for i in range(d)]
        nv = math.sqrt(sum(x*x for x in v))
        if nv > 1e-7:
            basis.append([x/nv for x in v])
        if len(basis) == 3:
            break
    return [tuple(sum(D[k][i]*basis[b][i] for i in range(d)) for b in range(3))
            for k in range(n)]

def symmetric_associahedron():
    m = 6
    hexagon = [(math.cos(math.pi*k/3), math.sin(math.pi*k/3)) for k in range(m)]
    Ts = triangulations(list(range(m)))
    gkz = []
    labels = []
    for T in Ts:
        phi = [0.0]*m
        for t in T:
            A = tri_area(hexagon, t)
            for i in t:
                phi[i] += A
        gkz.append(tuple(phi))
        dg = sorted("".join(str(x) for x in sorted(e)) for e in diagonals(T, m))
        labels.append("{" + ",".join(dg) + "}")
    V = project_to_3d(gkz)
    # diagonal sets, for the flip-adjacency check
    diagsets = [diagonals(T, m) for T in Ts]
    return V, labels, diagsets


# --------------------------------------------------------------------------
# build
# --------------------------------------------------------------------------
def main():
    out = "tamari_sym"
    os.makedirs(out, exist_ok=True)
    V, labels, diagsets = symmetric_associahedron()

    planes, faces = N.hull_facets(V)
    edges = N.polytope_edges(V, faces)
    print(f"associahedron (secondary polytope of regular hexagon):")
    print(f"  {len(V)} vertices, {len(edges)} edges, {len(faces)} facets, "
          f"facet sizes {sorted(len(f) for f in faces)}")

    contains = all(all(N.dot(V[v], V[v]) >= N.dot(V[w], V[v]) - 1e-9
                       for w in range(len(V))) for v in range(len(V)))
    print(f"  every cell contains its own vertex: {contains}")

    cells = [N.vertices_of(N.cell_halfspaces(v, V, planes)) for v in range(len(V))]

    # adjacency
    adj = defaultdict(set)
    for v in range(len(V)):
        for w in range(len(V)):
            if w == v:
                continue
            poly = N.face_polygon(cells[v], N.sub(V[w], V[v]), 0.0)
            if poly and len(poly) >= 3:
                adj[v].add(w)
    adj_edges = {frozenset((v, w)) for v in adj for w in adj[v]}
    degs = sorted(len(adj[v]) for v in range(len(V)))
    print(f"  cell adjacencies: {len(adj_edges)}, degree seq {degs}")
    print(f"  adjacency == associahedron edges: {adj_edges == edges}")

    # adjacency == single diagonal flips (Tamari covers)?
    flip_edges = set()
    for i in range(len(V)):
        for j in range(i+1, len(V)):
            if len(diagsets[i] ^ diagsets[j]) == 2:   # differ by one diagonal
                flip_edges.add(frozenset((i, j)))
    print(f"  flip (Tamari cover) graph edges: {len(flip_edges)}")
    print(f"  cell-adjacency == Tamari flip graph: {adj_edges == flip_edges}")

    # write STLs + checks
    def edge_counts(tris):
        ec = defaultdict(int); rk = lambda p: tuple(round(c, 6) for c in p)
        for a, b, c in tris:
            for u, w in ((a, b), (b, c), (c, a)):
                ec[frozenset((rk(u), rk(w)))] += 1
        return ec

    def cell_volume(tris):
        r = tuple(sum(p[i] for t in tris for p in t)/(3*len(tris)) for i in range(3))
        s = 0.0
        for a, b, c in tris:
            A = [a[i]-r[i] for i in range(3)]; B = [b[i]-r[i] for i in range(3)]
            C = [c[i]-r[i] for i in range(3)]
            s += abs(A[0]*(B[1]*C[2]-B[2]*C[1]) - A[1]*(B[0]*C[2]-B[2]*C[0])
                     + A[2]*(B[0]*C[1]-B[1]*C[0]))/6
        return s

    assembly = []; all_closed = True; total = 0.0
    for v in range(len(V)):
        verts = cells[v]
        ref = tuple(sum(p[i] for p in verts)/len(verts) for i in range(3))
        tris = []
        for (n, b) in N.cell_halfspaces(v, V, planes):
            poly = N.face_polygon(verts, n, b)
            if poly:
                tris.extend(N.fan(poly))
        N.write_stl(f"{out}/cell_{v:02d}.stl", tris, ref)
        assembly.extend(tris); total += cell_volume(tris)
        if any(c % 2 for c in edge_counts(tris).values()):
            all_closed = False

    shell = []
    for f in faces:
        shell.extend(N.fan(N.face_polygon(V, *N.plane_of_face(V, f))))
    N.write_stl(f"{out}/shell.stl", shell, ref=(0.0, 0.0, 0.0))
    N.write_stl(f"{out}/assembly.stl", assembly)
    shell_vol = cell_volume(shell)
    print(f"  all cells closed: {all_closed}; "
          f"tiling check |Σcells - shell| = {abs(total-shell_vol):.2e}")
    print(f"wrote {out}/shell.stl, assembly.stl, cell_00..13.stl")
    print("\nTamari elements (cell -> hexagon diagonals):")
    for v in range(len(V)):
        print(f"  cell_{v:02d}: {labels[v]}")
    return V, labels, faces, cells


if __name__ == "__main__":
    main()
