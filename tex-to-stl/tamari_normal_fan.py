#!/usr/bin/env python3
"""Convex, watertight decomposition of the 3D associahedron into 14 cells -- one
per Tamari-lattice element -- whose adjacency is EXACTLY the Tamari Hasse diagram.

Construction (the normal fan of Loday's K5):

    cell_v = { x in P : <v,x> >= <w,x> for every vertex w of P }
           = ( normal cone of P at v ) ∩ P

* P = Loday's associahedron (14 vertices), centered at its barycenter = origin.
* Each cell is an intersection of half-spaces  -> convex.
* The normal cones tile R^3, so the cells tile P (watertight); every interior
  wall is a plane through the origin -> flat, both neighbors convex across it.
* Normal-fan fact: cones N(v), N(w) share a 2-D wall  <=>  vw is an edge of P.
  So the cell-adjacency graph is exactly the 21 Tamari cover relations, 3-regular,
  with no extra adjacencies.

Outputs (in ./tamari/):  shell.stl, assembly.stl, cell_00.stl ... cell_13.stl
"""
import math
import os
import struct
from collections import defaultdict

# --------------------------------------------------------------------------
# vector helpers
# --------------------------------------------------------------------------
def sub(a, b): return (a[0]-b[0], a[1]-b[1], a[2]-b[2])
def cross(u, v): return (u[1]*v[2]-u[2]*v[1], u[2]*v[0]-u[0]*v[2], u[0]*v[1]-u[1]*v[0])
def dot(u, v): return u[0]*v[0]+u[1]*v[1]+u[2]*v[2]
def norm(u): return math.sqrt(dot(u, u))

def solve3(rows, rhs):
    """Solve the 3x3 system rows·x = rhs by Cramer's rule; None if singular."""
    def det(m):
        return (m[0][0]*(m[1][1]*m[2][2]-m[1][2]*m[2][1])
                - m[0][1]*(m[1][0]*m[2][2]-m[1][2]*m[2][0])
                + m[0][2]*(m[1][0]*m[2][1]-m[1][1]*m[2][0]))
    D = det(rows)
    if abs(D) < 1e-12:
        return None
    out = []
    for i in range(3):
        m = [r[:] for r in rows]
        for r in range(3):
            m[r][i] = rhs[r]
        out.append(det(m)/D)
    return tuple(out)


# --------------------------------------------------------------------------
# Loday's K5
# --------------------------------------------------------------------------
def gen_trees(n):
    if n == 0:
        return [None]
    out = []
    for k in range(n):
        for L in gen_trees(k):
            for R in gen_trees(n-1-k):
                out.append((L, R))
    return out

def nleaves(t):
    return 1 if t is None else nleaves(t[0]) + nleaves(t[1])

def loday(t):
    out = []
    def rec(s):
        if s is None:
            return
        rec(s[0]); out.append(nleaves(s[0]) * nleaves(s[1])); rec(s[1])
    rec(t)
    return tuple(out)

def tree_label(t):
    """A compact bracketing string for the binary tree (Tamari element)."""
    if t is None:
        return "."
    return "(" + tree_label(t[0]) + tree_label(t[1]) + ")"

def associahedron_vertices():
    trees = gen_trees(4)
    pts4 = [loday(t) for t in trees]
    c = (2.5, 2.5, 2.5, 2.5)                      # barycenter of the Loday points
    basis = [(1, -1, 0, 0), (1, 1, -2, 0), (1, 1, 1, -3)]
    basis = [tuple(x/math.sqrt(sum(t*t for t in u)) for x in u) for u in basis]
    def to3(p):
        d = [p[i]-c[i] for i in range(4)]
        return tuple(sum(d[i]*u[i] for i in range(4)) for u in basis)
    V = [to3(p) for p in pts4]
    labels = [tree_label(t) for t in trees]
    return V, labels


# --------------------------------------------------------------------------
# hull facets / edges of P
# --------------------------------------------------------------------------
def hull_facets(V, eps=1e-7):
    """Return list of (unit_outward_normal, offset) and {plane_key: vertex_set}."""
    n = len(V)
    facets = {}
    for i in range(n):
        for j in range(i+1, n):
            for k in range(j+1, n):
                nrm = cross(sub(V[j], V[i]), sub(V[k], V[i]))
                L = norm(nrm)
                if L < 1e-9:
                    continue
                nrm = tuple(t/L for t in nrm)
                d = dot(nrm, V[i])
                s = [dot(nrm, V[m]) - d for m in range(n)]
                if max(s) <= eps or min(s) >= -eps:
                    if min(s) >= -eps:                   # orient outward
                        nrm = tuple(-t for t in nrm); d = -d
                    onface = frozenset(m for m in range(n)
                                       if abs(dot(nrm, V[m]) - d) < 1e-6)
                    key = tuple(round(t, 5) for t in nrm) + (round(d, 5),)
                    facets[key] = (nrm, d, onface)
    planes = [(v[0], v[1]) for v in facets.values()]
    faces = [v[2] for v in facets.values()]
    return planes, faces

def polytope_edges(V, faces):
    edges = set()
    for f in faces:
        fl = list(f)
        ctr = tuple(sum(V[m][i] for m in fl)/len(fl) for i in range(3))
        p0 = sub(V[fl[0]], ctr)
        nrm = None
        for a in range(1, len(fl)):
            cand = cross(p0, sub(V[fl[a]], ctr))
            if dot(cand, cand) > 1e-9:
                nrm = cand; break
        e1 = tuple(t/norm(p0) for t in p0)
        e2 = cross(nrm, e1); e2 = tuple(t/norm(e2) for t in e2)
        order = sorted(fl, key=lambda m: math.atan2(dot(sub(V[m], ctr), e2),
                                                     dot(sub(V[m], ctr), e1)))
        for a in range(len(order)):
            edges.add(frozenset((order[a], order[(a+1) % len(order)])))
    return edges


# --------------------------------------------------------------------------
# normal-fan cells
# --------------------------------------------------------------------------
def vertices_of(halfspaces, eps=1e-6):
    """Enumerate vertices of { x : <n,x> <= b } over the given (n,b) half-spaces."""
    m = len(halfspaces)
    pts = []
    for i in range(m):
        for j in range(i+1, m):
            for k in range(j+1, m):
                x = solve3([list(halfspaces[i][0]), list(halfspaces[j][0]),
                            list(halfspaces[k][0])],
                           [halfspaces[i][1], halfspaces[j][1], halfspaces[k][1]])
                if x is None:
                    continue
                if all(dot(nb[0], x) <= nb[1] + eps for nb in halfspaces):
                    pts.append(x)
    uniq = []
    for p in pts:
        if not any(all(abs(p[i]-q[i]) < 1e-6 for i in range(3)) for q in uniq):
            uniq.append(p)
    return uniq

def cell_halfspaces(v, V, facet_planes):
    """Half-spaces (n,b) with <n,x> <= b defining cell_v."""
    hs = [(nrm, d) for (nrm, d) in facet_planes]          # P's facets
    vv = V[v]
    for w in range(len(V)):                               # normal-cone walls
        if w == v:
            continue
        nw = sub(V[w], vv)                                # <w-v, x> <= 0
        hs.append((nw, 0.0))
    return hs

def face_polygon(verts, n, b, eps=1e-6):
    """Ordered vertices of `verts` lying on plane <n,x>=b (>=3 -> a facet)."""
    on = [p for p in verts if abs(dot(n, p) - b) < eps]
    if len(on) < 3:
        return None
    ctr = tuple(sum(p[i] for p in on)/len(on) for i in range(3))
    e1 = None
    for p in on:
        d = sub(p, ctr)
        if norm(d) > 1e-9:
            e1 = tuple(t/norm(d) for t in d); break
    nn = tuple(t/norm(n) for t in n)
    e2 = cross(nn, e1); e2 = tuple(t/norm(e2) for t in e2)
    return sorted(on, key=lambda p: math.atan2(dot(sub(p, ctr), e2),
                                               dot(sub(p, ctr), e1)))


# --------------------------------------------------------------------------
# STL
# --------------------------------------------------------------------------
def tri_normal(a, b, c, ref=None):
    nrm = cross(sub(b, a), sub(c, a)); L = norm(nrm)
    if L == 0:
        return (0.0, 0.0, 0.0)
    nrm = tuple(t/L for t in nrm)
    if ref is not None:                       # orient away from ref (outward)
        if dot(nrm, sub(a, ref)) < 0:
            nrm = tuple(-t for t in nrm)
    return nrm

def write_stl(path, triangles, ref=None):
    with open(path, "wb") as f:
        f.write(b"\0"*80)
        f.write(struct.pack("<I", len(triangles)))
        for a, b, c in triangles:
            n = tri_normal(a, b, c, ref)
            f.write(struct.pack("<12fH", *n, *a, *b, *c, 0))

def fan(poly):
    return [(poly[0], poly[i], poly[i+1]) for i in range(1, len(poly)-1)]


# --------------------------------------------------------------------------
# main
# --------------------------------------------------------------------------
def main():
    out = "tamari"
    os.makedirs(out, exist_ok=True)
    V, labels = associahedron_vertices()
    facet_planes, faces = hull_facets(V)
    edges = polytope_edges(V, faces)
    print(f"associahedron: {len(V)} vertices, {len(edges)} edges, {len(faces)} facets")

    # each vertex extremal in its own radial direction?  (=> v is a corner of cell_v)
    contains = all(all(dot(V[v], V[v]) >= dot(V[w], V[v]) - 1e-9 for w in range(len(V)))
                   for v in range(len(V)))
    print(f"every cell contains its own vertex: {contains}")

    # build cells
    cells = []
    for v in range(len(V)):
        hs = cell_halfspaces(v, V, facet_planes)
        verts = vertices_of(hs)
        cells.append(verts)

    # adjacency: cells v,w share a facet iff the wall <w-v,x>=0 carries >=3 cell_v verts
    adj = defaultdict(set)
    for v in range(len(V)):
        for w in range(len(V)):
            if w == v:
                continue
            poly = face_polygon(cells[v], sub(V[w], V[v]), 0.0)
            if poly and len(poly) >= 3:
                adj[v].add(w)
    adj_edges = {frozenset((v, w)) for v in adj for w in adj[v]}
    degs = sorted(len(adj[v]) for v in range(len(V)))
    print(f"cell adjacencies: {len(adj_edges)}  | degree sequence: {degs}")
    print(f"adjacency == Tamari Hasse diagram (21 covers): {adj_edges == edges}")

    # write STLs + collect assembly; verify each cell closed
    def edge_counts(tris):
        ec = defaultdict(int)
        rk = lambda p: tuple(round(c, 6) for c in p)
        for a, b, c in tris:
            for u, w in ((a, b), (b, c), (c, a)):
                ec[frozenset((rk(u), rk(w)))] += 1
        return ec

    assembly = []
    all_closed = True
    internal_walls = 0
    for v in range(len(V)):
        verts = cells[v]
        ref = tuple(sum(p[i] for p in verts)/len(verts) for i in range(3))
        tris = []
        for (n, b) in cell_halfspaces(v, V, facet_planes):
            poly = face_polygon(verts, n, b)
            if poly:
                tris.extend(fan(poly))
        # dedupe coincident facet planes can double count; rebuild from unique facets
        write_stl(f"{out}/cell_{v:02d}.stl", tris, ref)
        assembly.extend(tris)
        ec = edge_counts(tris)
        bnd = sum(1 for n in ec.values() if n % 2 == 1)
        if bnd:
            all_closed = False
    print(f"all 14 cells closed (watertight solids): {all_closed}")

    # shell = hull of V
    shell = []
    for f in faces:
        poly = face_polygon(V, *plane_of_face(V, f))
        shell.extend(fan(poly))
    write_stl(f"{out}/shell.stl", shell, ref=(0.0, 0.0, 0.0))
    ec = edge_counts(shell)
    sh_bnd = sum(1 for n in ec.values() if n % 2 == 1)
    sh_dist = dict(sorted({k: v for k, v in
                           __import__("collections").Counter(ec.values()).items()}.items()))
    print(f"shell: {len(shell)} triangles, boundary edges {sh_bnd}, "
          f"edge use-counts {sh_dist}  (watertight: {sh_bnd == 0 and set(sh_dist) <= {2}})")

    write_stl(f"{out}/assembly.stl", assembly)
    print(f"\nwrote {out}/shell.stl, {out}/assembly.stl, and 14 cell_NN.stl files")
    print("\nTamari elements (cell -> binary tree):")
    for v in range(len(V)):
        print(f"  cell_{v:02d}: {labels[v]}")


def plane_of_face(V, f):
    fl = list(f)
    ctr = tuple(sum(V[m][i] for m in fl)/len(fl) for i in range(3))
    nrm = None
    p0 = sub(V[fl[0]], ctr)
    for a in range(1, len(fl)):
        cand = cross(p0, sub(V[fl[a]], ctr))
        if dot(cand, cand) > 1e-9:
            nrm = cand; break
    L = norm(nrm); nrm = tuple(t/L for t in nrm)
    if dot(nrm, ctr) < 0:
        nrm = tuple(-t for t in nrm)
    return nrm, dot(nrm, V[fl[0]])


if __name__ == "__main__":
    main()
