#!/usr/bin/env python3
"""The 4-dimensional associahedron K6 and its 3D Schlegel diagram.

K6 = secondary structure on triangulations of a HEPTAGON (7-gon):
  * 42 vertices  = Tamari lattice T5
  * 14 facets    = the 14 diagonals of the heptagon; each facet is the
                   product of the associahedra of the two sub-polygons the
                   diagonal cuts -> a product of associahedra:
                     diagonal cutting (3-gon,6-gon) -> K2 x K5 = K5      (x7)
                     diagonal cutting (4-gon,5-gon) -> K3 x K4 = prism   (x7)

Projecting K6 (Loday coords in R^4) from beyond one K5 facet gives a Schlegel
diagram: that facet becomes the outer 3D associahedron, the other 13 facets
become convex product-of-associahedra cells filling it.
"""
import math
from collections import defaultdict

import tamari_normal_fan as N
import tamari_symmetric as S

# --------------------------------------------------------------------------
def tri_to_tree(triset, lo, hi):
    if hi - lo == 1:
        return None
    for tri in triset:
        s = set(tri)
        if lo in s and hi in s:
            mids = [k for k in s if lo < k < hi]
            if len(mids) == 1:
                k = mids[0]
                return (tri_to_tree(triset, lo, k), tri_to_tree(triset, k, hi))
    raise RuntimeError("no triangle on edge")

def diagonals_of(T, m=7):
    boundary = {frozenset((i, (i+1) % m)) for i in range(m)}
    diag = set()
    for (a, b, c) in T:
        for e in (frozenset((a, b)), frozenset((b, c)), frozenset((a, c))):
            if e not in boundary:
                diag.add(e)
    return frozenset(diag)

def loday5(tree):
    out = []
    def rec(s):
        if s is None:
            return
        rec(s[0]); out.append(N.nleaves(s[0]) * N.nleaves(s[1])); rec(s[1])
    rec(tree)
    return tuple(out)

def project_R5_to_R4(pts):
    c = (3, 3, 3, 3, 3)
    basis = [(1,-1,0,0,0), (1,1,-2,0,0), (1,1,1,-3,0), (1,1,1,1,-4)]
    basis = [tuple(x/math.sqrt(sum(t*t for t in u)) for x in u) for u in basis]
    out = []
    for p in pts:
        d = [p[i]-c[i] for i in range(5)]
        out.append(tuple(sum(d[i]*u[i] for i in range(5)) for u in basis))
    return out

def project_to_R4(pts):
    """Isometric projection of points (in R^d, affinely 4-dimensional) to R^4."""
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
        if len(basis) == 4:
            break
    return [tuple(sum(D[k][i]*basis[b][i] for i in range(d)) for b in range(4))
            for k in range(n)]


def _facets_from_diagonals(Ts, m):
    diags = [diagonals_of(T, m) for T in Ts]
    alldiag = sorted({frozenset((i, j)) for i in range(m) for j in range(i+2, m)
                      if not (i == 0 and j == m-1)}, key=lambda e: tuple(sorted(e)))
    return {d: [i for i in range(len(Ts)) if d in diags[i]] for d in alldiag}, alldiag


def build_k6_sym():
    """Symmetric K6 = secondary polytope of a REGULAR heptagon (D7 symmetry)."""
    m = 7
    hept = [(math.cos(2*math.pi*k/m), math.sin(2*math.pi*k/m)) for k in range(m)]
    Ts = S.triangulations(list(range(m)))
    trees = [tri_to_tree(set(tuple(sorted(t)) for t in T), 0, m-1) for T in Ts]
    def area(t):
        a, b, c = hept[t[0]], hept[t[1]], hept[t[2]]
        return abs((b[0]-a[0])*(c[1]-a[1]) - (b[1]-a[1])*(c[0]-a[0]))/2
    gkz = []
    for T in Ts:
        phi = [0.0]*m
        for tri in T:
            A = area(tri)
            for i in tri:
                phi[i] += A
        gkz.append(tuple(phi))
    V4 = project_to_R4(gkz)
    facets, alldiag = _facets_from_diagonals(Ts, m)
    return Ts, trees, V4, facets, alldiag


def build_k6_hexfacet():
    """K6 = secondary polytope of a heptagon that is a REGULAR HEXAGON (vertices
    0..5) plus one extra vertex 6.  Then the facet for diagonal (0,5) -- which
    cuts off the ear at vertex 6 -- is the secondary polytope of the regular
    hexagon = EXACTLY the symmetric K5 (tamari_sym).  Projecting through it makes
    the Schlegel outer shell the symmetric associahedron, while the whole solid
    is still a genuine convex K6 (vertices = T5, facets = products of assoc.)."""
    m = 7
    hexa = [(math.cos(2*math.pi*k/6), math.sin(2*math.pi*k/6)) for k in range(6)]
    hept = hexa + [(math.cos(-math.pi/6), math.sin(-math.pi/6))]   # extra at -30deg
    Ts = S.triangulations(list(range(m)))
    trees = [tri_to_tree(set(tuple(sorted(t)) for t in T), 0, m-1) for T in Ts]
    def area(t):
        a, b, c = hept[t[0]], hept[t[1]], hept[t[2]]
        return abs((b[0]-a[0])*(c[1]-a[1]) - (b[1]-a[1])*(c[0]-a[0]))/2
    gkz = []
    for T in Ts:
        phi = [0.0]*m
        for tri in T:
            A = area(tri)
            for i in tri:
                phi[i] += A
        gkz.append(tuple(phi))
    V4 = project_to_R4(gkz)
    facets, alldiag = _facets_from_diagonals(Ts, m)
    return Ts, trees, V4, facets, alldiag


def build_k6():
    m = 7
    Ts = S.triangulations(list(range(m)))
    trees = [tri_to_tree(set(tuple(sorted(t)) for t in T), 0, m-1) for T in Ts]
    pts5 = [loday5(t) for t in trees]
    V4 = project_R5_to_R4(pts5)
    diags = [diagonals_of(T, m) for T in Ts]
    # all heptagon diagonals
    alldiag = sorted({frozenset((i, j)) for i in range(m) for j in range(i+2, m)
                      if not (i == 0 and j == m-1)}, key=lambda e: tuple(sorted(e)))
    facets = {d: [i for i in range(len(Ts)) if d in diags[i]] for d in alldiag}
    return Ts, trees, V4, facets, alldiag


if __name__ == "__main__":
    Ts, trees, V4, facets, alldiag = build_k6()
    print(f"vertices (triangulations of heptagon = Tamari T5): {len(Ts)}")
    print(f"Loday sum check: {set(sum(loday5(t)) for t in trees)} (should be 15)")
    print(f"diagonals of heptagon = facets: {len(alldiag)}")
    sizes = sorted(len(v) for v in facets.values())
    from collections import Counter
    print(f"facet vertex-counts: {dict(Counter(sizes))}")
    for d in alldiag:
        a, b = sorted(d)
        gap = min((b-a) % 7, (a-b) % 7)
        kind = "K5  (K2xK5)" if len(facets[d]) == 14 else "prism (K3xK4)"
        print(f"  diagonal {a}-{b} (skip {gap}): {len(facets[d]):2d} vertices -> {kind}")
