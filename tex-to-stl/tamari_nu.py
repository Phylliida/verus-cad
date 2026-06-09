#!/usr/bin/env python3
"""nu-trees for the nu-associahedron (Ceballos-Padrol-Sarmiento), validated.

A nu-tree (Def 3.1, CPS) for a lattice path nu (N/E steps from origin):
  A_nu = lattice points weakly above nu inside the Ferrers diagram.
  p, q are nu-INCOMPATIBLE iff one is STRICTLY southwest/northeast of the other
       AND the smallest rectangle spanned by them lies entirely inside A_nu.
  A nu-tree = a maximal set of pairwise compatible points (all have equal size).

For nu = (NEE)^4 (the staircase of the 2-Tamari lattice, n=4) there are 55
nu-trees of 13 points each -- the 55 vertices of Bergeron's Figure 6.
"""
from collections import Counter


def path_lower(nu):
    x = y = 0; L = {0: 0}
    for s in nu:
        if s == 'N':
            y += 1
        else:
            x += 1; L[x] = y
    return L, y, x


def A_nu(nu):
    L, b, a = path_lower(nu)
    return [(x, yy) for x in range(a + 1) for yy in range(L[x], b + 1)]


def incompatible(p, q, Aset):
    strictly = ((p[0] < q[0] and p[1] < q[1]) or (p[0] > q[0] and p[1] > q[1]))
    if not strictly:
        return False
    x0, x1 = sorted((p[0], q[0])); y0, y1 = sorted((p[1], q[1]))
    return all((xx, yy) in Aset
               for xx in range(x0, x1 + 1) for yy in range(y0, y1 + 1))


def nu_trees(nu):
    A = A_nu(nu); Aset = set(A); n = len(A)
    adj = [set() for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            if not incompatible(A[i], A[j], Aset):
                adj[i].add(j); adj[j].add(i)
    out = []
    def bk(R, P, X):
        if not P and not X:
            out.append(frozenset(A[i] for i in R)); return
        u = max(P | X, key=lambda z: len(adj[z]))
        for v in list(P - adj[u]):
            bk(R | {v}, P & adj[v], X & adj[v]); P = P - {v}; X = X | {v}
    bk(set(), set(range(n)), set())
    return A, out


def flip_graph(trees):
    """Edges between nu-trees differing by a single point (|T xor T'| == 2)."""
    edges = []
    for i in range(len(trees)):
        for j in range(i + 1, len(trees)):
            if len(trees[i] ^ trees[j]) == 2:
                edges.append((i, j))
    return edges


def brick_vectors(nu):
    """Pilaud-Stump brick vector for each nu-tree (validated on the CPS ENEEN
    example): tree points are elbows, others are crossings; at each lattice
    point (read column-by-column, bottom-to-top) count pipes at levels 1..q
    BEFORE the crossing.  b(T)_i = -(#lattice points below pipe i).
    The vectors span an affine space of dimension 2(n-1) for nu=(NEE)^n -- so
    the 2-Tamari(n=4) nu-associahedron is 6-dimensional, and any 3D picture of
    it (such as Bergeron's Figure 6) is necessarily a projection."""
    A, trees = nu_trees(nu)
    order = sorted(A, key=lambda p: (p[0], p[1]))
    C = 1 - min(x - y for (x, y) in A)
    label = {p: p[0] - p[1] + C for p in A}
    npipes = max(label.values()) + 1
    out = []
    for tr in trees:
        pi = list(range(1, npipes + 1)); cnt = [0]*(npipes + 1)
        for p in order:
            q = label[p]
            for lev in range(1, q + 1):
                cnt[pi[lev - 1]] += 1
            if p not in tr:
                pi[q - 1], pi[q] = pi[q], pi[q - 1]
        out.append(tuple(-cnt[i] for i in range(1, npipes + 1)))
    return trees, out


if __name__ == "__main__":
    NU = "NEENEENEENEE"   # (NEE)^4
    A, trees = nu_trees(NU)
    print(f"nu = {NU}  (2-Tamari, n=4)")
    print(f"|A_nu| = {len(A)} lattice points")
    print(f"nu-trees (vertices)          : {len(trees)}  (Fuss-Catalan 55)")
    print(f"all nu-trees have size        : {sorted(set(len(t) for t in trees))}")
    E = flip_graph(trees)
    deg = Counter()
    for i, j in E:
        deg[i] += 1; deg[j] += 1
    print(f"flip-graph edges (1-skeleton): {len(E)}")
    print(f"vertex-degree distribution   : {dict(sorted(Counter(deg.values()).items()))}")
