#!/usr/bin/env python3
"""Schlegel diagram of the 4D associahedron K6 -> 3D STLs.

Project K6 (in R^4) from a point just beyond one K5 facet onto that facet's
hyperplane. That facet becomes the outer 3D associahedron; the other 13 facets
become convex product-of-associahedra cells (5 more K5 + 7 pentagon-prisms... actually
6 K5 + 7 prisms) filling its interior.  Vertices stay the Tamari lattice T5.
"""
import math
from collections import defaultdict, Counter
import tamari_normal_fan as N
import tamari_k6 as K

# ---- R^4 helpers ----
def sub4(a, b): return tuple(a[i]-b[i] for i in range(4))
def dot4(a, b): return sum(a[i]*b[i] for i in range(4))
def norm4(a): return math.sqrt(dot4(a, a))
def det3(M):
    return (M[0][0]*(M[1][1]*M[2][2]-M[1][2]*M[2][1])
            - M[0][1]*(M[1][0]*M[2][2]-M[1][2]*M[2][0])
            + M[0][2]*(M[1][0]*M[2][1]-M[1][1]*M[2][0]))
def normal4(a, b, c):
    cols = [a, b, c]; n = []
    for k in range(4):
        idx = [i for i in range(4) if i != k]
        M = [[cols[r][idx[t]] for t in range(3)] for r in range(3)]
        n.append(((-1)**k)*det3(M))
    return tuple(n)

def facet_hyperplane(Fv):
    """Unit 4D normal n and offset d with n.x = d for the 3-flat through Fv."""
    p0 = Fv[0]; indep = []
    for q in Fv[1:]:
        r = list(sub4(q, p0))
        for u in indep:
            c = dot4(r, u)/dot4(u, u)
            r = [r[i]-c*u[i] for i in range(4)]
        if norm4(r) > 1e-7:
            indep.append(tuple(r))
        if len(indep) == 3:
            break
    n = normal4(*indep); L = norm4(n); n = tuple(t/L for t in n)
    return n, dot4(n, p0)

def hull_triangles(P, eps=1e-6):
    """Triangulate the convex hull surface of 3D point list P."""
    n = len(P); seen = set(); out = []
    for i in range(n):
        for j in range(i+1, n):
            for k in range(j+1, n):
                nr = N.cross(N.sub(P[j], P[i]), N.sub(P[k], P[i])); L = N.norm(nr)
                if L < 1e-9:
                    continue
                nr = tuple(t/L for t in nr); d = N.dot(nr, P[i])
                s = [N.dot(nr, P[m])-d for m in range(n)]
                if max(s) <= eps or min(s) >= -eps:
                    if min(s) >= -eps:
                        nr = tuple(-t for t in nr); d = -d
                    key = tuple(round(t, 5) for t in nr)+(round(d, 5),)
                    if key in seen:
                        continue
                    seen.add(key)
                    on = [m for m in range(n) if abs(N.dot(nr, P[m])-d) < 1e-5]
                    ctr = tuple(sum(P[m][t] for m in on)/len(on) for t in range(3))
                    e1 = None
                    for m in on:
                        dv = N.sub(P[m], ctr)
                        if N.norm(dv) > 1e-9:
                            e1 = tuple(t/N.norm(dv) for t in dv); break
                    e2 = N.cross(nr, e1); e2 = tuple(t/N.norm(e2) for t in e2)
                    order = sorted(on, key=lambda m: math.atan2(
                        N.dot(N.sub(P[m], ctr), e2), N.dot(N.sub(P[m], ctr), e1)))
                    for a in range(1, len(order)-1):
                        out.append((P[order[0]], P[order[a]], P[order[a+1]]))
    return out

def cell_volume(tris):
    if not tris:
        return 0.0
    r = tuple(sum(p[i] for t in tris for p in t)/(3*len(tris)) for i in range(3))
    s = 0.0
    for a, b, c in tris:
        A = N.sub(a, r); B = N.sub(b, r); C = N.sub(c, r)
        s += abs(N.dot(A, N.cross(B, C)))/6
    return s


def main():
    import os
    out = "tamari_k6"; os.makedirs(out, exist_ok=True)
    Ts, trees, V4, facets, alldiag = K.build_k6_hexfacet()
    C = tuple(sum(v[i] for v in V4)/len(V4) for i in range(4))   # centroid ~0

    # project through the facet (0,5) -- the one that IS the symmetric K5
    Fdiag = frozenset((0, 5))
    Fidx = facets[Fdiag]
    Fv = [V4[i] for i in Fidx]
    nF, dF = facet_hyperplane(Fv)
    if dot4(nF, C) > dF:                       # orient outward (centroid inside)
        nF = tuple(-t for t in nF); dF = -dF
    onplane = max(abs(dot4(nF, V4[i])-dF) for i in Fidx)
    print(f"project through facet {sorted(Fdiag)} (K5, 14 vtx); "
          f"max off-plane = {onplane:.2e}")

    cF = tuple(sum(p[i] for p in Fv)/len(Fv) for i in range(4))
    h = dF - dot4(nF, C)                         # > 0, centroid below facet
    e = tuple(cF[i] + 0.30*h*nF[i] for i in range(4))   # viewpoint just beyond F

    # 3D orthonormal basis of the facet hyperplane
    bvecs = []
    for k in range(4):
        v = [1.0 if i == k else 0.0 for i in range(4)]
        v = [v[i]-dot4(v, nF)*nF[i] for i in range(4)]
        for u in bvecs:
            c = dot4(v, u); v = [v[i]-c*u[i] for i in range(4)]
        if norm4(v) > 1e-7:
            bvecs.append(tuple(x/norm4(v) for x in v))
        if len(bvecs) == 3:
            break

    def project(v4):
        denom = dot4(nF, sub4(v4, e))
        t = (dF - dot4(nF, e))/denom
        p = tuple(e[i] + t*(v4[i]-e[i]) for i in range(4))
        q = sub4(p, cF)
        return tuple(dot4(q, b) for b in bvecs)

    P3 = [project(v) for v in V4]

    # build each facet's cell (and the outer facet) as STL
    def kind(d): return "K5" if len(facets[d]) == 14 else "prism"
    interior = [d for d in alldiag if d != Fdiag]
    shell_tris = hull_triangles([P3[i] for i in Fidx])
    N.write_stl(f"{out}/symm_shell.stl", shell_tris)
    shell_vol = cell_volume(shell_tris)

    total = 0.0; counts = Counter()
    for idx, d in enumerate(interior):
        pts = [P3[i] for i in facets[d]]
        tris = hull_triangles(pts)
        ref = tuple(sum(p[i] for p in pts)/len(pts) for i in range(3))
        a, b = sorted(d)
        N.write_stl(f"{out}/symm_cell_{idx:02d}_{a}{b}_{kind(d)}.stl", tris, ref)
        total += cell_volume(tris); counts[kind(d)] += 1

    print(f"outer shell (3D associahedron): {len(shell_tris)} triangles, vol {shell_vol:.4f}")
    print(f"interior cells: {len(interior)}  ({dict(counts)})")
    print(f"tiling check |sum(cells) - shell| = {abs(total-shell_vol):.2e}")
    print(f"wrote {out}/symm_shell.stl + {len(interior)} symm_cell_*.stl")
    return P3, Fidx, facets, interior, Fdiag


if __name__ == "__main__":
    main()
