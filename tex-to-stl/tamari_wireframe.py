#!/usr/bin/env python3
"""Hollow / wireframe version of the Tamari decomposition.

Every edge of every cell becomes a cylindrical strut and every vertex a small
sphere, so the whole cell complex is see-through. Overlapping closed solids are
fine -- slicers union them automatically.

Outputs (in ./tamari_sym/ by default):
    wireframe_all.stl     all 14 cells' edges in one see-through frame
    wire_cell_NN.stl      each cell as its own hollow frame  (--per-piece)
"""
import math
import sys
from collections import defaultdict

import tamari_normal_fan as N
import tamari_symmetric as S

def norm(u): return math.sqrt(sum(x*x for x in u))
def sub(a, b): return (a[0]-b[0], a[1]-b[1], a[2]-b[2])
def cross(u, v): return (u[1]*v[2]-u[2]*v[1], u[2]*v[0]-u[0]*v[2], u[0]*v[1]-u[1]*v[0])


def cylinder(p, q, r, seg=12):
    d = sub(q, p); L = norm(d)
    if L < 1e-9:
        return []
    ax = tuple(x/L for x in d)
    t = (1.0, 0.0, 0.0) if abs(ax[0]) < 0.9 else (0.0, 1.0, 0.0)
    u = cross(ax, t); u = tuple(x/norm(u) for x in u)
    w = cross(ax, u)
    def ring(c):
        return [tuple(c[i] + r*(math.cos(2*math.pi*k/seg)*u[i]
                                + math.sin(2*math.pi*k/seg)*w[i]) for i in range(3))
                for k in range(seg)]
    A, B = ring(p), ring(q)
    tris = []
    for k in range(seg):
        k2 = (k+1) % seg
        tris.append((A[k], A[k2], B[k2]))
        tris.append((A[k], B[k2], B[k]))
        tris.append((p, A[k2], A[k]))     # caps
        tris.append((q, B[k], B[k2]))
    return tris


def sphere(c, r, nlat=8, nlon=12):
    def P(i, j):
        th = math.pi*i/nlat; ph = 2*math.pi*j/nlon
        return (c[0]+r*math.sin(th)*math.cos(ph),
                c[1]+r*math.sin(th)*math.sin(ph),
                c[2]+r*math.cos(th))
    tris = []
    for i in range(nlat):
        for j in range(nlon):
            j2 = (j+1) % nlon
            a, b, cc, d = P(i, j), P(i+1, j), P(i+1, j2), P(i, j2)
            if i == 0:
                tris.append((a, b, cc))
            elif i == nlat-1:
                tris.append((a, b, d))
            else:
                tris.append((a, b, cc)); tris.append((a, cc, d))
    return tris


def cell_complex_edges_vertices(V, planes):
    """All distinct edges (segments) and vertices of the 14 normal-fan cells."""
    edset = {}
    vset = {}
    def vkey(p): return tuple(round(c, 6) for c in p)
    for v in range(len(V)):
        verts = N.vertices_of(N.cell_halfspaces(v, V, planes))
        for p in verts:
            vset[vkey(p)] = p
        for (n, b) in N.cell_halfspaces(v, V, planes):
            poly = N.face_polygon(verts, n, b)
            if not poly:
                continue
            m = len(poly)
            for a in range(m):
                p, q = poly[a], poly[(a+1) % m]
                key = frozenset((vkey(p), vkey(q)))
                edset[key] = (p, q)
    return list(edset.values()), list(vset.values())


def build_wireframe(edges, vertices, strut_r, joint_r, seg=12, joints=False):
    tris = []
    for (p, q) in edges:
        tris.extend(cylinder(p, q, strut_r, seg))
    if joints and joint_r > 0:                 # optional joint spheres (nubs)
        for c in vertices:
            tris.extend(sphere(c, joint_r))
    return tris


def main(argv):
    realization = "loday" if "--loday" in argv else "sym"
    per_piece = "--per-piece" in argv
    joints = "--joints" in argv          # off by default -> no corner nubs
    if realization == "sym":
        V, labels, _ = S.symmetric_associahedron(); outdir = "tamari_sym"
    else:
        V, labels = N.associahedron_vertices(); outdir = "tamari"
    planes, faces = N.hull_facets(V)
    R = max(norm(v) for v in V)
    strut_r = 0.030 * R          # thin enough to see through
    joint_r = 0.045 * R

    edges, vertices = cell_complex_edges_vertices(V, planes)
    print(f"realization: {realization}")
    print(f"cell-complex 1-skeleton: {len(vertices)} vertices, {len(edges)} edges")
    print(f"strut radius {strut_r:.3f}; corner joints: {'on' if joints else 'off (flush)'}")

    tris = build_wireframe(edges, vertices, strut_r, joint_r, joints=joints)
    N.write_stl(f"{outdir}/wireframe_all.stl", tris)
    print(f"wrote {outdir}/wireframe_all.stl  ({len(tris)} triangles)")

    if per_piece:
        for v in range(len(V)):
            verts = N.vertices_of(N.cell_halfspaces(v, V, planes))
            ed = {}
            def vkey(p): return tuple(round(c, 6) for c in p)
            for (n, b) in N.cell_halfspaces(v, V, planes):
                poly = N.face_polygon(verts, n, b)
                if not poly:
                    continue
                for a in range(len(poly)):
                    p, q = poly[a], poly[(a+1) % len(poly)]
                    ed[frozenset((vkey(p), vkey(q)))] = (p, q)
            t = build_wireframe(list(ed.values()), verts, strut_r, joint_r, joints=joints)
            N.write_stl(f"{outdir}/wire_cell_{v:02d}.stl", t)
        print(f"wrote {len(V)} per-piece wire_cell_NN.stl files")
    return V, planes, edges


if __name__ == "__main__":
    main(sys.argv)
