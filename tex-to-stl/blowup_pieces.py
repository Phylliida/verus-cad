#!/usr/bin/env python3
"""Make a "blown-up" (exploded-but-connected) version of a tiling of solids.

Takes a directory of per-piece closed STL solids that tile a shape watertight
(e.g. c2_congruent_out/shell_*.stl), pushes every piece radially away from the
common centre so gaps open between neighbours, then bridges each pair of
originally-adjacent pieces with a thin strut whose cross-section is a shrunk
copy of the face they used to share.  The strut pokes a little way into both
pieces, so the whole thing is one connected body when a slicer unions the
overlapping solids -- like shrink-wrapping the exploded cluster and sucking the
air out, leaving indented webbing in the crevices.

Pure Python, no deps.  Output is a multi-solid binary STL: each piece and each
strut is its own closed mesh, and neighbours overlap where the struts dive in.
Any slicer (Cura / Prusa / Bambu / ...) treats overlapping closed volumes as a
union, so it prints as a single connected object.

Usage:
    python3 blowup_pieces.py [in_dir] [out.stl] [explode] [shrink] [pen]

Defaults: in_dir=c2_congruent_out  out=c2_blownup_out/blownup.stl
          explode=1.10  shrink=0.85  pen=0.45
"""
import glob
import math
import os
import struct
import sys
from collections import defaultdict


# ---------- tiny vector helpers ----------
def sub(a, b): return (a[0] - b[0], a[1] - b[1], a[2] - b[2])
def add(a, b): return (a[0] + b[0], a[1] + b[1], a[2] + b[2])
def scl(a, s): return (a[0] * s, a[1] * s, a[2] * s)
def dot(a, b): return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]
def cross(a, b):
    return (a[1] * b[2] - a[2] * b[1],
            a[2] * b[0] - a[0] * b[2],
            a[0] * b[1] - a[1] * b[0])
def norm(a): return math.sqrt(dot(a, a))
def unit(a):
    n = norm(a)
    return (0.0, 0.0, 0.0) if n < 1e-12 else scl(a, 1.0 / n)
def mean(pts):
    n = len(pts)
    s = (0.0, 0.0, 0.0)
    for p in pts:
        s = add(s, p)
    return scl(s, 1.0 / n)


# ---------- STL io ----------
def read_stl(path):
    with open(path, 'rb') as f:
        data = f.read()
    if data[:5] == b'solid' and b'facet' in data[:512]:
        import re
        txt = data.decode('utf8', errors='ignore')
        v = re.findall(r'vertex\s+([-\d.eE+]+)\s+([-\d.eE+]+)\s+([-\d.eE+]+)', txt)
        v = [(float(a), float(b), float(c)) for a, b, c in v]
        return [(v[i], v[i + 1], v[i + 2]) for i in range(0, len(v), 3)]
    n = struct.unpack('<I', data[80:84])[0]
    off, tris = 84, []
    for _ in range(n):
        val = struct.unpack('<12fH', data[off:off + 50]); off += 50
        tris.append((val[3:6], val[6:9], val[9:12]))
    return tris


def write_binary_stl(path, tris, name="blownup"):
    with open(path, 'wb') as f:
        hdr = name.encode()[:79].ljust(80, b'\0')
        f.write(hdr)
        f.write(struct.pack('<I', len(tris)))
        for a, b, c in tris:
            nrm = unit(cross(sub(b, a), sub(c, a)))
            f.write(struct.pack('<12fH', *nrm, *a, *b, *c, 0))


# ---------- geometry ----------
def ckey(v, g=20.0):
    """coarse spatial key for matching shared vertices across pieces"""
    return (round(v[0] * g), round(v[1] * g), round(v[2] * g))


def unique_verts(tris):
    d = {}
    for tri in tris:
        for v in tri:
            d[ckey(v)] = v
    return d


def order_polygon(verts):
    """order a set of ~coplanar points into a polygon; return (ordered, normal)"""
    c = mean(verts)
    # seed normal from first non-degenerate triple
    nrm = None
    for i in range(1, len(verts) - 1):
        cand = cross(sub(verts[i], verts[0]), sub(verts[i + 1], verts[0]))
        if norm(cand) > 1e-9:
            nrm = unit(cand); break
    if nrm is None:
        nrm = (0.0, 0.0, 1.0)
    u = unit(sub(verts[0], c))
    if norm(u) < 1e-9:
        u = unit(sub(verts[1], c))
    w = unit(cross(nrm, u))
    ordered = sorted(verts, key=lambda p: math.atan2(dot(sub(p, c), w),
                                                      dot(sub(p, c), u)))
    # refine normal via Newell over the ordered loop
    nx = ny = nz = 0.0
    m = len(ordered)
    for i in range(m):
        p, q = ordered[i], ordered[(i + 1) % m]
        nx += (p[1] - q[1]) * (p[2] + q[2])
        ny += (p[2] - q[2]) * (p[0] + q[0])
        nz += (p[0] - q[0]) * (p[1] + q[1])
    if norm((nx, ny, nz)) > 1e-9:
        nrm = unit((nx, ny, nz))
    return ordered, nrm


def loft(ringA, ringB):
    """closed prism between two equal-length ordered rings"""
    tris = []
    m = len(ringA)
    for i in range(m):
        j = (i + 1) % m
        tris.append((ringA[i], ringA[j], ringB[j]))
        tris.append((ringA[i], ringB[j], ringB[i]))
    # caps (fan)
    ca, cb = mean(ringA), mean(ringB)
    for i in range(m):
        j = (i + 1) % m
        tris.append((ca, ringA[j], ringA[i]))   # cap A
        tris.append((cb, ringB[i], ringB[j]))   # cap B
    return tris


def main():
    in_dir = sys.argv[1] if len(sys.argv) > 1 else "c2_congruent_out"
    out_path = sys.argv[2] if len(sys.argv) > 2 else "c2_blownup_out/blownup.stl"
    EXPLODE = float(sys.argv[3]) if len(sys.argv) > 3 else 1.10
    SHRINK = float(sys.argv[4]) if len(sys.argv) > 4 else 0.85
    PEN = float(sys.argv[5]) if len(sys.argv) > 5 else 0.45

    files = sorted(glob.glob(os.path.join(in_dir, "shell_[0-9]*.stl")))
    if not files:
        files = sorted(f for f in glob.glob(os.path.join(in_dir, "*.stl"))
                       if "assembly" not in f and os.path.basename(f) != "shell.stl")
    pieces = {}
    for p in files:
        name = os.path.basename(p)
        for pre in ("shell_",):
            if name.startswith(pre):
                name = name[len(pre):]
        pieces[name[:-4]] = read_stl(p)
    names = list(pieces)
    print(f"loaded {len(names)} pieces from {in_dir}")

    # centroids + global centre
    centroid = {n: mean([v for tri in pieces[n] for v in tri]) for n in names}
    G = mean(list(centroid.values()))
    disp = {n: scl(sub(centroid[n], G), EXPLODE - 1.0) for n in names}

    # adjacency: shared coarse-vertex set of size >=3 defines a shared face
    pv = {n: unique_verts(pieces[n]) for n in names}
    pvc = {n: {ckey(v): v for v in pv[n].values()} for n in names}
    shared_faces = []          # (A, B, [verts in A coords])
    seen = set()
    for a in names:
        for b in names:
            if a >= b:
                continue
            common = set(pvc[a]) & set(pvc[b])
            if len(common) >= 3:
                verts = [pvc[a][k] for k in common]
                shared_faces.append((a, b, verts))
    print(f"found {len(shared_faces)} internal shared faces (struts)")

    all_tris = []
    # exploded pieces
    for n in names:
        d = disp[n]
        for tri in pieces[n]:
            all_tris.append(tuple(add(v, d) for v in tri))

    # struts
    gaps = []
    for a, b, verts in shared_faces:
        ordered, _ = order_polygon(verts)
        c = mean(ordered)
        Q = [add(c, scl(sub(v, c), SHRINK)) for v in ordered]   # shrunk cross-section
        uA = unit(sub(centroid[a], c))   # face -> interior of A
        uB = unit(sub(centroid[b], c))
        dA, dB = disp[a], disp[b]
        ringA = [add(add(q, dA), scl(uA, PEN)) for q in Q]   # poke into exploded A
        ringB = [add(add(q, dB), scl(uB, PEN)) for q in Q]   # poke into exploded B
        all_tris.extend(loft(ringA, ringB))
        gaps.append((a, b, norm(sub(add(c, dB), add(c, dA)))))

    os.makedirs(os.path.dirname(out_path) or ".", exist_ok=True)
    write_binary_stl(out_path, all_tris)
    print(f"wrote {out_path}: {len(all_tris)} triangles "
          f"({len(names)} pieces + {len(shared_faces)} struts)")
    gv = [g for _, _, g in gaps]
    print(f"strut spans (opened gaps): min {min(gv):.2f}  max {max(gv):.2f}  "
          f"mean {sum(gv)/len(gv):.2f}")


if __name__ == "__main__":
    main()
