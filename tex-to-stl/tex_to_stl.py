#!/usr/bin/env python3
"""Convert the TikZ 3D dissection figure into an STL mesh.

The .tex file defines named 3D points via ``\\coordinate (name) at (x,y,z);``
and draws polygonal faces with two macros:

    \\Carre{a}{b}{c}{d}{color}            quadrilateral (4 vertices)
    \\Pentagone{a}{b}{c}{d}{e}{color}     pentagon      (5 vertices)

Faces are grouped into "pieces" delimited by ``% ... <id> - <id>`` comment
headers. This script parses the coordinates and faces (only inside the
tikzpicture environment, so the \\newcommand definitions in the preamble are
ignored), triangulates every polygon with a fan triangulation, and writes an
STL file.

Many of the quad/pentagon faces are *non-planar* (skew). A skew polygon can be
folded along different diagonals; the fold we pick is its "crease". To stay
watertight, each *distinct* face is triangulated once (keyed by its vertex set)
and reused everywhere it appears, so a wall shared by two cells gets the same
crease from both sides and the cells meet with no gap. Boundary faces fold
convexly outward; internal walls fold about the midpoint of the two cells they
separate. See ``shared_triangulation`` and the ``--crease`` flag.

Outputs:
    out.stl            the closed outer SHELL of the whole solid -- a single
                       watertight 2-manifold (internal walls dropped).
    --split            one closed STL per piece; shared creases make them tile
                       the shell exactly (they mate watertight).
    --assembly         all faces in one file (internal walls kept, gap-free but
                       non-manifold) -- use to keep every cell in one model.

Usage:
    python tex_to_stl.py figure.tex out.stl              # watertight shell
    python tex_to_stl.py figure.tex out.stl --split      # + one STL per piece
    python tex_to_stl.py figure.tex out.stl --assembly   # + all-faces model
    python tex_to_stl.py figure.tex out.stl --ascii      # ASCII instead of binary
    python tex_to_stl.py figure.tex out.stl --crease=fan # convex|concave|fan
"""

import math
import re
import struct
import sys
from collections import Counter, defaultdict
from fractions import Fraction

# ---------------------------------------------------------------------------
# Parsing
# ---------------------------------------------------------------------------

_TIKZ_RE = re.compile(r"\\begin\{tikzpicture\}(.*?)\\end\{tikzpicture\}", re.DOTALL)
_COORD_RE = re.compile(r"\\coordinate\s*\(([^)]+)\)\s*at\s*\(([^)]+)\)")
_CARRE_RE = re.compile(r"\\Carre((?:\s*\{[^}]*\}){5})")
_PENT_RE = re.compile(r"\\Pentagone((?:\s*\{[^}]*\}){6})")
_ARG_RE = re.compile(r"\{([^}]*)\}")
# A piece header looks like "... 432 - 111" or "... 542 -221" inside a comment.
_PIECE_RE = re.compile(r"(\d+)\s*-\s*(\d+)")


def parse_value(token):
    """Parse a coordinate component: integer, decimal, or fraction like -7/2."""
    token = token.strip()
    if "/" in token:
        num, den = token.split("/")
        return float(Fraction(int(num), int(den)))
    return float(token)


def parse_tex(text):
    """Return (coords, faces).

    coords: {name: (x, y, z)}
    faces:  list of (vertex_names, color, piece_label)
    """
    m = _TIKZ_RE.search(text)
    block = m.group(1) if m else text  # fall back to whole file

    coords = {}
    faces = []
    current_piece = "unknown"

    for raw in block.splitlines():
        code, sep, comment = raw.partition("%")

        if sep:  # update the current piece label from comment headers
            pm = _PIECE_RE.search(comment)
            if pm:
                current_piece = f"{pm.group(1)}-{pm.group(2)}"

        cm = _COORD_RE.search(code)
        if cm:
            name = cm.group(1).strip()
            comps = [parse_value(v) for v in cm.group(2).split(",")]
            coords[name] = tuple(comps)
            continue

        for fm in _CARRE_RE.finditer(code):
            args = _ARG_RE.findall(fm.group(1))
            faces.append((args[:4], args[4], current_piece))
        for fm in _PENT_RE.finditer(code):
            args = _ARG_RE.findall(fm.group(1))
            faces.append((args[:5], args[5], current_piece))

    return coords, faces


# ---------------------------------------------------------------------------
# Geometry
# ---------------------------------------------------------------------------

def _sub(p, q):
    return (p[0] - q[0], p[1] - q[1], p[2] - q[2])


def _cross(u, v):
    return (
        u[1] * v[2] - u[2] * v[1],
        u[2] * v[0] - u[0] * v[2],
        u[0] * v[1] - u[1] * v[0],
    )


def _normal(a, b, c):
    n = _cross(_sub(b, a), _sub(c, a))
    length = math.sqrt(n[0] ** 2 + n[1] ** 2 + n[2] ** 2)
    if length == 0.0:
        return (0.0, 0.0, 0.0)
    return (n[0] / length, n[1] / length, n[2] / length)


def _tetra_vol(g, a, b, c):
    """Absolute volume of the tetrahedron (g, a, b, c)."""
    ax, ay, az = a[0] - g[0], a[1] - g[1], a[2] - g[2]
    bx, by, bz = b[0] - g[0], b[1] - g[1], b[2] - g[2]
    cx, cy, cz = c[0] - g[0], c[1] - g[1], c[2] - g[2]
    det = (ax * (by * cz - bz * cy)
           - ay * (bx * cz - bz * cx)
           + az * (bx * cy - by * cx))
    return abs(det) / 6.0


def _fan(pts, apex):
    """Triangulate polygon `pts` as a fan rooted at vertex index `apex`."""
    n = len(pts)
    return [(pts[apex], pts[(apex + i) % n], pts[(apex + i + 1) % n])
            for i in range(1, n - 1)]


def _choose_apex(pts, ref, crease="convex"):
    """Pick the fan apex (= crease) for a polygon given a reference point.

    A skew polygon can be folded several ways; the diagonal we pick is the
    *crease*. The candidate fans differ in the volume of the cone they sweep
    from `ref`:

        crease="convex"  -> fold that bulges AWAY from `ref` (maximal cone
                            volume). Keeps the surface locally convex.
        crease="concave" -> the opposite fold (minimal cone volume).
        crease="fan"     -> naive fan from vertex 0 (original behaviour).

    The candidate fans (one per apex) enumerate every triangulation of a
    quad (2 distinct) and every triangulation of a pentagon (5 = Catalan_3).
    """
    if len(pts) <= 3 or crease == "fan":
        return 0
    best = None
    for apex in range(len(pts)):
        vol = sum(_tetra_vol(ref, *t) for t in _fan(pts, apex))
        score = vol if crease == "convex" else -vol
        if best is None or score > best[0]:
            best = (score, apex)
    return best[1]


def triangulate_face(pts, ref, crease="convex"):
    """Triangulate one (possibly non-planar) polygon about reference `ref`."""
    return _fan(pts, _choose_apex(pts, ref, crease))


def _piece_centroids(coords, faces):
    verts_by_piece = defaultdict(set)
    for verts, _color, piece in faces:
        verts_by_piece[piece].update(verts)
    centroids = {}
    for piece, names in verts_by_piece.items():
        pts = [coords[v] for v in names if v in coords]
        n = len(pts)
        centroids[piece] = tuple(sum(p[i] for p in pts) / n for i in range(3))
    return centroids


def shared_triangulation(coords, faces, crease="convex"):
    """Triangulate each *distinct* face once and reuse it everywhere.

    Faces are keyed by their vertex SET, so a wall shared by two pieces (even
    if the two pieces list it rotated/reflected) gets one identical set of
    triangles — i.e. the two cells share the crease and meet watertight.

    The interior reference for each face is the centroid of all pieces that
    contain it: a single cell's centroid for a boundary face (so it folds
    convexly outward), or the midpoint of the two cells for an internal wall
    (a neutral, order-independent choice).

    Returns:
        tri_by_key   : {frozenset(verts) -> [(vname, vname, vname), ...]}
        pieces_by_key: {frozenset(verts) -> {piece, ...}}
    """
    centroids = _piece_centroids(coords, faces)
    pieces_by_key = defaultdict(set)
    order_by_key = {}
    for verts, _color, piece in faces:
        key = frozenset(verts)
        pieces_by_key[key].add(piece)
        order_by_key.setdefault(key, list(verts))

    tri_by_key = {}
    missing = set()
    for key, vorder in order_by_key.items():
        try:
            pts = [coords[v] for v in vorder]
        except KeyError as exc:
            missing.add(exc.args[0])
            continue
        pcs = pieces_by_key[key]
        ref = tuple(sum(centroids[p][i] for p in pcs) / len(pcs)
                    for i in range(3))
        apex = _choose_apex(pts, ref, crease)
        n = len(vorder)
        tri_by_key[key] = [
            (vorder[apex], vorder[(apex + i) % n], vorder[(apex + i + 1) % n])
            for i in range(1, n - 1)
        ]
    if missing:
        print(f"warning: undefined vertices referenced: {sorted(missing)}",
              file=sys.stderr)
    return tri_by_key, pieces_by_key


def _names_to_coords(name_tris, coords):
    return [tuple(coords[v] for v in tri) for tri in name_tris]


def edge_manifold_report(triangles, ndigits=6):
    """Return (boundary_edge_count, {use_count: num_edges}) for a triangle soup.

    A closed, watertight, 2-manifold surface has every edge used exactly
    twice and zero boundary (odd-use) edges.
    """
    def key(p):
        return (round(p[0], ndigits), round(p[1], ndigits), round(p[2], ndigits))
    counts = defaultdict(int)
    for a, b, c in triangles:
        for u, v in ((a, b), (b, c), (c, a)):
            counts[frozenset((key(u), key(v)))] += 1
    boundary = sum(1 for n in counts.values() if n % 2 == 1)
    dist = dict(sorted(Counter(counts.values()).items()))
    return boundary, dist


# ---------------------------------------------------------------------------
# STL writers
# ---------------------------------------------------------------------------

def write_binary_stl(path, triangles):
    with open(path, "wb") as f:
        f.write(b"\0" * 80)                       # 80-byte header
        f.write(struct.pack("<I", len(triangles)))
        for a, b, c in triangles:
            n = _normal(a, b, c)
            f.write(struct.pack("<12fH", *n, *a, *b, *c, 0))


def write_ascii_stl(path, triangles, name="dissection"):
    with open(path, "w") as f:
        f.write(f"solid {name}\n")
        for a, b, c in triangles:
            n = _normal(a, b, c)
            f.write(f"  facet normal {n[0]:.6e} {n[1]:.6e} {n[2]:.6e}\n")
            f.write("    outer loop\n")
            for v in (a, b, c):
                f.write(f"      vertex {v[0]:.6e} {v[1]:.6e} {v[2]:.6e}\n")
            f.write("    endloop\n")
            f.write("  endfacet\n")
        f.write(f"endsolid {name}\n")


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main(argv):
    args = [a for a in argv[1:] if not a.startswith("--")]
    flags = {a for a in argv[1:] if a.startswith("--")}
    if len(args) < 2:
        print(__doc__)
        return 1

    in_path, out_path = args[0], args[1]
    ascii_mode = "--ascii" in flags
    split = "--split" in flags
    assembly = "--assembly" in flags
    crease = "convex"
    for f in flags:
        if f.startswith("--crease="):
            crease = f.split("=", 1)[1]
    if crease not in ("convex", "concave", "fan"):
        print(f"error: --crease must be convex|concave|fan, got {crease!r}")
        return 1

    def emit(path, tris, name="dissection"):
        if ascii_mode:
            write_ascii_stl(path, tris, name=name)
        else:
            write_binary_stl(path, tris)

    with open(in_path) as f:
        text = f.read()

    coords, faces = parse_tex(text)

    # One triangulation per distinct face -> shared creases -> watertight seams.
    tri_by_key, pieces_by_key = shared_triangulation(coords, faces, crease)

    # The main output is the closed outer SHELL: faces belonging to exactly one
    # piece (the boundary of the union). With shared creases this is a single
    # watertight 2-manifold.
    shell = []
    for key, pcs in pieces_by_key.items():
        if len(pcs) == 1:
            shell.extend(_names_to_coords(tri_by_key[key], coords))
    emit(out_path, shell)

    boundary_edges, dist = edge_manifold_report(shell)
    watertight = boundary_edges == 0 and set(dist) <= {2}

    # Report
    pts_all = [p for t in shell for p in t]
    xs = [p[0] for p in pts_all]; ys = [p[1] for p in pts_all]
    zs = [p[2] for p in pts_all]
    print(f"coordinates  : {len(coords)}")
    print(f"faces        : {len(faces)} "
          f"({sum(1 for f in faces if len(f[0]) == 4)} quads, "
          f"{sum(1 for f in faces if len(f[0]) == 5)} pentagons); "
          f"{len(tri_by_key)} distinct, "
          f"{sum(1 for k in pieces_by_key if len(pieces_by_key[k]) > 1)} "
          f"internal walls")
    print(f"crease rule  : {crease}")
    print(f"shell        : {len(shell)} triangles -> {out_path} "
          f"({'ASCII' if ascii_mode else 'binary'} STL)")
    if pts_all:
        print(f"bounding box : x[{min(xs):g},{max(xs):g}] "
              f"y[{min(ys):g},{max(ys):g}] z[{min(zs):g},{max(zs):g}]")
    print(f"watertight   : {watertight}  "
          f"(boundary edges: {boundary_edges}, edge use-counts: {dist})")

    stem = out_path[:-4] if out_path.lower().endswith(".stl") else out_path

    if assembly:
        # Every face (internal walls included), shared creases. Gap-free but
        # non-manifold (internal walls appear twice). Useful to keep all cells.
        asm = []
        for verts, _color, _piece in faces:
            asm.extend(_names_to_coords(tri_by_key[frozenset(verts)], coords))
        emit(f"{stem}_assembly.stl", asm)
        print(f"assembly     : {len(asm)} triangles -> {stem}_assembly.stl")

    if split:
        groups = defaultdict(list)
        for verts, _color, piece in faces:
            groups[piece].extend(
                _names_to_coords(tri_by_key[frozenset(verts)], coords))
        for piece, tris in sorted(groups.items()):
            p = f"{stem}_{piece}.stl"
            emit(p, tris, name=f"piece_{piece}")
            be, _ = edge_manifold_report(tris)
            print(f"  piece {piece:>8}: {len(tris):3d} triangles -> {p}"
                  f"  ({'closed' if be == 0 else f'{be} open edges'})")

    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
