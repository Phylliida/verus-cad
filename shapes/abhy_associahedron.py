"""
ABHY Associahedron (type A3) STL Generator
==========================================

The 14 vertices of U_c from Example 2.4 (p. 6) of

  Bazier-Matte, Chapelier-Laget, Douville, Mousavand, Thomas, Yildirim,
  "ABHY Associahedra and Newton Polytopes of F-polynomials for finite
  type cluster algebras"

for the quiver Q = 1 -> 2 <- 3 with all deformation parameters c_ij = 1.

Each vertex has 9 coordinates p_ij, one per node of the Auslander-Reiten
quiver, stored here in the order they appear in the paper's diagrams:

    (p01, p03, p02, p11, p13, p12, p21, p23, p22)

The polytope A_c in R^3 is obtained by the projection pi which keeps the
final slice (the three rightmost entries) in the order determined by the
g-vectors: pi = (p23, p22, p21).  (This is the paper's convention; e.g.
the first vertex below has pi = (3,4,3), as stated after Lemma 5.1.)

As a sanity check, every transcribed vertex is verified against the
c-deformed mesh relations with c = (1,...,1):

    p01 + p11 = p02 + 1
    p03 + p13 = p02 + 1
    p02 + p12 = p11 + p13 + 1
    p11 + p21 = p12 + 1
    p13 + p23 = p12 + 1
    p12 + p22 = p21 + p23 + 1
"""

import struct

import numpy as np
from scipy.spatial import ConvexHull

TARGET_SIZE_MM = 60.0  # longest dimension of the printed model

# The 14 vertices of U_c, coordinates (p01, p03, p02, p11, p13, p12, p21, p23, p22)
VERTICES_9D = [
    (0, 0, 0, 1, 1, 3, 3, 3, 4),
    (0, 1, 0, 1, 0, 2, 2, 3, 4),
    (1, 0, 0, 0, 1, 2, 3, 2, 4),
    (1, 1, 0, 0, 0, 1, 2, 2, 4),
    (2, 2, 1, 0, 0, 0, 1, 1, 3),
    (2, 3, 2, 1, 0, 0, 0, 1, 2),
    (3, 2, 2, 0, 1, 0, 1, 0, 2),
    (3, 3, 3, 1, 1, 0, 0, 0, 1),
    (3, 3, 4, 2, 2, 1, 0, 0, 0),
    (3, 0, 2, 0, 3, 2, 3, 0, 2),
    (0, 3, 2, 3, 0, 2, 0, 3, 2),
    (3, 0, 4, 2, 5, 4, 3, 0, 0),
    (0, 3, 4, 5, 2, 4, 0, 3, 0),
    (0, 0, 4, 5, 5, 7, 3, 3, 0),
]


def check_mesh_relations(p):
    """Verify the c-deformed mesh relations with all c_ij = 1."""
    p01, p03, p02, p11, p13, p12, p21, p23, p22 = p
    return (
        p01 + p11 == p02 + 1 and
        p03 + p13 == p02 + 1 and
        p02 + p12 == p11 + p13 + 1 and
        p11 + p21 == p12 + 1 and
        p13 + p23 == p12 + 1 and
        p12 + p22 == p21 + p23 + 1
    )


def main():
    for p in VERTICES_9D:
        assert check_mesh_relations(p), f"mesh relations fail at {p}"

    # pi keeps the final slice in g-vector order: (p23, p22, p21)
    V = np.array([(p[7], p[8], p[6]) for p in VERTICES_9D], dtype=float)

    hull = ConvexHull(V)
    assert len(hull.vertices) == 14, "all 14 points should be extreme"

    # Scale so the longest dimension is TARGET_SIZE_MM, center on origin
    V *= TARGET_SIZE_MM / np.ptp(V, axis=0).max()
    V -= V.mean(axis=0)

    tris_out = []
    for simplex, eq in zip(hull.simplices, hull.equations):
        tri = V[simplex]
        normal = eq[:3]  # scipy guarantees outward-pointing
        # winding: right-hand rule w.r.t. outward normal
        if np.dot(np.cross(tri[1] - tri[0], tri[2] - tri[0]), normal) < 0:
            tri = tri[[0, 2, 1]]
        tris_out.append((normal / np.linalg.norm(normal), tri))

    print(f"vertices: {len(V)}, facets: {len(hull.simplices)} triangles")
    print(f"size: {np.ptp(V, axis=0).round(2)} mm")

    write_stl("abhy_associahedron.stl", tris_out)


def write_stl(path, triangles):
    with open(path, "wb") as f:
        f.write(b"\0" * 80)
        f.write(struct.pack("<I", len(triangles)))
        for normal, tri in triangles:
            f.write(struct.pack("<3f", *normal))
            for v in tri:
                f.write(struct.pack("<3f", *v))
            f.write(struct.pack("<H", 0))
    print(f"wrote {path}")


if __name__ == "__main__":
    main()
