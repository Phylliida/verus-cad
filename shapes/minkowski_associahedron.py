"""
Associahedron as a Minkowski Sum — STL Generator
=================================================

A second realization of the 3D associahedron K5, this time directly in R^3
as a Minkowski sum of segments and triangles:

    P = [0, e1] + [0, e2] + [0, e3]
      + conv{0, e1, e1+e2}
      + conv{0, e2, e2+e3}
      + conv{0, e3, e3+e1}        (indices cyclic mod 3)

where P + Q = {p + q : p in P, q in Q} is the Minkowski sum
(a sum of convex sets is convex).

No projection needed this time: the sum is already 3-dimensional, and it
comes out with the K5 combinatorics — 14 vertices, 21 edges, 9 facets
(3 quadrilaterals + 6 pentagons).

Key fact used: conv(V) + conv(W) = conv{v + w : v in V, w in W}, so the
hull is computed from all 2*2*2*3*3*3 = 216 sums of summand vertices.
"""

import struct
from itertools import product

import numpy as np
from scipy.spatial import ConvexHull

TARGET_SIZE_MM = 60.0  # longest dimension of the printed model


def minkowski_vertices(summands):
    """All sums choosing one vertex from each summand."""
    return np.array([sum(choice) for choice in product(*summands)])


def main():
    e = np.eye(3)
    segments = [[np.zeros(3), e[i]] for i in range(3)]
    triangles = [[np.zeros(3), e[i], e[i] + e[(i + 1) % 3]] for i in range(3)]
    summands = segments + triangles

    pts = minkowski_vertices(summands)
    assert np.linalg.matrix_rank(pts - pts.mean(axis=0), tol=1e-9) == 3

    hull = ConvexHull(pts)
    assert len(hull.vertices) == 14, \
        f"expected 14 vertices, got {len(hull.vertices)}"

    # Scale so the longest dimension is TARGET_SIZE_MM, center on origin
    pts *= TARGET_SIZE_MM / np.ptp(pts, axis=0).max()
    pts -= pts.mean(axis=0)

    tris_out = []
    for simplex, eq in zip(hull.simplices, hull.equations):
        tri = pts[simplex]
        normal = eq[:3]  # scipy guarantees outward-pointing
        # winding: right-hand rule w.r.t. outward normal
        if np.dot(np.cross(tri[1] - tri[0], tri[2] - tri[0]), normal) < 0:
            tri = tri[[0, 2, 1]]
        tris_out.append((normal / np.linalg.norm(normal), tri))

    print(f"vertices: {len(hull.vertices)}, facets: {len(hull.simplices)} triangles "
          f"(9 facets: 3 quadrilaterals + 6 pentagons)")
    print(f"size: {np.ptp(pts[hull.vertices], axis=0).round(2)} mm")

    write_stl("minkowski_associahedron.stl", tris_out)


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
