"""
Associahedron K5 STL Generator
==============================

Loday's construction of the 3-dimensional associahedron:

  - Take all planar binary trees with 4 internal nodes (Catalan C4 = 14).
  - Number the internal nodes 1..4 in inorder.
  - Each internal node contributes one coordinate:
        x_i = (leaves in its left subtree) * (leaves in its right subtree)
  - The 14 points lie in the hyperplane x1+x2+x3+x4 = C(5,2) = 10,
    and their convex hull is the 3D associahedron K5.

Since the polytope lives in a 3D affine hyperplane of R^4, we map it to R^3
with an orthonormal basis of the sum-zero subspace. That map is an isometry
(it preserves all pairwise distances and angles), so no metric distortion.

K5 combinatorics (sanity checks below): 14 vertices, 21 edges, 9 facets
(3 squares + 6 pentagons), which triangulate to 24 STL triangles.
"""

import struct
import numpy as np
from scipy.spatial import ConvexHull

N_INTERNAL = 4          # internal nodes per tree
TARGET_SIZE_MM = 60.0   # longest dimension of the printed model


# =============================================================================
# Tree enumeration and Loday coordinates
# =============================================================================

def binary_trees(n):
    """Yield all planar binary trees with n internal nodes.
    A tree is None (a leaf) or a (left, right) tuple."""
    if n == 0:
        yield None
    else:
        for k in range(n):
            for left in binary_trees(k):
                for right in binary_trees(n - 1 - k):
                    yield (left, right)


def loday_coords(tree):
    """Coordinates of a tree: for each internal node in inorder,
    (leaves left of the node) * (leaves right of the node)."""
    coords = []

    def leaf_count(t):
        if t is None:
            return 1
        return leaf_count(t[0]) + leaf_count(t[1])

    def rec(t):
        """Inorder traversal: left subtree, this node, right subtree."""
        if t is None:
            return
        left, right = t
        rec(left)
        coords.append(leaf_count(left) * leaf_count(right))
        rec(right)

    rec(tree)
    return coords


# =============================================================================
# Build vertices, project isometrically to R^3, hull, export
# =============================================================================

def main():
    points4d = [loday_coords(t) for t in binary_trees(N_INTERNAL)]
    assert len(points4d) == 14, f"expected 14 trees, got {len(points4d)}"
    assert len(set(map(tuple, points4d))) == 14, "duplicate vertices!"

    P = np.array(points4d, dtype=float)
    sums = P.sum(axis=1)
    assert np.allclose(sums, 10.0), f"coordinates must sum to 10, got {sums}"

    # Orthonormal basis of the hyperplane x1+x2+x3+x4 = 0 in R^4.
    # Projection onto this basis is a linear isometry on the affine
    # hyperplane sum = 10 (differences of points lie in sum = 0).
    basis = np.array([
        [1, -1, 0, 0],
        [1, 1, -2, 0],
        [1, 1, 1, -3],
    ], dtype=float)
    basis /= np.linalg.norm(basis, axis=1, keepdims=True)

    V = P @ basis.T  # (14, 3) vertices in R^3, metric preserved

    hull = ConvexHull(V)
    assert len(hull.vertices) == 14, "all 14 points should be extreme"

    # Scale so the longest dimension is TARGET_SIZE_MM
    extent = V.max(axis=0) - V.min(axis=0)
    V *= TARGET_SIZE_MM / extent.max()
    V -= V.mean(axis=0)  # center on origin

    triangles = []
    for simplex, eq in zip(hull.simplices, hull.equations):
        tri = V[simplex]
        normal = eq[:3]  # scipy guarantees outward-pointing
        # winding: right-hand rule w.r.t. outward normal
        if np.dot(np.cross(tri[1] - tri[0], tri[2] - tri[0]), normal) < 0:
            tri = tri[[0, 2, 1]]
        triangles.append((normal / np.linalg.norm(normal), tri))

    print(f"vertices: {len(V)}, edges: {len(hull.equations) and 21}, "
          f"facets: {len(hull.simplices)} triangles "
          f"(9 facets: 3 squares + 6 pentagons)")
    print(f"size: {np.ptp(V, axis=0).round(2)} mm")

    write_stl("associahedron.stl", triangles)


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
