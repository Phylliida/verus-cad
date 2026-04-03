"""
Hopf Fibration STL Generator — Print-Friendly Edition
======================================================

Generates a 3D-printable Hopf fibration designed for FDM without supports.

Design for printability:
  - Thick tubes (3mm+ diameter) so nothing is fragile
  - Fewer fibers with more spacing so they don't crowd
  - Flat base: model is cut at Z=0 with a solid base plate; fibers that
    dip below get clipped, so the print sits flat on the build plate
  - Torus axis oriented vertically: each ring arches up from the base,
    and the overhang angles stay manageable
  - Oval cross-section (wider in XY, narrower in Z) to reduce overhang
    steepness on the top arches of each ring

The math is the same: stereographic projection of Hopf fibers from S³ to R³.
Every pair of fibers is still linked with Hopf linking number 1.
"""

import numpy as np
import struct


# =============================================================================
# Hopf fibration math
# =============================================================================

def hopf_fiber(theta, phi, num_points=256):
    """
    Compute a single Hopf fiber for the point (theta, phi) on S².
    Returns (N, 3) array of points in R³ via stereographic projection.
    """
    t = np.linspace(0, 2 * np.pi, num_points, endpoint=False)

    half_theta = theta / 2.0
    cos_ht = np.cos(half_theta)
    sin_ht = np.sin(half_theta)

    x1 = cos_ht * np.cos((t + phi) / 2.0)
    x2 = cos_ht * np.sin((t + phi) / 2.0)
    x3 = sin_ht * np.cos((t - phi) / 2.0)
    x4 = sin_ht * np.sin((t - phi) / 2.0)

    denom = np.maximum(1.0 + x4, 1e-10)

    X = x1 / denom
    Y = x2 / denom
    Z = x3 / denom

    return np.column_stack([X, Y, Z])


# =============================================================================
# Tube mesh generation with oval cross-section
# =============================================================================

def parallel_transport_frames(pts, tangents):
    """Compute a smooth normal frame along a closed curve via parallel transport."""
    N = len(pts)
    normals = np.zeros_like(pts)
    binormals = np.zeros_like(pts)

    t0 = tangents[0]
    arbitrary = np.array([1.0, 0.0, 0.0]) if abs(t0[0]) < 0.9 else np.array([0.0, 1.0, 0.0])

    normal = np.cross(t0, arbitrary)
    normal /= np.linalg.norm(normal)
    binormal = np.cross(t0, normal)
    binormal /= np.linalg.norm(binormal)

    normals[0] = normal
    binormals[0] = binormal

    for i in range(1, N):
        v = np.cross(tangents[i - 1], tangents[i])
        c = np.dot(tangents[i - 1], tangents[i])
        if np.linalg.norm(v) < 1e-12:
            normals[i] = normals[i - 1]
            binormals[i] = binormals[i - 1]
        else:
            s = np.linalg.norm(v)
            v_hat = v / s
            normals[i] = (normals[i - 1] * c +
                          np.cross(v_hat, normals[i - 1]) * s +
                          v_hat * np.dot(v_hat, normals[i - 1]) * (1 - c))
            binormals[i] = np.cross(tangents[i], normals[i])
            bn = np.linalg.norm(binormals[i])
            if bn > 1e-12:
                binormals[i] /= bn

    return normals, binormals


def make_tube(center_curve, radius_h, radius_v, num_radial=16):
    """
    Generate a tube mesh around a closed curve with oval cross-section.

    radius_h: horizontal radius of cross-section (XY plane)
    radius_v: vertical radius of cross-section (Z direction)

    The oval is oriented so that the "flat" direction aligns with gravity (Z),
    reducing overhang steepness.
    """
    N = len(center_curve)
    pts = center_curve.astype(np.float64)

    # Tangent vectors (central differences, closed)
    tangents = np.zeros_like(pts)
    tangents[0] = pts[1] - pts[-1]
    tangents[-1] = pts[0] - pts[-2]
    tangents[1:-1] = pts[2:] - pts[:-2]
    norms = np.linalg.norm(tangents, axis=1, keepdims=True)
    tangents = tangents / np.maximum(norms, 1e-12)

    normals, binormals = parallel_transport_frames(pts, tangents)

    # For the oval: we want the "narrow" axis aligned with Z (gravity).
    # At each point, decompose the normal frame into a Z-component and a
    # horizontal component, then scale the Z-component by radius_v and
    # the horizontal by radius_h.
    #
    # More precisely, for each cross-section angle a, the offset is:
    #   offset = cos(a) * normal + sin(a) * binormal
    # Then we scale: the Z-component of offset gets radius_v,
    # the XY-component gets radius_h.

    angles = np.linspace(0, 2 * np.pi, num_radial, endpoint=False)
    cos_a = np.cos(angles)
    sin_a = np.sin(angles)

    vertices = np.zeros((N * num_radial, 3), dtype=np.float32)
    for i in range(N):
        for j in range(num_radial):
            offset = cos_a[j] * normals[i] + sin_a[j] * binormals[i]
            # Scale Z-component differently from XY
            xy_part = np.array([offset[0], offset[1], 0.0])
            z_part = np.array([0.0, 0.0, offset[2]])
            scaled_offset = xy_part * radius_h + z_part * radius_v
            vertices[i * num_radial + j] = (pts[i] + scaled_offset).astype(np.float32)

    # Triangle faces
    faces = np.zeros((N * num_radial * 2, 3), dtype=np.int32)
    idx = 0
    for i in range(N):
        i_next = (i + 1) % N
        for j in range(num_radial):
            j_next = (j + 1) % num_radial
            v00 = i * num_radial + j
            v01 = i * num_radial + j_next
            v10 = i_next * num_radial + j
            v11 = i_next * num_radial + j_next
            faces[idx] = [v00, v10, v01]
            faces[idx + 1] = [v01, v10, v11]
            idx += 2

    return vertices, faces


# =============================================================================
# Base plate and Z-clipping
# =============================================================================

def clip_tube_to_base(vertices, faces, z_min=0.0):
    """
    Clip tube vertices below z_min up to z_min (flatten the bottom).
    This ensures the print sits flat on the build plate.
    """
    vertices = vertices.copy()
    vertices[:, 2] = np.maximum(vertices[:, 2], z_min)
    return vertices, faces


def make_base_plate(all_vertices, z_base=0.0, thickness=1.5, margin=3.0, resolution=1.0):
    """
    Generate a base plate (rounded rectangle / ellipse) that encompasses
    all vertices that touch the build plate.

    Returns (vertices, faces) for the base plate mesh.
    """
    # Find the XY footprint of all geometry near the base
    all_pts = np.vstack(all_vertices)
    near_base = all_pts[all_pts[:, 2] < z_base + 2.0]

    if len(near_base) == 0:
        # Fallback: use all points
        near_base = all_pts

    cx = (near_base[:, 0].min() + near_base[:, 0].max()) / 2.0
    cy = (near_base[:, 1].min() + near_base[:, 1].max()) / 2.0
    rx = (near_base[:, 0].max() - near_base[:, 0].min()) / 2.0 + margin
    ry = (near_base[:, 1].max() - near_base[:, 1].min()) / 2.0 + margin

    # Create elliptical disc
    n_rings = max(3, int(max(rx, ry) / resolution))
    n_angular = 64

    verts = []
    # Center point (top and bottom)
    verts.append([cx, cy, z_base])
    verts.append([cx, cy, z_base - thickness])

    for ring in range(1, n_rings + 1):
        frac = ring / n_rings
        for k in range(n_angular):
            angle = 2 * np.pi * k / n_angular
            x = cx + frac * rx * np.cos(angle)
            y = cy + frac * ry * np.sin(angle)
            verts.append([x, y, z_base])
            verts.append([x, y, z_base - thickness])

    verts = np.array(verts, dtype=np.float32)

    # Faces
    tris = []

    # Center fan (top and bottom)
    for k in range(n_angular):
        k_next = (k + 1) % n_angular
        v_top = 2 + k * 2
        v_top_next = 2 + k_next * 2
        v_bot = 3 + k * 2
        v_bot_next = 3 + k_next * 2
        # Top face
        tris.append([0, v_top, v_top_next])
        # Bottom face (reversed winding)
        tris.append([1, v_bot_next, v_bot])

    # Ring quads (top, bottom, and sides)
    for ring in range(1, n_rings):
        for k in range(n_angular):
            k_next = (k + 1) % n_angular
            # Inner ring vertex indices
            inner_top = 2 + (ring - 1) * n_angular * 2 + k * 2
            inner_bot = inner_top + 1
            inner_top_next = 2 + (ring - 1) * n_angular * 2 + k_next * 2
            inner_bot_next = inner_top_next + 1
            # Outer ring
            outer_top = 2 + ring * n_angular * 2 + k * 2
            outer_bot = outer_top + 1
            outer_top_next = 2 + ring * n_angular * 2 + k_next * 2
            outer_bot_next = outer_top_next + 1

            # Top face quad
            tris.append([inner_top, outer_top, outer_top_next])
            tris.append([inner_top, outer_top_next, inner_top_next])
            # Bottom face quad (reversed)
            tris.append([inner_bot, outer_bot_next, outer_bot])
            tris.append([inner_bot, inner_bot_next, outer_bot_next])

    # Side wall (outer ring)
    ring = n_rings
    for k in range(n_angular):
        k_next = (k + 1) % n_angular
        outer_top = 2 + (ring - 1) * n_angular * 2 + k * 2
        outer_bot = outer_top + 1
        outer_top_next = 2 + (ring - 1) * n_angular * 2 + k_next * 2
        outer_bot_next = outer_top_next + 1
        tris.append([outer_top, outer_bot, outer_bot_next])
        tris.append([outer_top, outer_bot_next, outer_top_next])

    return verts, np.array(tris, dtype=np.int32)


# =============================================================================
# STL writing
# =============================================================================

def write_binary_stl(filename, vert_face_pairs):
    """Write binary STL from list of (vertices, faces) pairs."""
    total_triangles = sum(f.shape[0] for _, f in vert_face_pairs)

    with open(filename, 'wb') as fp:
        header = b'Hopf Fibration (support-free) - linked fibers on nested tori'
        fp.write(header[:80].ljust(80, b'\x00'))
        fp.write(struct.pack('<I', total_triangles))

        for verts, faces in vert_face_pairs:
            for tri in faces:
                v0 = verts[tri[0]].astype(np.float64)
                v1 = verts[tri[1]].astype(np.float64)
                v2 = verts[tri[2]].astype(np.float64)
                e1 = v1 - v0
                e2 = v2 - v0
                n = np.cross(e1, e2)
                norm = np.linalg.norm(n)
                if norm > 1e-12:
                    n /= norm
                fp.write(struct.pack('<3f', *n.astype(np.float32)))
                fp.write(struct.pack('<3f', *v0.astype(np.float32)))
                fp.write(struct.pack('<3f', *v1.astype(np.float32)))
                fp.write(struct.pack('<3f', *v2.astype(np.float32)))
                fp.write(struct.pack('<H', 0))

    print(f"Wrote {filename}: {total_triangles:,} triangles")


# =============================================================================
# Fiber selection and positioning
# =============================================================================

def select_fibers():
    """
    Fewer, well-spaced fibers on 2 tori for a clean, sturdy print.
    """
    fibers = []

    torus_config = [
        # Inner torus: 8 fibers
        (0.50 * np.pi, 8, 0.0),
        # Outer torus: 14 fibers
        (0.80 * np.pi, 14, 0.0),
    ]

    for theta, n_fibers, phase in torus_config:
        for k in range(n_fibers):
            phi = 2.0 * np.pi * k / n_fibers + phase
            fibers.append((theta, phi))

    return fibers


# =============================================================================
# Main
# =============================================================================

def main():
    print("Generating support-free Hopf fibration...")

    fibers = select_fibers()
    print(f"  {len(fibers)} fibers on 2 nested tori")

    # Parameters
    curve_points = 512       # smoothness of each fiber curve
    tube_radius_h = 1.6      # horizontal radius (mm) — generous for strength
    tube_radius_v = 1.2      # vertical radius (mm) — slightly squashed to reduce overhangs
    tube_radial = 16         # cross-section polygon sides
    scale = 14.0             # overall scale in mm (~170mm max dim)

    meshes = []
    all_vert_arrays = []

    for i, (theta, phi) in enumerate(fibers):
        curve = hopf_fiber(theta, phi, num_points=curve_points)
        curve = curve * scale

        # Slightly thicker inner torus for structure
        rh = tube_radius_h * (1.2 if theta < 0.6 * np.pi else 1.0)
        rv = tube_radius_v * (1.2 if theta < 0.6 * np.pi else 1.0)

        verts, faces = make_tube(curve, rh, rv, num_radial=tube_radial)

        # Find lowest Z and shift so the lowest fiber just touches Z=0
        # (we'll do a global shift after collecting all fibers)
        meshes.append((verts, faces))
        all_vert_arrays.append(verts)

    # Global shift: move everything so the lowest point is at Z = base_thickness
    all_pts = np.vstack(all_vert_arrays)
    z_min_global = all_pts[:, 2].min()
    base_thickness = 2.0  # mm

    # Shift up so bottom fibers rest on the base plate
    z_shift = -z_min_global + base_thickness

    shifted_meshes = []
    shifted_verts_list = []
    for verts, faces in meshes:
        v = verts.copy()
        v[:, 2] += z_shift
        # Clip: anything below base_thickness gets pushed up to it
        v, faces = clip_tube_to_base(v, faces, z_min=base_thickness)
        shifted_meshes.append((v, faces))
        shifted_verts_list.append(v)

    # Generate base plate
    base_verts, base_faces = make_base_plate(
        shifted_verts_list,
        z_base=base_thickness,
        thickness=base_thickness,
        margin=4.0,
        resolution=2.0
    )
    shifted_meshes.append((base_verts, base_faces))

    # Write STL
    outfile = "shapes/hopf_fibration.stl"
    write_binary_stl(outfile, shifted_meshes)

    # Stats
    total_verts = sum(v.shape[0] for v, _ in shifted_meshes)
    total_tris = sum(f.shape[0] for _, f in shifted_meshes)
    all_pts = np.vstack([v for v, _ in shifted_meshes])
    bbox_min = all_pts.min(axis=0)
    bbox_max = all_pts.max(axis=0)
    dims = bbox_max - bbox_min

    print(f"\nStats:")
    print(f"  Vertices: {total_verts:,}")
    print(f"  Triangles: {total_tris:,}")
    print(f"  Bounding box: {dims[0]:.1f} x {dims[1]:.1f} x {dims[2]:.1f} mm")
    print(f"  Tube cross-section: {tube_radius_h * 2:.1f} x {tube_radius_v * 2:.1f} mm (oval)")
    print(f"  Base plate thickness: {base_thickness:.1f} mm")
    print(f"\n  Printability:")
    print(f"    - Flat base, no supports needed")
    print(f"    - Oval tube cross-section reduces overhang angles")
    print(f"    - {tube_radius_h * 2:.1f}mm wide tubes for strength")
    print(f"\n  Topology: {len(fibers)} fibers, every pair linked (Hopf linking number 1)")


if __name__ == "__main__":
    main()
