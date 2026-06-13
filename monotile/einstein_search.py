"""
Search for an 'equivariant aperiodic Wang cube':
a single decorated cube whose 24 rotational images tile Z^3,
but (hopefully) never with a translational period.

Model
-----
Cube = [-2,2]^3. Each face is split into a 2x2 grid of sub-squares.
The 24 sub-square centers are the points with one coordinate = +/-2
and the other two in {+1,-1}. A decoration assigns a height in {-1,+1}
(bump/dent) to each of the 24 surface points.

A placement is a rotation R in SO(3,Z) (24 elements) plus a lattice
translation. The placed tile's height at world point q is d[R^-1 q].

Two cubes adjacent along axis `ax` are compatible iff at each of the 4
coinciding surface points the heights sum to 0 (bump meets dent).

Because all 24 alphabet letters are rotations of ONE shape, the induced
Z^3 subshift is automatically rotation-equivariant: this is the
'ein Stein' condition in symbolic form.
"""
import itertools
import random
import time
import numpy as np
from pysat.solvers import Glucose3

# ---------------------------------------------------------------- geometry

def rotation_group():
    """All 24 proper rotations of the cube as integer matrices."""
    mats = []
    for perm in itertools.permutations(range(3)):
        for signs in itertools.product((1, -1), repeat=3):
            M = np.zeros((3, 3), dtype=int)
            for i, (p, s) in enumerate(zip(perm, signs)):
                M[i, p] = s
            if round(np.linalg.det(M)) == 1:
                mats.append(M)
    assert len(mats) == 24
    return mats

ROTS = rotation_group()
ROT_KEY = {tuple(M.flatten()): i for i, M in enumerate(ROTS)}

def rot_index(M):
    return ROT_KEY[tuple(np.asarray(M).flatten())]

def surface_points():
    """24 sub-square centers; fixed global ordering."""
    pts = []
    for axis in range(3):
        for s in (2, -2):
            rest = [i for i in range(3) if i != axis]
            for a in (1, -1):
                for b in (1, -1):
                    p = [0, 0, 0]
                    p[axis] = s
                    p[rest[0]] = a
                    p[rest[1]] = b
                    pts.append(tuple(p))
    return pts

PTS = surface_points()
PT_INDEX = {p: i for i, p in enumerate(PTS)}

def face_point(axis, val, a, b):
    """Surface point with coord[axis]=val and remaining coords (ascending
    axis order) set to (a, b)."""
    rest = [i for i in range(3) if i != axis]
    p = [0, 0, 0]
    p[axis] = val
    p[rest[0]] = a
    p[rest[1]] = b
    return tuple(p)

# Pairs of opposing surface points across each interface, precomputed.
# Interface along +axis: A's face coord = +2, B's face coord = -2,
# tangential coords agree in world space.
IFACE_PAIRS = []
for ax in range(3):
    pairs = []
    for a in (1, -1):
        for b in (1, -1):
            pairs.append((PT_INDEX[face_point(ax, 2, a, b)],
                          PT_INDEX[face_point(ax, -2, a, b)]))
    IFACE_PAIRS.append(pairs)

# ------------------------------------------------------------- decorations

def placed_vectors(dec):
    """dec: tuple of 24 heights indexed by PTS order (identity placement).
    Returns 24 x 24 int array: row o = height vector of the tile rotated
    by ROTS[o], indexed by world surface point."""
    out = np.zeros((24, 24), dtype=np.int8)
    for o, R in enumerate(ROTS):
        for i, p in enumerate(PTS):
            q = tuple(R @ np.array(p))         # base point p lands at q
            out[o, PT_INDEX[q]] = dec[i]
    return out

def compat_tables(placed):
    """compat[ax][o1][o2] = True iff tile o1 at cell c is compatible with
    tile o2 at cell c + e_ax."""
    compat = np.zeros((3, 24, 24), dtype=bool)
    for ax in range(3):
        pairs = IFACE_PAIRS[ax]
        for o1 in range(24):
            v1 = placed[o1]
            for o2 in range(24):
                v2 = placed[o2]
                compat[ax, o1, o2] = all(v1[i] + v2[j] == 0 for i, j in pairs)
    return compat

def orbit_size(placed):
    return len({tuple(row) for row in placed})

# ------------------------------------------------------- equivariance test

def check_equivariance(compat, trials=None):
    """Physical fact: rotating a compatible pair of placed tiles by any g
    yields a compatible pair. Verifies the symbolic model respects it."""
    E = np.eye(3, dtype=int)
    for gi, g in enumerate(ROTS):
        # precompose: tile oriented o, then rotate whole space by g -> g@o
        gmap = [rot_index(g @ ROTS[o]) for o in range(24)]
        for ax in range(3):
            w = g @ E[ax]
            bx = int(np.flatnonzero(w)[0])
            sign = int(w[bx])
            for o1 in range(24):
                for o2 in range(24):
                    lhs = compat[ax, o1, o2]
                    if sign == 1:
                        rhs = compat[bx, gmap[o1], gmap[o2]]
                    else:
                        rhs = compat[bx, gmap[o2], gmap[o1]]
                    if lhs != rhs:
                        return False, (gi, ax, o1, o2)
    return True, None

# ------------------------------------------------------------- SAT tiling

def solve_tiling(dims, wrap, compat):
    """SAT check: orientations on a dims[0] x dims[1] x dims[2] block.
    wrap=True  -> torus (a satisfying assignment = fully periodic tiling)
    wrap=False -> box with free boundary (locally admissible pattern)."""
    cells = list(itertools.product(*[range(d) for d in dims]))
    idx = {c: i for i, c in enumerate(cells)}

    def var(ci, o):
        return ci * 24 + o + 1

    cnf = []
    for c in cells:
        ci = idx[c]
        cnf.append([var(ci, o) for o in range(24)])
        for o1 in range(24):
            for o2 in range(o1 + 1, 24):
                cnf.append([-var(ci, o1), -var(ci, o2)])

    for c in cells:
        ci = idx[c]
        for ax in range(3):
            nc = list(c)
            nc[ax] += 1
            if nc[ax] == dims[ax]:
                if not wrap:
                    continue
                nc[ax] = 0
            nci = idx[tuple(nc)]
            if nci == ci:                       # dims[ax] == 1, torus
                for o in range(24):
                    if not compat[ax, o, o]:
                        cnf.append([-var(ci, o)])
                continue
            bad = np.argwhere(~compat[ax])
            for o1, o2 in bad:
                cnf.append([-var(ci, int(o1)), -var(nci, int(o2))])

    with Glucose3(bootstrap_with=cnf) as s:
        sat = s.solve()
        model = s.get_model() if sat else None
    if model is None:
        return False, None
    grid = {}
    pos = set(v for v in model if v > 0)
    for c in cells:
        ci = idx[c]
        for o in range(24):
            if var(ci, o) in pos:
                grid[c] = o
    return True, grid

# Torus shapes, sorted dims suffice (axis permutations realized by group).
TORI_SMALL = sorted(
    {tuple(sorted(t)) for t in itertools.product((1, 2, 3), repeat=3)},
    key=lambda t: (t[0] * t[1] * t[2], t))
TORI_EXT = sorted(
    {tuple(sorted(t)) for t in itertools.product((1, 2, 3, 4), repeat=3)
     if max(t) == 4 and t[0] * t[1] * t[2] <= 48},
    key=lambda t: (t[0] * t[1] * t[2], t))

# ---------------------------------------------------------------- pipeline

def analyze(dec, deep=False):
    """Filter cascade. Returns (verdict, detail)."""
    placed = placed_vectors(dec)
    if orbit_size(placed) < 24:
        return "symmetric", None            # decorated cube has a symmetry
    compat = compat_tables(placed)
    for ax in range(3):
        if not compat[ax].any():
            return "untileable_axis", ax    # no pair ever fits along ax

    # cheapest periodic kills first
    for dims in TORI_SMALL:
        if dims[0] * dims[1] * dims[2] > 2:
            break
        sat, _ = solve_tiling(dims, True, compat)
        if sat:
            return "periodic", dims

    sat, _ = solve_tiling((3, 3, 3), False, compat)
    if not sat:
        return "untileable_box3", None

    for dims in TORI_SMALL:
        sat, _ = solve_tiling(dims, True, compat)
        if sat:
            return "periodic", dims

    sat, _ = solve_tiling((4, 4, 4), False, compat)
    if not sat:
        return "untileable_box4", None

    if deep:
        for dims in TORI_EXT:
            sat, _ = solve_tiling(dims, True, compat)
            if sat:
                return "periodic_ext", dims
        sat, _ = solve_tiling((5, 5, 5), False, compat)
        if not sat:
            return "untileable_box5", None
        return "SURVIVOR_DEEP", None
    return "SURVIVOR", None

def random_decoration(rng, p_flat=0.0):
    def h():
        if p_flat and rng.random() < p_flat:
            return 0
        return rng.choice((-1, 1))
    return tuple(h() for _ in range(24))

def run_search(n_samples, seed=0, p_flat=0.0, deep_survivors=True,
               verbose_every=200):
    from collections import Counter
    rng = random.Random(seed)
    funnel = {}
    torus_hits = Counter()
    survivors = []
    t0 = time.time()
    for k in range(n_samples):
        dec = random_decoration(rng, p_flat)
        verdict, detail = analyze(dec)
        if verdict == "SURVIVOR" and deep_survivors:
            verdict, detail = analyze(dec, deep=True)
        funnel[verdict] = funnel.get(verdict, 0) + 1
        if verdict.startswith("periodic"):
            torus_hits[detail] += 1
        if verdict.startswith("SURVIVOR"):
            survivors.append((dec, verdict, detail))
            print(f"  [{k}] {verdict}: dec = {dec}")
        if verbose_every and (k + 1) % verbose_every == 0:
            dt = time.time() - t0
            print(f"  ... {k+1}/{n_samples} sampled, {dt:.1f}s, "
                  f"funnel so far: {funnel}")
    return funnel, survivors, torus_hits

# --------------------------------------------------------------- self-test

def self_test():
    # 1) equivariance of the symbolic model, on a random decoration
    rng = random.Random(12345)
    dec = random_decoration(rng)
    placed = placed_vectors(dec)
    compat = compat_tables(placed)
    ok, witness = check_equivariance(compat)
    print(f"[test] equivariance: {'OK' if ok else f'FAIL {witness}'}")
    assert ok

    # 2) control: heights = sign of the face's outward coordinate.
    #    +x face all bumps, -x face all dents, etc. The identity placement
    #    is then self-compatible along every axis -> 1x1x1 torus tiles,
    #    i.e. a fully periodic tiling exists and must be detected.
    dec_p = []
    for p in PTS:
        ax = max(range(3), key=lambda i: abs(p[i]))
        dec_p.append(1 if p[ax] > 0 else -1)
    dec_p = tuple(dec_p)
    placed_p = placed_vectors(dec_p)
    compat_p = compat_tables(placed_p)
    sat, _ = solve_tiling((1, 1, 1), True, compat_p)
    print(f"[test] periodic control tiles 1x1x1 torus: "
          f"{'OK' if sat else 'FAIL'}")
    assert sat

    # 3) box solver sanity on same control
    sat, grid = solve_tiling((3, 3, 3), False, compat_p)
    print(f"[test] periodic control tiles 3x3x3 box: "
          f"{'OK' if sat else 'FAIL'}")
    assert sat

if __name__ == "__main__":
    self_test()
    for p_flat in (0.35, 0.55):
        print()
        print(f"=== hunt: 600 random decorations, heights {{-1,0,+1}}, "
              f"p_flat={p_flat} ===")
        funnel, survivors, torus_hits = run_search(600, seed=7,
                                                   p_flat=p_flat)
        print()
        print("funnel:", funnel)
        print("killer tori:", dict(torus_hits.most_common(8)))
        print("survivors:", len(survivors))
