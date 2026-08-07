"""The one-edge obstruction: solver-free verification and dissection.

corner3d_core_hunt.py found that the 4x4 mid-slice UNSAT core is just
the central 2x2 block of cubes — i.e. the 4 cubes around ONE lattice
edge (the edge from (2,2,0) to (2,2,1)), with mark agreement at every
lattice vertex shared by >= 2 of them (the central vertex, 4-wise, plus
4 pairwise edge vertices, on both planes). Since vertex glue in any #10
tiling implies all these agreements, UNSAT of this 4-cube system proves
#10 (and #11) cannot tile Z^3.

This script verifies the core with pure brute force (12^4 = 20736
assignments, no SAT solver), dissects which agreements are essential,
and prints near-miss structure for the human proof.

Run:  ./runpy.sh corner3d_edge.py
"""
import itertools
import sys

sys.argv = ["corner3d.py"]
import corner3d as C
from corner3d_transfer import PAIRS, marked_by

# the 4 cubes around the edge from (2,2,0) to (2,2,1)
CUBES = [(1, 1), (1, 2), (2, 1), (2, 2)]

# lattice vertices of one plane shared by >= 2 of the 4 cubes,
# with their incident cube list (both planes have the same x,y)
SHARED = {}
for x, y in itertools.product(range(4), repeat=2):
    inc = [(i, j) for (i, j) in CUBES if i in (x - 1, x) and j in (y - 1, y)]
    if len(inc) >= 2:
        SHARED[(x, y)] = inc
print("shared vertices (per plane):",
      {v: len(c) for v, c in SHARED.items()})


def marks(cube, pair_j, kpar):
    """The 8 corner marks (0/1) of a cube in the layer of parity kpar."""
    cp = (cube[0] + cube[1] + kpar) % 2
    return tuple(1 if marked_by(e, PAIRS[cp][pair_j], cp) else 0
                 for e in range(8))


def corner_of(cube, x, y, plane):
    return C.cidx((x - cube[0], y - cube[1], plane))


def agreements_ok(assign, kpar, skip=None):
    """assign: dict cube -> pair index. Check all shared-vertex mark
    agreements on both planes, optionally skipping one (vertex, plane)."""
    mk = {c: marks(c, j, kpar) for c, j in assign.items()}
    for (x, y), inc in SHARED.items():
        for plane in (0, 1):
            if skip == ((x, y), plane):
                continue
            vals = {mk[c][corner_of(c, x, y, plane)] for c in inc}
            if len(vals) > 1:
                return False
    return True


for kpar in (0, 1):
    total = 0
    survivors = []
    for js in itertools.product(range(12), repeat=4):
        total += 1
        assign = dict(zip(CUBES, js))
        if agreements_ok(assign, kpar):
            survivors.append(assign)
    print(f"kpar={kpar}: {total} assignments, {len(survivors)} survive "
          f"all agreements  {'<== UNSAT confirmed' if not survivors else ''}")

    # which agreements are essential? drop each one in turn
    essential = 0
    for key in [(v, p) for v in SHARED for p in (0, 1)]:
        n = 0
        for js in itertools.product(range(12), repeat=4):
            assign = dict(zip(CUBES, js))
            if agreements_ok(assign, kpar, skip=key):
                n += 1
        if n == 0:
            essential += 1
    print(f"  agreements that are individually essential "
          f"(dropping keeps UNSAT): {essential} of {2 * len(SHARED)}")

    # relax ONLY the 4-wise central agreement (keep the 8 pair agreements)
    n = 0
    central_count_dist = {}
    central_pattern_dist = {}
    for js in itertools.product(range(12), repeat=4):
        assign = dict(zip(CUBES, js))
        mk = {c: marks(c, j, kpar) for c, j in assign.items()}
        pair_ok = all(
            len({mk[c][corner_of(c, x, y, p)] for c in inc}) == 1
            for (x, y), inc in SHARED.items() if (x, y) != (2, 2)
            for p in (0, 1))
        if pair_ok:
            n += 1
            for p in (0, 1):
                pat = tuple(mk[c][corner_of(c, 2, 2, p)] for c in CUBES)
                central_count_dist[sum(pat)] = \
                    central_count_dist.get(sum(pat), 0) + 1
                central_pattern_dist[pat] = \
                    central_pattern_dist.get(pat, 0) + 1
    print(f"  assignments satisfying the 8 pair agreements "
          f"(central dropped): {n}")
    print(f"  central-vertex mark-count distribution "
          f"(over both planes): {dict(sorted(central_count_dist.items()))}")
    print(f"  central mark patterns "
          f"(cubes ordered {CUBES}): "
          f"{dict(sorted(central_pattern_dist.items()))}")
