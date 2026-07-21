"""COLOR census: achievable equation-profiles for EQUAL-COLOR Wang cubes
(matching = patterns identical through the twist, no complement).

The gain group is the 8 grid isometries (signed swaps, sign always +1)
instead of binary's 16 (twists x complement). The 84 equations (face
pair, twist) are the same cube geometry as faceeq3d_census.json; only
the matching rule changes, so eqmaps carry +1 signs throughout.

Feasibility: a subgroup H of the twists must be realizable as the EXACT
stabilizer of some 2-color KxK pattern (then it stays realizable at all
larger K and any palette >= 2 — the achievable profile set is palette
independent for T >= 2). Verified by brute-force pattern search on
K = 2, 3, 4 grids.

Usage:  ./runpy.sh color_census.py
"""
import itertools
import json
from countclosures import (close_group, subgroups, set_partitions,
                           class_profiles)


def tau_map_cells(cells, idx, tau):
    sw, s1, s2 = tau

    def ap(uv):
        u, v = (uv[1], uv[0]) if sw else uv
        return (s1 * u, s2 * v)
    return tuple((idx[ap(c)], 1) for c in cells)


def setup_color():
    """6 face nodes; K=2 tangential grid; the 84 equations with sign +1."""
    cells = list(itertools.product((-1, 1), (-1, 1)))
    idx = {c: i for i, c in enumerate(cells)}
    n = 4
    census = json.load(open("faceeq3d_census.json"))
    eqmaps = []
    for g, h, tau in census["equations"]:
        eqmaps.append((g, h, tau_map_cells(cells, idx, tuple(tau))))
    assert len(eqmaps) == 84
    # the 8 twists: swap + one coordinate flip generate D4
    gens = [tau_map_cells(cells, idx, (1, 1, 1)),
            tau_map_cells(cells, idx, (0, -1, 1))]
    G = close_group(set(gens), n)
    assert len(G) == 8, len(G)
    return 6, n, G, eqmaps


def twist_of(m):
    """Recover (sw, s1, s2) from a concrete cell map on the (±1)^2 grid."""
    cells = list(itertools.product((-1, 1), (-1, 1)))
    idx = {c: i for i, c in enumerate(cells)}
    image = {cells[i]: cells[c] for i, (c, s) in enumerate(m) if s == 1}
    assert len(image) == 4 and all(s == 1 for _, s in m)
    sw = 1 if image[(-1, -1)][0] != -1 or (
        image[(-1, -1)] != (-1, -1) and image[(1, -1)][0] != 1) else 0
    # robust: compare against the 8 twist maps directly
    for sw_ in (0, 1):
        for s1_ in (1, -1):
            for s2_ in (1, -1):
                t = tau_map_cells(cells, idx, (sw_, s1_, s2_))
                if t == m:
                    return (sw_, s1_, s2_)
    raise ValueError("not a twist")


def stabilizer(pattern, G):
    """Exact stabilizer of a pattern (tuple of cell values) in G."""
    return frozenset(
        g for g in G
        if all(pattern[g[c][0]] == pattern[c] for c in range(len(pattern))))


def feasibility_witnesses(G):
    """Every subgroup of the 8 twists must be an exact stabilizer of a
    2-color pattern on K = 2, 3, or 4 (tangential coords -K+1..K-1).
    Subgroups are tracked as frozensets of concrete K=2 maps; lifted
    elements are mapped back to the K=2 map via twist_of for comparison."""
    subs = subgroups(G, 4)
    # canonical representative: the K=2 concrete map of each lifted element
    k2map = {}
    for m in G:
        k2map[m] = m
    missing = set(subs)
    witnesses = {}
    for K in (2, 3, 4):
        if not missing:
            break
        tang = list(range(-(K - 1), K, 2))
        cells = list(itertools.product(tang, tang))
        idx = {c: i for i, c in enumerate(cells)}
        # lift each group element to this grid via its twist, and record
        # its canonical K=2 map for subgroup comparison
        GK = []
        for m in G:
            sw, s1, s2 = twist_of(m)
            GK.append((m, tau_map_cells(cells, idx, (sw, s1, s2))))
        n = len(cells)
        if K <= 3:
            pats = itertools.product((0, 1), repeat=n)
        else:
            import random
            rng = random.Random(7)
            pats = (tuple(rng.choice((0, 1)) for _ in range(n))
                    for _ in range(300000))
        for pat in pats:
            if not missing:
                break
            H = frozenset(m for (m, gK) in GK
                          if all(pat[gK[c][0]] == pat[c]
                                 for c in range(n)))
            if H in missing:
                missing.discard(H)
                witnesses[H] = (K, pat)
    return subs, missing, witnesses


def main():
    nf, n, G, eqmaps = setup_color()
    eq_index = {e: i for i, e in enumerate(eqmaps)}
    subs, missing, witnesses = feasibility_witnesses(G)
    print(f"gain group order {len(G)}; subgroups {len(subs)}", flush=True)
    if missing:
        print(f"WARNING: {len(missing)} subgroups have no exact-stabilizer "
              f"witness on K<=4 grids — excluding them from feasibility",
              flush=True)
    subs_f = [H for H in subs if H not in missing]
    print(f"feasible subgroups: {len(subs_f)}", flush=True)

    HS = {}
    for size in range(1, nf + 1):
        for cls in itertools.combinations(range(nf), size):
            HS[cls] = class_profiles(list(cls), n, G, subs_f, eqmaps,
                                     eq_index)
        print(f"  class size {size}: max profiles "
              f"{max(len(HS[c]) for c in HS if len(c) == size)}", flush=True)

    total = set()
    nparts = 0
    for part in set_partitions(list(range(nf))):
        nparts += 1
        sets = [HS[tuple(sorted(c))] for c in part]
        for combo in itertools.product(*sets):
            total.add(frozenset().union(*combo))
        if nparts % 50 == 0:
            print(f"  partitions {nparts}: running distinct {len(total)}",
                  flush=True)
    print(f"partitions: {nparts}", flush=True)
    print(f"DISTINCT ACHIEVABLE PROFILES (color): {len(total)}", flush=True)
    json.dump(sorted(sorted(p) for p in total),
              open("color3d_profiles.json", "w"))
    print("wrote color3d_profiles.json", flush=True)


if __name__ == "__main__":
    main()
