"""anyk-08: count the consistent gain-graph closures = achievable
equation-profiles (the 3D analogue of 2D's 116).

Model: faces are nodes; a decoration groups them into classes where the
face-functions are related by gains g ∈ G = (grid isometries) × (sign);
F_v = A(g_v)·F_root with F_root having stabilizer exactly H ≤ G (chosen
subgroup). Equation E(g, h, τ) — meaning F_g = −(F_h ∘ τ) — holds iff
A(a_g)⁻¹ · A((τ,−1)) · A(a_h) ∈ A(H). Achievable-at-some-K profiles =
profiles induced by structures whose every H is feasible at large even K
(odd-K structures are a subset: they simply have smaller feasible H's).

Feasibility (large even K): H is feasible iff no element of H fixes a grid
cell with sign −1. The K=2 grid reproduces the fixed-cell pattern of every
even K (verified in faceeq3d.py's parity table), so feasibility is checked
concretely on the K=2 grid.

Gains are represented as CONCRETE signed permutations of the small even
grid's cells (composition = function composition), eliminating
convention/order bugs — the non-abelian D4×Z2 arithmetic is never written
by hand. Sanity: `--mode 2d` must reproduce the known 116 (including the
17 relations that need K=6 — this validates the genericity assumption the
count relies on).

Usage:  ./runpy.sh countclosures.py 2d     # expect 116
        ./runpy.sh countclosures.py 3d     # THE count
"""
import itertools
import json
import sys
from collections import defaultdict

# ---------------------------------------------------------------- groups


def compose(m1, m2):
    """(m1 ∘ m2) as an action on functions: (M·F)(x) = sign·F(cell(x)).
    (M1·(M2·F))(x) = s1(x)·s2(c1(x))·F(c2(c1(x)))."""
    return tuple((m2[c1][0], s1 * m2[c1][1]) for (c1, s1) in m1)


def inverse(m):
    inv = [None] * len(m)
    for x, (cx, sx) in enumerate(m):
        inv[cx] = (x, sx)
    return tuple(inv)


def identity(n):
    return tuple((x, 1) for x in range(n))


def close_group(gens, n):
    G = {identity(n)}
    frontier = list(gens)
    while frontier:
        g = frontier.pop()
        if g in G:
            continue
        G.add(g)
        for h in list(G):
            for p in (compose(g, h), compose(h, g)):
                if p not in G:
                    frontier.append(p)
    return G


def subgroups(G, n):
    """All subgroups of a small group by closure of generator subsets."""
    Gl = sorted(G)
    subs = {frozenset([identity(n)])}
    frontier = [frozenset([identity(n)])]
    while frontier:
        H = frontier.pop()
        for g in Gl:
            if g in H:
                continue
            H2 = frozenset(close_group(set(H) | {g}, n))
            if H2 not in subs:
                subs.add(H2)
                frontier.append(H2)
    return subs


def feasible_even(H):
    """No element fixes a cell with sign −1 (large-even-K criterion,
    checked on the concrete even grid)."""
    return all(not (c == x and s == -1)
               for m in H for x, (c, s) in enumerate(m))


# --------------------------------------------------------- mode setup


def setup_2d():
    """4 edge nodes; grid = 2 slots {0,1}; τ ∈ {id, mirror}; equations =
    all 10 pairs (g ≤ h) with τ = mirror (from faceeq2d)."""
    n = 2
    mirror = ((1, 1), (0, 1))
    taus = {"m": mirror, "i": identity(n)}
    neg = lambda m: tuple((c, -s) for (c, s) in m)
    eqmaps = []                      # (g, h, concrete map of (τ,-1))
    for g in range(4):
        for h in range(g, 4):
            eqmaps.append((g, h, neg(mirror)))
    gens = [neg(identity(n)), mirror]
    G = close_group(set(gens), n)
    assert len(G) == 4
    return 4, n, G, eqmaps


def setup_3d():
    """6 face nodes; grid = K=2 tangential square, cells indexed 0..3 as
    (u,v) ∈ {-1,1}²; the 84 equations from faceeq3d_census.json."""
    cells = list(itertools.product((-1, 1), (-1, 1)))
    idx = {c: i for i, c in enumerate(cells)}
    n = 4

    def tau_map(tau):
        sw, s1, s2 = tau

        def ap(uv):
            u, v = (uv[1], uv[0]) if sw else uv
            return (s1 * u, s2 * v)
        return tuple((idx[ap(c)], 1) for c in cells)

    census = json.load(open("faceeq3d_census.json"))
    eqmaps = []
    for g, h, tau in census["equations"]:
        m = tau_map(tuple(tau))
        eqmaps.append((g, h, tuple((c, -s) for (c, s) in m)))
    assert len(eqmaps) == 84
    gens = [tau_map((1, 1, 1)), tau_map((0, -1, 1)),
            tuple((c, -s) for (c, s) in identity(n))]
    G = close_group(set(gens), n)
    assert len(G) == 16, len(G)
    return 6, n, G, eqmaps


# ------------------------------------------------------- enumeration


def set_partitions(elems):
    if not elems:
        yield []
        return
    first, rest = elems[0], elems[1:]
    for part in set_partitions(rest):
        for i in range(len(part)):
            yield part[:i] + [[first] + part[i]] + part[i + 1:]
        yield [[first]] + part


def class_profiles(cls, n, G, subs_feasible, eqmaps, eq_index):
    """All achievable held-sets (as frozensets of global equation indices)
    for the faces in `cls` forming ONE gain-connected class."""
    cls = sorted(cls)
    root = cls[0]
    rel_eqs = [(i, g, h, m) for i, (g, h, m) in enumerate(eqmaps)
               if g in cls and h in cls]
    out = set()
    for H in subs_feasible:
        Hset = set(H)
        # coset representatives of G/H for the non-root gains
        seen, reps = set(), []
        for g in sorted(G):
            key = frozenset(compose(g, h) for h in H)
            if key not in seen:
                seen.add(key)
                reps.append(g)
        for gains in itertools.product(reps, repeat=len(cls) - 1):
            a = {root: identity(n)}
            for v, g in zip(cls[1:], gains):
                a[v] = g
            held = frozenset(
                i for (i, g, h, m) in rel_eqs
                if compose(compose(inverse(a[g]), m), a[h]) in Hset)
            out.add(held)
    return out


def main(mode):
    nf, n, G, eqmaps = setup_2d() if mode == "2d" else setup_3d()
    eq_index = {e: i for i, e in enumerate(eqmaps)}
    subs = subgroups(G, n)
    subs_f = [H for H in subs if feasible_even(H)]
    print(f"gain group order {len(G)}; subgroups {len(subs)}, "
          f"even-feasible {len(subs_f)}", flush=True)

    # per-subset class profile sets (classes are subsets of faces)
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
        if nparts % 25 == 0:
            print(f"  partitions {nparts}: running distinct {len(total)}",
                  flush=True)
    print(f"partitions: {nparts}", flush=True)
    print(f"DISTINCT ACHIEVABLE PROFILES ({mode}): {len(total)}", flush=True)
    if mode == "3d":
        json.dump(sorted(sorted(p) for p in total),
                  open("anyk3d_profiles.json", "w"))
        print("wrote anyk3d_profiles.json", flush=True)
    return len(total)


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "2d"
    count = main(mode)
    if mode == "2d":
        print("expected 116:", "MATCH" if count == 116 else "MISMATCH",
              flush=True)
