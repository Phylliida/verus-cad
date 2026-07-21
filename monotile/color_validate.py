"""Constructive validation of the color census (K=4 grid, 2 colors):
sample (partition, subgroup, gain-tuple) structures, build decorations,
check the direct profile (brute eqHolds over the 84 equations) equals
the structure's induced profile.

Run:  ./runpy.sh color_validate.py
"""
import itertools
import json
import random

from countclosures import close_group, subgroups, set_partitions, compose

CENSUS = json.load(open("faceeq3d_census.json"))
K = 4
TANG = list(range(-(K - 1), K, 2))
CELLS = list(itertools.product(TANG, TANG))
IDX = {c: i for i, c in enumerate(CELLS)}
N = len(CELLS)


def tau_map(tau):
    sw, s1, s2 = tau

    def ap(uv):
        u, v = (uv[1], uv[0]) if sw else uv
        return (s1 * u, s2 * v)
    return tuple((IDX[ap(c)], 1) for c in CELLS)


TWISTS = [tau_map((sw, s1, s2))
          for sw in (0, 1) for s1 in (1, -1) for s2 in (1, -1)]
G = frozenset(TWISTS)
assert len(G) == 8

EQMAPS = [(g, h, tau_map(tuple(tau))) for g, h, tau in CENSUS["equations"]]
IDENT = tuple((i, 1) for i in range(N))


def inverse(m):
    inv = [None] * len(m)
    for x, (cx, sx) in enumerate(m):
        inv[cx] = (x, sx)
    return tuple(inv)


def stabilizer_of(pattern):
    return frozenset(
        g for g in G
        if all(pattern[g[c][0]] == pattern[c] for c in range(N)))


def direct_profile(dec):
    held = set()
    for i, (g, h, m) in enumerate(EQMAPS):
        Fg, Fh = dec[g], dec[h]
        if all(Fh[m[c][0]] == Fg[c] for c in range(N)):
            held.add(i)
    return held


def random_partition(rng):
    part = [[0]]
    for f in range(1, 6):
        if rng.random() < 0.5:
            part.append([f])
        else:
            rng.choice(part).append(f)
    return part


def main():
    subs = subgroups(G, N)
    Gl = sorted(G)
    rng = random.Random(11)

    wit = {}
    for pat in itertools.product((0, 1), repeat=N):
        H = stabilizer_of(pat)
        if H not in wit:
            wit[H] = pat
        if len(wit) == len(subs):
            break
    assert len(wit) == len(subs), f"missing witnesses: {len(subs) - len(wit)}"

    coset = {}
    for H in subs:
        seen, reps = set(), []
        for g in Gl:
            key = frozenset(compose(g, h) for h in H)
            if key not in seen:
                seen.add(key)
                reps.append(g)
        coset[H] = reps

    ok = bad = 0
    for trial in range(300):
        dec = [None] * 6
        induced = set()
        for cls in random_partition(rng):
            cls = sorted(cls)
            root = cls[0]
            H = rng.choice(sorted(subs, key=len))
            rootpat = wit[H]
            a = {root: IDENT}
            for v in cls[1:]:
                a[v] = rng.choice(coset[H])
            for v in cls:
                dec[v] = tuple(rootpat[a[v][c][0]] for c in range(N))
            Hset = set(H)
            induced |= {i for i, (g, h, m) in enumerate(EQMAPS)
                        if g in cls and h in cls
                        and compose(compose(inverse(a[g]), m), a[h]) in Hset}
        got = direct_profile(tuple(dec))
        if got == induced:
            ok += 1
        else:
            bad += 1
            if bad <= 3:
                print(f"MISMATCH trial {trial}: induced {sorted(induced)} "
                      f"vs direct {sorted(got)}", flush=True)
    print(f"validation: {ok} ok, {bad} bad of 300", flush=True)


if __name__ == "__main__":
    main()
