"""Completeness check for the color census: random 2-color decorations
(K = 2, 3 grids) must ALL have their direct profile inside the census
set (color3d_profiles.json). Undercounting is fatal; overcounting is
harmless — this is the direction that matters.

Run:  ./runpy.sh color_complete_check.py [nsample]
"""
import itertools
import json
import random
import sys

CENSUS = json.load(open("faceeq3d_census.json"))
EQT = [(g, h, tuple(tau)) for g, h, tau in CENSUS["equations"]]


def lift(cells, idx, tau):
    sw, s1, s2 = tau

    def ap(uv):
        u, v = (uv[1], uv[0]) if sw else uv
        return (s1 * u, s2 * v)
    return tuple((idx[ap(c)], 1) for c in cells)


def direct_profile(dec, K):
    tang = list(range(-(K - 1), K, 2))
    cells = list(itertools.product(tang, tang))
    idx = {c: i for i, c in enumerate(cells)}
    maps = [(g, h, lift(cells, idx, tau)) for g, h, tau in EQT]
    held = set()
    n = len(cells)
    for i, (g, h, m) in enumerate(maps):
        Fg, Fh = dec[g], dec[h]
        if all(Fh[m[c][0]] == Fg[c] for c in range(n)):
            held.add(i)
    return held


def main():
    nsample = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
    census = {tuple(p) for p in json.load(open("color3d_profiles.json"))}
    rng = random.Random(5)
    bad = 0
    for t in range(nsample):
        K = rng.choice((2, 3))
        n = K * K
        dec = tuple(tuple(rng.choice((0, 1)) for _ in range(n))
                    for _ in range(6))
        prof = tuple(sorted(direct_profile(dec, K)))
        if prof not in census:
            bad += 1
            if bad <= 3:
                print(f"MISSING profile (K={K}): {prof}", flush=True)
    print(f"completeness: {nsample} sampled, {bad} missing", flush=True)


if __name__ == "__main__":
    main()
