"""Extract an actual 2-color K=4 decoration realizing canon 755's
profile, for the visualizer. Searches (partition, subgroup, gain-tuple)
structures for one whose induced profile equals canonical[755] exactly.

Run:  ./runpy.sh color_755_dec.py
"""
import itertools
import json

from color_validate import (G, EQMAPS, IDENT, inverse, stabilizer_of,
                            N, CELLS, TANG)
from countclosures import subgroups, set_partitions, compose

TARGET = frozenset(json.load(open("color3d_canonical.json"))
                   ["canonical"][755])


def induced_profile(cls, H, a, rel_eqs, Hset):
    return frozenset(
        i for i, g, h, m in rel_eqs
        if compose(compose(inverse(a[g]), m), a[h]) in Hset)


def main():
    subs = subgroups(G, N)
    Gl = sorted(G)
    wit = {}
    for pat in itertools.product((0, 1), repeat=N):
        H = stabilizer_of(pat)
        if H not in wit:
            wit[H] = pat

    coset = {}
    for H in subs:
        seen, reps = set(), []
        for g in Gl:
            key = frozenset(compose(g, h) for h in H)
            if key not in seen:
                seen.add(key)
                reps.append(g)
        coset[H] = reps

    rel_eqs_all = {}
    for size in range(1, 7):
        for cls in itertools.combinations(range(6), size):
            rel_eqs_all[cls] = [(i, g, h, m)
                                for i, (g, h, m) in enumerate(EQMAPS)
                                if g in cls and h in cls]

    found = None
    for part in set_partitions(list(range(6))):
        classes = [tuple(sorted(c)) for c in part]
        rel = [rel_eqs_all[c] for c in classes]
        # iterate structures lazily with early pruning: induced must ⊆ TARGET
        for Hs in itertools.product(subs, repeat=len(classes)):
            a_opts = []
            for cls, H in zip(classes, Hs):
                opts = []
                for gains in itertools.product(coset[H],
                                               repeat=len(cls) - 1):
                    a = {cls[0]: IDENT}
                    for v, g in zip(cls[1:], gains):
                        a[v] = g
                    opts.append(a)
                a_opts.append(opts)
            for combo in itertools.product(*a_opts):
                held = frozenset()
                for cls, H, a, re in zip(classes, Hs, combo, rel):
                    held |= induced_profile(cls, H, a, re, set(H))
                if held == TARGET:
                    found = (classes, Hs, combo)
                    break
            if found:
                break
        if found:
            break

    if not found:
        print("NO STRUCTURE FOUND?!", flush=True)
        return
    classes, Hs, combo = found
    print(f"structure: classes={classes}", flush=True)
    dec = [None] * 6
    for cls, H, a in zip(classes, Hs, combo):
        rootpat = wit[H]
        for v in cls:
            dec[v] = list(rootpat[a[v][c][0]] for c in range(N))
    # verify direct profile
    held = set()
    for i, (g, h, m) in enumerate(EQMAPS):
        Fg, Fh = dec[g], dec[h]
        if all(Fh[m[c][0]] == Fg[c] for c in range(N)):
            held.add(i)
    assert frozenset(held) == TARGET, (sorted(held), sorted(TARGET))
    print(f"direct profile matches: {len(held)} held", flush=True)
    out = {"K": 4, "T": 2, "cells": [list(c) for c in CELLS],
           "faces": dec, "profile": sorted(TARGET)}
    json.dump(out, open("color_755_decoration.json", "w"))
    print("wrote color_755_decoration.json", flush=True)


if __name__ == "__main__":
    main()
