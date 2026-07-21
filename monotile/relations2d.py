"""anyk-08/12 dress rehearsal, step 1: collect and classify the achievable
2D Compat relations.

A decoration's tilings depend only on its induced relation
Compat_d <= {x,y} x 4 x 4 (32 bits). This script, for one K:
  - enumerates canonical decorations, computes each one's relation mask,
  - groups decorations by relation, canonicalizes relations under C4
    conjugation (flip acts trivially on relations),
  - classifies every distinct relation at the RELATION level (box UNSAT =>
    empty / torus SAT => periodic(index) / SUSPICIOUS), no balance involved,
  - cross-checks every decoration's sweep verdict against its relation's
    class:
        unbalanced   => relation empty   (balance law x reduction, the
                                          strongest available consistency test)
        untileable6  => relation empty
        periodic i   => relation periodic with the same minimal index
                        (identical sweep order => identical minimal index)

Run:  ARENA2D_K=3 ./runpy.sh relations2d.py
Writes relations2d_K{K}.json.
"""
import json
import os
import time

import arena2d
from arena2d import (K, NPTS, NORI, ROTS, placed_vectors, compat_tables,
                     bad_tables, box_sat, lattice_classes,
                     solve_lattice_torus, canon_key)
import numpy as np


def rel_mask(compat):
    m = 0
    for ax in range(2):
        for o1 in range(NORI):
            for o2 in range(NORI):
                if compat[ax, o1, o2]:
                    m |= 1 << (ax * 16 + o1 * 4 + o2)
    return m


def mask_to_bad(m):
    bad = [[], []]
    selfbad = [[], []]
    for ax in range(2):
        for o1 in range(NORI):
            for o2 in range(NORI):
                if not (m >> (ax * 16 + o1 * 4 + o2)) & 1:
                    bad[ax].append((o1, o2))
                    if o1 == o2:
                        selfbad[ax].append(o1)
    return bad, selfbad


# C4 conjugation on relations (mirrors check_equivariance's transformation)
_key = {tuple(R.flatten()): o for o, R in enumerate(ROTS)}
_E = np.eye(2, dtype=int)


def rel_conj(m, g):
    gmap = [_key[tuple((ROTS[g] @ ROTS[o]).flatten())] for o in range(NORI)]
    out = 0
    for ax in range(2):
        w = ROTS[g] @ _E[ax]
        bx = int(np.flatnonzero(w)[0])
        sign = int(w[bx])
        for o1 in range(NORI):
            for o2 in range(NORI):
                if sign == 1:
                    bit = (m >> (bx * 16 + gmap[o1] * 4 + gmap[o2])) & 1
                else:
                    bit = (m >> (bx * 16 + gmap[o2] * 4 + gmap[o1])) & 1
                if bit:
                    out |= 1 << (ax * 16 + o1 * 4 + o2)
    return out


def rel_canon(m):
    return min(rel_conj(m, g) for g in range(NORI))


def classify_relation(m):
    bad, selfbad = mask_to_bad(m)
    sb, _ = box_sat((6, 6), bad, conf_budget=500_000)
    if sb is False:
        return {"class": "empty", "via": "box6"}
    for B in lattice_classes(32):
        if solve_lattice_torus(B, bad, selfbad, conf_budget=50_000):
            return {"class": "periodic", "index": B[0][0] * B[1][1]}
    sb8, _ = box_sat((8, 8), bad, conf_budget=5_000_000)
    if sb8 is False:
        return {"class": "empty", "via": "box8"}
    for B in lattice_classes(64):
        if B[0][0] * B[1][1] <= 32:
            continue
        if solve_lattice_torus(B, bad, selfbad, conf_budget=50_000):
            return {"class": "periodic", "index": B[0][0] * B[1][1]}
    return {"class": "SUSPICIOUS"}


def main():
    t0 = time.time()
    # verdicts from the sweep, for the cross-check
    verdicts = {}
    with open(f"arena2d_K{K}_results.jsonl") as f:
        for line in f:
            r = json.loads(line)
            verdicts[tuple(r["dec"])] = r

    groups = {}                      # canonical relation mask -> sample info
    for bits in range(1 << NPTS):
        dec = tuple(1 if (bits >> i) & 1 else -1 for i in range(NPTS))
        if canon_key(dec) != dec:
            continue
        m = rel_mask(compat_tables(placed_vectors(dec)))
        cm = rel_canon(m)
        g = groups.setdefault(cm, {"count": 0, "verdict_counts": {},
                                   "sample_dec": list(dec)})
        g["count"] += 1
        v = verdicts[dec]["verdict"]
        g["verdict_counts"][v] = g["verdict_counts"].get(v, 0) + 1
        # remember one periodic index per group for the index cross-check
        if v == "periodic":
            g.setdefault("dec_periodic_index", verdicts[dec]["index"])
    print(f"K={K}: {len(groups)} distinct relations (canonical, up to C4) "
          f"[{time.time() - t0:.0f}s]", flush=True)

    # classify each relation and cross-check
    bad_consistency = []
    for cm, g in sorted(groups.items()):
        cls = classify_relation(cm)
        g["classification"] = cls
        for v, n in g["verdict_counts"].items():
            ok = ((v in ("unbalanced", "untileable6", "untileable8")
                   and cls["class"] == "empty")
                  or (v == "periodic" and cls["class"] == "periodic"))
            if not ok:
                bad_consistency.append((cm, v, cls))
        if "dec_periodic_index" in g and cls.get("index") is not None:
            if g["dec_periodic_index"] != cls["index"]:
                bad_consistency.append((cm, "index-mismatch", cls))
    n_empty = sum(1 for g in groups.values()
                  if g["classification"]["class"] == "empty")
    n_per = sum(1 for g in groups.values()
                if g["classification"]["class"] == "periodic")
    n_sus = len(groups) - n_empty - n_per
    print(f"relations: {n_empty} empty, {n_per} periodic, {n_sus} suspicious",
          flush=True)
    print(f"consistency violations: {len(bad_consistency)}", flush=True)
    for x in bad_consistency[:10]:
        print("  VIOLATION:", x, flush=True)

    out = {"K": K, "n_relations": len(groups),
           "n_empty": n_empty, "n_periodic": n_per, "n_suspicious": n_sus,
           "consistency_violations": len(bad_consistency),
           "relations": {str(cm): {"count": g["count"],
                                   "verdicts": g["verdict_counts"],
                                   "class": g["classification"],
                                   "sample_dec": g["sample_dec"]}
                         for cm, g in sorted(groups.items())},
           "secs": round(time.time() - t0, 1)}
    with open(f"relations2d_K{K}.json", "w") as f:
        json.dump(out, f, indent=1)
    print(json.dumps({k: v for k, v in out.items() if k != "relations"}),
          flush=True)


if __name__ == "__main__":
    main()
