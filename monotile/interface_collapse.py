"""The collapse test: how rigid is compat_S for each catalogue
pattern S?

Every tiling of every decoration realizing S lives inside compat_S.
We compute, per pattern:

  * the VIABLE CORE: letters surviving iterated removal of any letter
    lacking an in- AND out-neighbour along EVERY axis (necessary to
    appear in any Z^3 tiling of compat_S);
  * per-axis out-degree profile within the core -- out-degree 1
    everywhere means the axis dynamics are DETERMINISTIC (a
    permutation of the core), the strongest possible collapse;
  * per-axis shortest cycle lengths in the core;
  * a witness-index heuristic: product over axes of shortest cycles.

If cores are small and (near-)deterministic, the Matching Collapse
lemma reduces to finite case analysis over this table.
"""
import json

import numpy as np

from arena2 import PAIRS, PATTERN_FILE
from catalogue_anatomy import compat_of


def viable_core(compat):
    alive = set(range(24))
    changed = True
    while changed:
        changed = False
        for o in list(alive):
            ok = True
            for ax in range(3):
                if not any(compat[ax, o, b] for b in alive):
                    ok = False
                    break
                if not any(compat[ax, a, o] for a in alive):
                    ok = False
                    break
            if not ok:
                alive.discard(o)
                changed = True
    return alive


def shortest_cycle(core, succ):
    best = None
    for s in core:
        dist = {s: 0}
        frontier = [s]
        d = 0
        hit = None
        while frontier and hit is None:
            d += 1
            nxt = []
            for x in frontier:
                for y in succ[x]:
                    if y == s:
                        hit = d
                        break
                    if y not in dist:
                        dist[y] = d
                        nxt.append(y)
                if hit is not None:
                    break
            frontier = nxt
        if hit is not None and (best is None or hit < best):
            best = hit
    return best


if __name__ == "__main__":
    with open(PATTERN_FILE) as f:
        data = json.load(f)
    pats = [frozenset((min(a, b), max(a, b)) for a, b in pl)
            for pl in data["patterns"]]

    print(" id |S|  core  per-axis: |edges| outdeg-profile  min-cycles"
          "  idx-bound")
    for i, S in enumerate(pats):
        compat = compat_of(S)
        core = viable_core(compat)
        if not core:
            print(f" {i:2d} {len(S):3d}  EMPTY CORE ?!")
            continue
        cyc = []
        info = []
        for ax in range(3):
            succ = {o: [b for b in core if compat[ax, o, b]]
                    for o in core}
            outs = sorted(len(v) for v in succ.values())
            profile = (f"det" if set(outs) == {1}
                       else f"{outs[0]}..{outs[-1]}")
            m = shortest_cycle(core, succ)
            cyc.append(m)
            ne = sum(len(v) for v in succ.values())
            info.append(f"{ne:3d}e {profile:5s} c={m}")
        bound = None
        if all(c is not None for c in cyc):
            bound = cyc[0] * cyc[1] * cyc[2]
        tag = "MATCHING" if len(S) == 27 else ""
        print(f" {i:2d} {len(S):3d}  {len(core):2d}    "
              f"{' | '.join(info)}   ~{bound}  {tag}")
