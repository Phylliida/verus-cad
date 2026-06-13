"""Pattern saturation: enumerate ALL minimal periodic patterns up to a
lattice index bound, instead of only the ones CEGIS stumbled into.

For each lattice class B (rotation-conjugacy reps from skew, ascending
index), build a SAT instance with the decoration SYMBOLIC:

    one-hot torus orientation field x[cell, o]
  + H-bits with e_{ab} <-> H_a xor H_b
  + adjacency: every coinciding point-pair must be complementary
    (pairs with a == b forbid the orientation pair outright)
  + Lemma-A balance per orbit (only balanced-realizable patterns are
    useful to the synthesizer)

Each solution is a valid torus tiling for EVERY decoration realizing
its pattern S; emit S, block S and its 24 conjugates, repeat to UNSAT.
UNSAT = class fully saturated (every balanced-realizable periodic
pattern of this class is in the library). Known patterns (the existing
file + everything found so far) are pre-blocked, so only novel minimal
patterns surface.

Soundness of blocking each emitted S in the synthesizer: any
decoration realizing S admits the (B, qgrid) torus tiling by
construction -- it is periodic. Blocking is exact, never lossy.

Output: saturation_results.jsonl (one line per pattern / per class
summary) and, at the end, a merge into arena2_patterns.json.

Usage:  python3 saturate.py [max_index=8] [max_pat_per_class=1000]
                            [class_time_cap_s=300]
"""
import itertools
import json
import sys
import time

from pysat.solvers import Cadical195
from pysat.card import CardEnc, EncType

from arena2 import (NPTS, PAIRS, PERM, PATTERN_FILE, reduce_vec,
                    pattern_pairs_lattice)
from skew import lattice_classes


def stamp():
    return time.strftime("%H:%M:%S")


def orbits_of_points():
    orbits, seen = [], set()
    for i in range(NPTS):
        if i in seen:
            continue
        orb = {PERM[g][i] for g in range(24)}
        seen |= orb
        orbits.append(sorted(orb))
    return orbits


ORBITS = orbits_of_points()


def conjugates(S):
    out = []
    for g in range(24):
        pg = PERM[g]
        out.append(frozenset((min(pg[a], pg[b]), max(pg[a], pg[b]))
                             for a, b in S))
    return out


def enumerate_class(B, blocked, logf, max_pat, time_cap):
    """Returns (novel_patterns, complete?, n_solutions)."""
    a, d, f = B[0][0], B[1][1], B[2][2]
    cells = [(x, y, z) for x in range(a) for y in range(d)
             for z in range(f)]
    cidx = {c: i for i, c in enumerate(cells)}
    xbase = NPTS
    nv = NPTS + len(cells) * 24
    evmap = {}
    cnf = []
    holder = [None]                          # live solver, once built

    def xvar(ci, o):
        return xbase + ci * 24 + o + 1

    def evar(p, q):
        # defs must reach the SOLVER: clauses appended to the python
        # list after bootstrap are invisible, leaving any blocking
        # clause over a fresh e-var inert (free var satisfies it)
        nonlocal nv
        key = (p, q) if p < q else (q, p)
        v = evmap.get(key)
        if v is None:
            nv += 1
            v = nv
            evmap[key] = v
            Ha, Hb = key[0] + 1, key[1] + 1
            defs = [[-v, Ha, Hb], [-v, -Ha, -Hb],
                    [v, Ha, -Hb], [v, -Ha, Hb]]
            if holder[0] is None:
                cnf.extend(defs)
            else:
                for cl in defs:
                    holder[0].add_clause(cl)
        return v

    for orb in ORBITS:                      # Lemma-A balance
        enc = CardEnc.equals(lits=[i + 1 for i in orb],
                             bound=len(orb) // 2, top_id=nv,
                             encoding=EncType.seqcounter)
        nv = enc.nv
        cnf.extend(enc.clauses)
    for c in cells:                          # one-hot
        ci = cidx[c]
        cnf.append([xvar(ci, o) for o in range(24)])
        for o1 in range(24):
            for o2 in range(o1 + 1, 24):
                cnf.append([-xvar(ci, o1), -xvar(ci, o2)])
    for c in cells:                          # symbolic adjacency
        ci = cidx[c]
        for ax in range(3):
            nc = list(c)
            nc[ax] += 1
            nci = cidx[reduce_vec(tuple(nc), B)]
            if nci == ci:
                for o in range(24):
                    pairs = PAIRS[ax][o][o]
                    if any(p == q for p, q in pairs):
                        cnf.append([-xvar(ci, o)])
                    else:
                        for p, q in pairs:
                            cnf.append([-xvar(ci, o), evar(p, q)])
                continue
            for o1 in range(24):
                x1 = xvar(ci, o1)
                for o2 in range(24):
                    x2 = xvar(nci, o2)
                    pairs = PAIRS[ax][o1][o2]
                    if any(p == q for p, q in pairs):
                        cnf.append([-x1, -x2])
                    else:
                        for p, q in pairs:
                            cnf.append([-x1, -x2, evar(p, q)])

    for S in blocked:                        # pre-block known patterns
        cnf.append([-evar(p, q) for p, q in S])    # before bootstrap!
    s = Cadical195(bootstrap_with=cnf)
    holder[0] = s                            # later evars go to solver

    novel = []
    t0 = time.time()
    nsol = 0
    complete = False
    while True:
        if len(novel) >= max_pat or time.time() - t0 > time_cap:
            break
        if not s.solve():
            complete = True
            break
        nsol += 1
        model = set(v for v in s.get_model() if v > 0)
        grid = {}
        for c in cells:
            ci = cidx[c]
            for o in range(24):
                if xvar(ci, o) in model:
                    grid[c] = o
                    break
        S = pattern_pairs_lattice(B, grid)
        novel.append(S)
        logf.write(json.dumps({"B": [list(r) for r in B],
                               "index": a * d * f,
                               "pattern": sorted(map(list, S))}) + "\n")
        for Sg in set(conjugates(S)):
            s.add_clause([-evar(p, q) for p, q in Sg])
            blocked.add(Sg)
    s.delete()
    return novel, complete, nsol


def main():
    max_index = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    max_pat = int(sys.argv[2]) if len(sys.argv) > 2 else 1000
    time_cap = float(sys.argv[3]) if len(sys.argv) > 3 else 300.0

    with open(PATTERN_FILE) as fh:
        data = json.load(fh)
    existing = [frozenset((min(p, q), max(p, q)) for p, q in plist)
                for plist in data.get("patterns", [])]
    blocked = set()
    for S in existing:
        blocked.update(conjugates(S))
    print(f"[{stamp()}] saturation to index {max_index}; "
          f"{len(existing)} existing patterns "
          f"({len(blocked)} conjugates) pre-blocked", flush=True)

    classes = sorted(lattice_classes(max_index),
                     key=lambda B: B[0][0] * B[1][1] * B[2][2])
    print(f"[{stamp()}] {len(classes)} lattice classes <= {max_index}",
          flush=True)

    logf = open("saturation_results.jsonl", "a")
    all_novel = []
    incomplete = []
    for n, B in enumerate(classes):
        ix = B[0][0] * B[1][1] * B[2][2]
        t0 = time.time()
        novel, complete, nsol = enumerate_class(B, blocked, logf,
                                                max_pat, time_cap)
        all_novel.extend(novel)
        if not complete:
            incomplete.append(B)
        logf.write(json.dumps({"class": [list(r) for r in B],
                               "index": ix, "novel": len(novel),
                               "complete": complete,
                               "secs": round(time.time() - t0, 1)})
                   + "\n")
        logf.flush()
        print(f"[{stamp()}] class {n+1}/{len(classes)} {B} idx {ix}: "
              f"{len(novel)} novel, "
              f"{'COMPLETE' if complete else 'CAPPED'} "
              f"[{time.time()-t0:.0f}s] (total novel {len(all_novel)})",
              flush=True)

    # merge into the shared pattern file
    with open(PATTERN_FILE) as fh:
        data = json.load(fh)
    have = {frozenset((min(p, q), max(p, q)) for p, q in plist)
            for plist in data.get("patterns", [])}
    added = 0
    for S in all_novel:
        if S not in have:
            have.add(S)
            data["patterns"].append(sorted(map(list, S)))
            added += 1
    with open(PATTERN_FILE, "w") as fh:
        json.dump(data, fh)
    print(f"[{stamp()}] SATURATION DONE: {len(all_novel)} novel patterns "
          f"({added} merged into {PATTERN_FILE}, now "
          f"{len(data['patterns'])}); {len(incomplete)} classes capped "
          f"of {len(classes)}", flush=True)
    if not incomplete:
        print(f"[{stamp()}] all classes COMPLETE: library now contains "
              f"EVERY balanced-realizable periodic pattern of index <= "
              f"{max_index}", flush=True)


if __name__ == "__main__":
    main()
