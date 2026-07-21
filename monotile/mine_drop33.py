"""anyk-05: build the 33 drop-one-pattern census instances (K=3, 4^3 box).

For each i, the instance is: balanced AND tiles-4^3 AND avoids the rotation
closure of the other 32 patterns. The original MUS pass left 3 of these
neither fast-SAT nor fast-UNSAT at 200s; rebuilding all 33 with full lex
symmetry-breaking (sound at the cubic box: rotation-closed pattern set,
flip-invariant e-blocks) to re-run the census with the tractability trick
the closure run validated.

Usage:  ./runpy.sh mine_drop33.py     # writes drop_census/drop_NN.cnf x33
Solve each: cadical -t <sec> drop_census/drop_NN.cnf  (10=SAT, 20=UNSAT)
"""
import json
import os
import time

import arena2
from arena2 import Synth, PATTERN_FILE, PERMINV, NPTS

assert NPTS == 54 and arena2.K == 3
assert arena2.SYNTH_DIMS == (4, 4, 4)


class Collector:
    def __init__(self):
        self.clauses = []

    def add_clause(self, cl):
        self.clauses.append(list(cl))


def add_lex_leaders_group(cnf, nv, elems):
    for g, f in elems:
        if g == 0 and f == 1:
            continue
        prev = None
        for j in range(NPTS):
            la = j + 1
            v = PERMINV[g][j] + 1
            lb = v if f == 1 else -v
            if la == lb:
                continue
            if la == -lb:
                cnf.append([-la] if prev is None else [-prev, -la])
                break
            cnf.append([-la, lb] if prev is None else [-prev, -la, lb])
            nv += 1
            q = nv
            if prev is not None:
                cnf.append([-q, prev])
            cnf.append([-q, -la, lb])
            cnf.append([-q, la, -lb])
            prev = q
    return nv


with open(PATTERN_FILE) as f:
    data = json.load(f)
patterns = [frozenset((min(a, b), max(a, b)) for a, b in plist)
            for plist in data.get("patterns", [])]
assert len(patterns) == 33, len(patterns)

os.makedirs("drop_census", exist_ok=True)
FULL48 = [(g, f) for g in range(24) for f in (1, -1)]

for drop in range(33):
    t0 = time.time()
    syn = Synth()
    syn.solver.delete()
    col = Collector()
    syn.solver = col
    seen = set()
    blocked = sum(syn.block_pattern(S, seen)
                  for i, S in enumerate(patterns) if i != drop)
    assert syn.cnf[0] == [1]
    cnf = syn.cnf[1:] + col.clauses
    nv = add_lex_leaders_group(cnf, syn.next_var - 1, FULL48)
    path = f"drop_census/drop_{drop:02d}.cnf"
    with open(path, "w") as f:
        f.write(f"p cnf {nv} {len(cnf)}\n")
        for cl in cnf:
            f.write(" ".join(map(str, cl)) + " 0\n")
    print(f"{path}: {nv} vars, {len(cnf)} clauses, {blocked} blocks "
          f"[{time.time() - t0:.0f}s]", flush=True)
print("all 33 built", flush=True)
