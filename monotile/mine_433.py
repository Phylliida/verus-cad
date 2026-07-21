"""anyk-04: build the 4x3x3 candidate-minimal-box instance (K=3) as DIMACS.

Instance: balanced AND tiles-(4,3,3) AND avoids all 33 patterns
(rotation-conjugated blocks, as in cube_conquer3.build_cnf; no point-blocks --
matches the formal SearchUnsat statement, which is patterns-only).

Lex symmetry-breaking soundness on a non-cubic box: a rotation g maps a
(4,3,3)-tiling of dec to a tiling of the axis-permuted box by rotDec(g)dec,
so only rotations preserving the long axis {+x,-x} (8 of the 24) keep the
box shape (y,z dims equal, so any {+-x}-preserving rotation works), and the
global bit-complement always works. Lex over that order-16 group is sound;
full-24 lex would be unsound here (a "UNSAT" could be a lex artifact).

Usage:  ./runpy.sh mine_433.py        # writes mine_433.cnf
then:   cadical mine_433.cnf          # 10=SAT (decode vars 1..54), 20=UNSAT
"""
import json
import time

import numpy as np

import arena2
arena2.SYNTH_DIMS = (4, 3, 3)
from arena2 import Synth, PATTERN_FILE, PERMINV, NPTS, ROTS

assert NPTS == 54, "this instance is the K=3 arena"
assert arena2.K == 3


class Collector:
    def __init__(self):
        self.clauses = []

    def add_clause(self, cl):
        self.clauses.append(list(cl))


def axis_subgroup():
    """Rotations that fix the x-axis up to sign (they permute {+-y,+-z},
    which is fine since the y/z dims are equal)."""
    ex = np.array([1, 0, 0])
    H = [g for g in range(24) if abs(int((ROTS[g] @ ex)[0])) == 1]
    assert len(H) == 8, H
    return H


def add_lex_leaders_group(cnf, nv, elems):
    """cube_conquer3.add_lex_leaders restricted to the given (g, flip)
    group elements."""
    n0 = len(cnf)
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
    print(f"lex-leader (order-{len(elems)} group): {len(cnf) - n0} clauses",
          flush=True)
    return nv


t0 = time.time()
print(f"building Synth at dims {arena2.SYNTH_DIMS} ...", flush=True)
syn = Synth()
syn.solver.delete()
col = Collector()
syn.solver = col

with open(PATTERN_FILE) as f:
    data = json.load(f)
patterns = [frozenset((min(a, b), max(a, b)) for a, b in plist)
            for plist in data.get("patterns", [])]
assert len(patterns) == 33, len(patterns)
seen = set()
blocked = sum(syn.block_pattern(S, seen) for S in patterns)

assert syn.cnf[0] == [1]
cnf = syn.cnf[1:] + col.clauses
nv = syn.next_var - 1
elems = [(g, f) for g in axis_subgroup() for f in (1, -1)]
nv = add_lex_leaders_group(cnf, nv, elems)

with open("mine_433.cnf", "w") as f:
    f.write(f"p cnf {nv} {len(cnf)}\n")
    for cl in cnf:
        f.write(" ".join(map(str, cl)) + " 0\n")
print(f"wrote mine_433.cnf: {nv} vars, {len(cnf)} clauses, "
      f"{blocked} pattern blocks, {time.time() - t0:.0f}s", flush=True)
