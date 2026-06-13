"""
CEGIS for the equivariant aperiodic Wang cube (binary heights, k=2).

Synthesizer: one incremental SAT instance over
  - 24 decoration bits H_i  (True = bump, False = dent)
  - orientation selectors for every cell of a 4x4x4 box
  demanding a locally consistent box tiling.

Verifier: for a concrete decoration, search torus tilings (= fully
periodic tilings) and check a 5x5x5 box.

Refinement:
  - periodic counterexample (T, grid): the validity of that exact
    periodic pattern is EXACTLY the conjunction of XOR constraints
    H_a != H_b over a pair-set S(T, grid). Blocking clause:
    "not all of S holds" -- one clause over reusable aux vars
    e_{ab} <-> (H_a XOR H_b). Conjugated over all 24 rotations.
    This removes EVERY decoration realizing that periodic pattern.
  - untileable counterexample: point-block the decoration and its
    24 rotated relabelings.

Possible outcomes:
  UNSAT     -> every k=2 binary cube tiling a 4^3 box realizes one of
               the discovered periodic patterns: finite impossibility
               result for this micro-arena.
  SURVIVOR  -> candidate: tiles 4^3 and 5^3, no torus tiling found in
               the checked family. NOT a proof of aperiodicity.
"""
import itertools
import json
import time
import numpy as np
from pysat.solvers import Glucose3

from einstein_search import (ROTS, PTS, PT_INDEX, IFACE_PAIRS,
                             placed_vectors, compat_tables, solve_tiling,
                             TORI_SMALL, TORI_EXT)

# ------------------------------------------------- index machinery

# PERM[o][i] = world point index where base point i lands under ROTS[o]
PERM = [[PT_INDEX[tuple(R @ np.array(p))] for p in PTS] for R in ROTS]
PERMINV = []
for o in range(24):
    inv = [0] * 24
    for i, j in enumerate(PERM[o]):
        inv[j] = i
    PERMINV.append(inv)

# PAIRS[ax][o1][o2] = the 4 (decoration-index, decoration-index) pairs
# whose heights must be opposite when tile o1 sits at c, tile o2 at c+e_ax
PAIRS = [[[None] * 24 for _ in range(24)] for _ in range(3)]
for ax in range(3):
    for o1 in range(24):
        for o2 in range(24):
            PAIRS[ax][o1][o2] = [(PERMINV[o1][jA], PERMINV[o2][jB])
                                 for jA, jB in IFACE_PAIRS[ax]]

ALL_TORI = sorted(set(TORI_SMALL) | set(TORI_EXT),
                  key=lambda t: (t[0] * t[1] * t[2], t))

# ------------------------------------------------- synthesizer CNF

SYNTH_DIMS = (4, 4, 4)

class Synth:
    def __init__(self):
        self.next_var = 24 + 1            # H vars are 1..24
        cells = list(itertools.product(*[range(d) for d in SYNTH_DIMS]))
        self.cell_idx = {c: i for i, c in enumerate(cells)}
        self.xbase = self.next_var
        self.next_var += len(cells) * 24
        self.aux = {}                     # (a,b) a<b -> var
        self.cnf = []
        self.cnf.append([1])              # H_0 = True (global flip symmetry)
        self._build(cells)
        self.solver = Glucose3()
        self.solver.append_formula(self.cnf)
        self.n_base = len(self.cnf)

    def xvar(self, ci, o):
        return self.xbase + ci * 24 + o

    def evar(self, a, b):
        key = (a, b) if a < b else (b, a)
        v = self.aux.get(key)
        if v is None:
            v = self.next_var
            self.next_var += 1
            self.aux[key] = v
            Ha, Hb = key[0] + 1, key[1] + 1
            defs = [[-v, Ha, Hb], [-v, -Ha, -Hb],
                    [v, Ha, -Hb], [v, -Ha, Hb]]
            if hasattr(self, "solver"):
                for cl in defs:
                    self.solver.add_clause(cl)
            else:
                self.cnf.extend(defs)
        return v

    def _build(self, cells):
        for c in cells:
            ci = self.cell_idx[c]
            self.cnf.append([self.xvar(ci, o) for o in range(24)])
            for o1 in range(24):
                for o2 in range(o1 + 1, 24):
                    self.cnf.append([-self.xvar(ci, o1),
                                     -self.xvar(ci, o2)])
        for c in cells:
            ci = self.cell_idx[c]
            for ax in range(3):
                nc = list(c)
                nc[ax] += 1
                if nc[ax] == SYNTH_DIMS[ax]:
                    continue
                nci = self.cell_idx[tuple(nc)]
                for o1 in range(24):
                    x1 = self.xvar(ci, o1)
                    for o2 in range(24):
                        x2 = self.xvar(nci, o2)
                        es = set()
                        dead = False
                        for a, b in PAIRS[ax][o1][o2]:
                            if a == b:
                                dead = True
                                break
                            es.add(self.evar(a, b))
                        if dead:
                            self.cnf.append([-x1, -x2])
                        else:
                            for e in es:
                                self.cnf.append([-x1, -x2, e])

    def propose(self):
        if not self.solver.solve():
            return None
        model = self.solver.get_model()
        pos = set(v for v in model if v > 0)
        return tuple(1 if (i + 1) in pos else -1 for i in range(24))

    def block_pattern(self, pair_set, seen):
        """Block every decoration realizing this periodic pattern,
        conjugated over the 24 rotations."""
        added = 0
        for g in range(24):
            pg = PERM[g]
            Sg = frozenset((min(pg[a], pg[b]), max(pg[a], pg[b]))
                           for a, b in pair_set)
            if Sg in seen:
                continue
            seen.add(Sg)
            self.solver.add_clause([-self.evar(a, b) for a, b in Sg])
            added += 1
        return added

    def block_point(self, dec):
        """Block this decoration and its 24 rotated relabelings."""
        for g in range(24):
            dg = [dec[PERMINV[g][j]] for j in range(24)]
            self.solver.add_clause(
                [-(i + 1) if dg[i] == 1 else (i + 1) for i in range(24)])
        return 24

# ------------------------------------------------- verifier

def pattern_pairs(dims, grid):
    S = set()
    for c in grid:
        for ax in range(3):
            nc = list(c)
            nc[ax] += 1
            if nc[ax] == dims[ax]:
                nc[ax] = 0
            o1, o2 = grid[c], grid[tuple(nc)]
            for a, b in PAIRS[ax][o1][o2]:
                S.add((min(a, b), max(a, b)))
    return frozenset(S)

def verify(dec):
    placed = placed_vectors(dec)
    compat = compat_tables(placed)
    for dims in ALL_TORI:
        sat, grid = solve_tiling(dims, True, compat)
        if sat:
            return ("periodic", dims, grid)
    sat, _ = solve_tiling((5, 5, 5), False, compat)
    if not sat:
        return ("untileable5", None, None)
    return ("survivor", None, None)

# ------------------------------------------------- loop

def run(max_iters=100000, time_budget=170.0):
    t0 = time.time()
    print(f"building synthesizer ({SYNTH_DIMS} box) ...")
    syn = Synth()
    print(f"  base clauses: {syn.n_base}, vars: {syn.next_var}")

    from collections import Counter
    kills = Counter()
    seen_patterns = set()
    survivors = []
    it = 0
    while time.time() - t0 < time_budget and it < max_iters:
        it += 1
        dec = syn.propose()
        if dec is None:
            print()
            print("=" * 64)
            print("SYNTHESIZER UNSAT.")
            print("Every binary k=2 decorated cube that tiles a 4x4x4 box")
            print("realizes one of the discovered periodic patterns, i.e.")
            print("EVERY such cube that tiles space admits a fully periodic")
            print("tiling with periods <= the checked torus family.")
            print(f"(after {it-1} counterexamples, "
                  f"{len(seen_patterns)} blocked patterns)")
            print("=" * 64)
            return "UNSAT", kills, survivors, it - 1

        verdict, dims, grid = verify(dec)
        if verdict == "periodic":
            S = pattern_pairs(dims, grid)
            syn.block_pattern(S, seen_patterns)
            kills[("torus", dims)] += 1
        elif verdict == "untileable5":
            syn.block_point(dec)
            kills[("untileable5",)] += 1
        else:
            print(f"  iter {it}: *** SURVIVOR *** dec = {dec}")
            survivors.append(dec)
            syn.block_point(dec)          # keep hunting for more
            kills[("survivor",)] += 1

        if it <= 5:   # soundness invariant: dec must now be infeasible
            assum = [(i + 1) if dec[i] == 1 else -(i + 1) for i in range(24)]
            assert not syn.solver.solve(assumptions=assum), \
                "blocking failed to exclude counterexample!"

        if it % 25 == 0:
            dt = time.time() - t0
            print(f"  iter {it}: {dt:.0f}s, patterns={len(seen_patterns)}, "
                  f"kills={dict(kills.most_common(5))}")

    print()
    print(f"budget reached after {it} iterations, "
          f"{time.time()-t0:.0f}s")
    return "BUDGET", kills, survivors, it

if __name__ == "__main__":
    status, kills, survivors, iters = run()
    print()
    print("status:", status)
    print("iterations:", iters)
    print("kill statistics:")
    for k, v in sorted(kills.items(), key=lambda kv: -kv[1]):
        print(f"   {k}: {v}")
    print("survivors:", len(survivors))
    for d in survivors:
        print("  ", d)
    with open("cegis_log.json", "w") as f:
        json.dump({"status": status, "iters": iters,
                   "kills": {str(k): v for k, v in kills.items()},
                   "survivors": [list(d) for d in survivors]}, f)
