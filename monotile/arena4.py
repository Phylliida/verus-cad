"""
Arena 4: joint lock+payload synthesis over all 54 bits.

ARCHIVED from the parallel claude.ai session 2026-06-09 (evening drop).
STATUS: CLOSED by two no-go theorems — for H in {D4 axis-stabilizer,
A4}, no balanced k=3 decoration whose matching system forbids all
cross-coset adjacencies of H tiles space without also tiling
periodically (index <= 16 for D4 / <= 8 for A4; 36 and 29 pattern
classes + synthesizer UNSAT). The frame-lock architecture is dead at
both viable subgroup sizes.

NOTE (local): imports arena3 and an arena2 with lsolve/lattice_sweep —
the parallel branch's versions. arena3.py is NOT on this box; ask for
it if we ever want to re-run these closures locally. Kept for the
record and for the techniques (joint co-design over the lock's full
parameter space; weakest-sufficient-form spec relaxation).

The lock is no longer fixed: corner bits are variables, constrained only
by the lock SPEC, relaxed to its weakest sufficient form --

    for every axis and every cross-coset orientation pair (o1, o2):
        at least one of the nine point-pairs is NON-complementary.

This forbids all cross-coset adjacencies in the full system, so every
tiling lives in a single coset of H; cosets are conjugate by system
equivariance (valid for any decoration), so the identity-coset sector
represents the tile. Within-coset structure is entirely free: the
synthesizer co-designs lock richness and payload structure.

No viability requirement (identity self-stack would force a periodic
tiling to exist); nonemptiness comes from the 5^3 sector box.

Survivors face a built-in deep gauntlet (lattice classes <= 32,
extended vectors with a coordinate 4, an 8^3 box) before being
reported.

Usage:  python3 arena4.py test
        python3 arena4.py d4 180
        python3 arena4.py a4 3600
"""
import itertools
import json
import sys
import time
from collections import Counter
import numpy as np
from pysat.solvers import Glucose3
from pysat.card import CardEnc, EncType

from arena2 import (PTS, ROTS, PERM, PAIRS, _hnf, lsolve,
                    held_vectors, implied_lattices)
import rigidity
from rigidity import CH, ROT_KEY
from arena3 import (a4_subgroup, box_sat, lattice_torus, sheet_scan,
                    bad_tables, D4_CANON)
from skew import lattice_classes

NPTS = len(PTS)
assert NPTS == 54
ORBITS = [sorted(CH["corner"]), sorted(CH["edge"]), sorted(CH["center"])]
MUL = [[ROT_KEY[tuple((ROTS[a] @ ROTS[b]).flatten())]
        for b in range(24)] for a in range(24)]

EXTRA4 = [(a, b, c) for a in range(5) for b in range(a, 5)
          for c in range(5) if max(a, b, c) > 3]

# ------------------------------------------------------------ setup

def setup(kind):
    Hset = a4_subgroup() if kind == "a4" else set(rigidity.H_AXIS)
    rigidity.HSET = Hset                      # keep rigidity consistent
    letters = sorted(Hset)
    coset_id = {}
    reps = []
    for o in range(24):
        if o in coset_id:
            continue
        members = frozenset(MUL[o][h] for h in letters)
        cid = len(reps)
        reps.append(members)
        for m in members:
            coset_id[m] = cid
    cross = [(o1, o2) for o1 in range(24) for o2 in range(24)
             if coset_id[o1] != coset_id[o2]]
    return letters, coset_id, cross

def compat_sector(dec, letters):
    NL = len(letters)
    compat = np.zeros((3, NL, NL), dtype=bool)
    for ax in range(3):
        for i, o1 in enumerate(letters):
            for j, o2 in enumerate(letters):
                compat[ax, i, j] = all(
                    a != b and dec[a] + dec[b] == 0
                    for a, b in PAIRS[ax][o1][o2])
    return compat

def spec_violations(dec, coset_id):
    """Count cross-coset orientation pairs the FULL system still allows."""
    bad = 0
    for ax in range(3):
        for o1 in range(24):
            for o2 in range(24):
                if coset_id[o1] == coset_id[o2]:
                    continue
                if all(a != b and dec[a] + dec[b] == 0
                       for a, b in PAIRS[ax][o1][o2]):
                    bad += 1
    return bad

def is_symmetric(dec):
    for g in range(1, 24):
        if all(dec[PERM[g][i]] == dec[i] for i in range(NPTS)):
            return True
    return False

# -------------------------------------------------------- synthesizer

SYNTH_DIMS = (5, 5, 5)

class Synth:
    def __init__(self, letters, cross):
        self.letters = letters
        self.NL = len(letters)
        self.next_var = NPTS + 1
        cells = list(itertools.product(*[range(d) for d in SYNTH_DIMS]))
        self.cell_idx = {c: i for i, c in enumerate(cells)}
        self.xbase = self.next_var
        self.next_var += len(cells) * self.NL
        self.aux = {}
        self.cnf = [[1]]                       # global flip symmetry
        for orb, bound in zip(ORBITS, (12, 12, 3)):
            enc = CardEnc.equals(lits=[i + 1 for i in orb], bound=bound,
                                 top_id=self.next_var - 1,
                                 encoding=EncType.seqcounter)
            self.next_var = enc.nv + 1
            self.cnf.extend(enc.clauses)
        self._lock_spec(cross)
        self._box(cells)
        self.solver = Glucose3()
        self.solver.append_formula(self.cnf)
        self.n_base = len(self.cnf)

    def xvar(self, ci, l):
        return self.xbase + ci * self.NL + l

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

    def _lock_spec(self, cross):
        for ax in range(3):
            for o1, o2 in cross:
                pairs = PAIRS[ax][o1][o2]
                if any(a == b for a, b in pairs):
                    continue                   # auto-forbidden
                self.cnf.append([-self.evar(a, b) for a, b in pairs])

    def _box(self, cells):
        for c in cells:
            ci = self.cell_idx[c]
            self.cnf.append([self.xvar(ci, l) for l in range(self.NL)])
            for l1 in range(self.NL):
                for l2 in range(l1 + 1, self.NL):
                    self.cnf.append([-self.xvar(ci, l1),
                                     -self.xvar(ci, l2)])
        for c in cells:
            ci = self.cell_idx[c]
            for ax in range(3):
                nc = list(c)
                nc[ax] += 1
                if nc[ax] == SYNTH_DIMS[ax]:
                    continue
                nci = self.cell_idx[tuple(nc)]
                for i, o1 in enumerate(self.letters):
                    x1 = self.xvar(ci, i)
                    for j, o2 in enumerate(self.letters):
                        x2 = self.xvar(nci, j)
                        pairs = PAIRS[ax][o1][o2]
                        if any(a == b for a, b in pairs):
                            self.cnf.append([-x1, -x2])
                            continue
                        for a, b in pairs:
                            self.cnf.append([-x1, -x2,
                                             self.evar(a, b)])

    def propose(self):
        r = lsolve(self.solver, 3_000_000)
        if r is None:
            return "STALL"
        if r is False:
            return None
        pos = set(v for v in self.solver.get_model() if v > 0)
        return tuple(1 if (i + 1) in pos else -1 for i in range(NPTS))

    def block_pattern(self, pair_set, seen):
        if pair_set in seen:
            return 0
        seen.add(pair_set)
        self.solver.add_clause([-self.evar(a, b) for a, b in pair_set])
        return 1

    def block_point(self, dec):
        self.solver.add_clause(
            [-(i + 1) if dec[i] == 1 else (i + 1) for i in range(NPTS)])

def pattern_pairs(B, qgrid, letters):
    """All complementary point-pairs realized by a quotient tiling."""
    from arena3 import reduce_vec
    S = set()
    for c, i in qgrid.items():
        for ax in range(3):
            nc = list(c)
            nc[ax] += 1
            j = qgrid[reduce_vec(tuple(nc), B)]
            for a, b in PAIRS[ax][letters[i]][letters[j]]:
                S.add((min(a, b), max(a, b)))
    return frozenset(S)

# ----------------------------------------------------------- verifier

class Verifier:
    def __init__(self, compat, NL):
        self.NL = NL
        self.compat = compat
        self.bad, self.selfbad = bad_tables(compat, NL)
        from arena3 import box_cnf, extract_grid
        self._extract = extract_grid
        cnf, cells, idx, var = box_cnf((5, 5, 5), self.bad, NL)
        self.cells, self.idx, self.var = cells, idx, var
        self.sels = {}
        nv = len(cells) * NL
        for v in D4_CANON:
            nv += 1
            self.sels[v] = nv
            for c in cells:
                c2 = (c[0] + v[0], c[1] + v[1], c[2] + v[2])
                if c2 in idx:
                    for l in range(NL):
                        cnf.append([-nv, -var(idx[c], l), var(idx[c2], l)])
                        cnf.append([-nv, var(idx[c], l), -var(idx[c2], l)])
        self.s = Glucose3(bootstrap_with=cnf)

    def close(self):
        self.s.delete()

    def confirm(self, grid, maxc, minp):
        held = held_vectors(grid, maxc, minp)
        for B in implied_lattices(held):
            sat, qgrid = lattice_torus(B, self.bad, self.selfbad, self.NL)
            if sat:
                return B, qgrid
        return None, None

    def verdict(self):
        hit = sheet_scan(self.compat, self.NL)
        if hit is not None:
            B, m = hit
            tsat, qgrid = lattice_torus(B, self.bad, self.selfbad,
                                        self.NL)
            if tsat:
                return ("periodic", B, qgrid)
        suspicious = []
        escalated = False
        for v in D4_CANON:
            r = lsolve(self.s, 50_000, [self.sels[v]])
            if r is False:
                continue
            if r is None:
                suspicious.append((v, "detect-timeout"))
                continue
            grid = self._extract(self.s.get_model(), self.cells,
                                 self.idx, self.var, self.NL)
            B, qgrid = self.confirm(grid, 3, 4)
            if B is not None:
                return ("periodic", B, qgrid)
            if not escalated:
                escalated = True
                s6, g6 = box_sat((6, 6, 6), self.bad, self.NL,
                                 identify=v, budget=200_000)
                if s6 is False:
                    continue
                if s6:
                    B, qgrid = self.confirm(g6, 4, 12)
                    if B is not None:
                        return ("periodic", B, qgrid)
            suspicious.append((v, "unconfirmed"))
        sat, _ = box_sat((6, 6, 6), self.bad, self.NL, budget=300_000)
        if sat is False:
            return ("untileable6", None, None)
        if sat is None:
            suspicious.append(("box6", "timeout"))
        if suspicious:
            return ("suspicious", suspicious, None)
        return ("survivor", None, None)

def deep_check(compat, NL):
    """Gauntlet for in-loop survivors. Returns (tag, B, qgrid)."""
    bad, selfbad = bad_tables(compat, NL)
    for B in lattice_classes(32):
        ts, qg = lattice_torus(B, bad, selfbad, NL)
        if ts:
            return ("periodic-deep", B, qg)
    for v in EXTRA4:
        sv, gv = box_sat((6, 6, 6), bad, NL, identify=v, budget=300_000)
        if sv is None:
            return ("ext-timeout", v, None)
        if sv:
            held = held_vectors(gv, 4, 12)
            for B in implied_lattices(held):
                ts, qg = lattice_torus(B, bad, selfbad, NL)
                if ts:
                    return ("periodic-deep", B, qg)
            return ("suspicious-ext", v, None)
    s8, _ = box_sat((8, 8, 8), bad, NL, budget=1_500_000)
    if s8 is False:
        return ("untileable8", None, None)
    if s8 is None:
        return ("box8-timeout", None, None)
    return ("DEEP-SURVIVOR", None, None)

_LC32 = None

def lattice_sweep(compat, NL, max_index=32):
    """Brute sweep over all sublattice classes up to max_index."""
    global _LC32
    if _LC32 is None:
        _LC32 = list(lattice_classes(max_index))
    bad, selfbad = bad_tables(compat, NL)
    for B in _LC32:
        ts, qg = lattice_torus(B, bad, selfbad, NL)
        if ts:
            return B, qg
    return None, None

# ---------------------------------------------------------------- main

def make_witness(kind):
    lock = rigidity.solve_spec("corner", "v2")
    dec = [0] * NPTS
    for g, v in lock.items():
        dec[g] = v
    for g in sorted(CH["edge"]) + sorted(CH["center"]):
        p = PTS[g]
        ax = max(range(3), key=lambda i: abs(p[i]))
        dec[g] = 1 if p[ax] > 0 else -1
    return tuple(dec)

def self_test(kind):
    letters, coset_id, cross = setup(kind)
    w = make_witness(kind)
    nv = spec_violations(w, coset_id)
    assert nv == 0, f"witness violates spec: {nv}"
    compat = compat_sector(w, letters)
    V = Verifier(compat, len(letters))
    verdict, B, _ = V.verdict()
    V.close()
    assert verdict == "periodic", verdict
    idx = B[0][0] * B[1][1] * B[2][2]
    print(f"[test {kind}] witness: spec OK, verdict 'periodic' "
          f"index {idx}: OK")

def run(kind, budget):
    letters, coset_id, cross = setup(kind)
    NL = len(letters)
    print(f"arena 4, sector {kind}: NL={NL}, "
          f"{len(cross)} cross-coset pairs per axis")
    self_test(kind)
    t0 = time.time()
    syn = Synth(letters, cross)
    print(f"  synth built: {syn.n_base} clauses, {time.time()-t0:.0f}s")
    kills = Counter()
    idxh = Counter()
    seen = set()
    deep_survivors, sus = [], []
    logf = open(f"arena4_{kind}_progress.jsonl", "a")
    it = 0
    while time.time() - t0 < budget:
        it += 1
        dec = syn.propose()
        if dec == "STALL":
            print(f"\nsynth budget exceeded at iter {it}")
            break
        if dec is None:
            print()
            print("=" * 62)
            print(f"SYNTHESIZER UNSAT: arena-4 {kind} CLOSED -- no")
            print("balanced cross-coset-locked decoration tiles a 5^3")
            print("sector box outside the blocked periodic patterns.")
            print("=" * 62)
            return ("UNSAT", kills, idxh, deep_survivors, sus, it - 1)
        if it <= 3:
            assert spec_violations(dec, coset_id) == 0
        rec = {"it": it}
        if is_symmetric(dec):
            kills["symmetric"] += 1
            rec["verdict"] = "symmetric"
            syn.block_point(dec)
        else:
            compat = compat_sector(dec, letters)
            V = Verifier(compat, NL)
            verdict, info, qgrid = V.verdict()
            V.close()
            if verdict == "survivor":
                verdict, info, qgrid = deep_check(compat, NL)
            elif verdict == "suspicious":
                B2, qg2 = lattice_sweep(compat, NL)
                if B2 is not None:
                    verdict, info, qgrid = "periodic-deep", B2, qg2
            rec["verdict"] = verdict
            if verdict in ("periodic", "periodic-deep"):
                B = info
                li = B[0][0] * B[1][1] * B[2][2]
                idxh[li] += 1
                rec["index"] = li
                syn.block_pattern(pattern_pairs(B, qgrid, letters), seen)
            elif verdict == "DEEP-SURVIVOR":
                print(f"  iter {it}: *** DEEP SURVIVOR *** dec={dec}")
                deep_survivors.append(dec)
                rec["dec"] = list(dec)
                syn.block_point(dec)
            elif verdict in ("suspicious", "suspicious-ext",
                             "ext-timeout", "box8-timeout"):
                sus.append((dec, info))
                rec["dec"] = list(dec)
                syn.block_point(dec)
            else:
                syn.block_point(dec)
            kills[verdict] += 1
        logf.write(json.dumps(rec) + "\n")
        logf.flush()
        if it % 10 == 0:
            print(f"  iter {it}: {time.time()-t0:.0f}s "
                  f"kills={dict(kills)} idx={dict(idxh)}")
    print(f"\nbudget reached: {it} iterations, {time.time()-t0:.0f}s")
    return ("BUDGET", kills, idxh, deep_survivors, sus, it)

if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "test":
        self_test("d4")
        self_test("a4")
        sys.exit(0)
    kind = sys.argv[1] if len(sys.argv) > 1 else "d4"
    budget = float(sys.argv[2]) if len(sys.argv) > 2 else 150.0
    status, kills, idxh, deeps, sus, iters = run(kind, budget)
    print()
    print("status:", status, "| iterations:", iters)
    print("verdicts:", dict(kills))
    print("confirmed period indices:", dict(sorted(idxh.items())))
    print(f"deep survivors: {len(deeps)}  suspicious: {len(sus)}")
