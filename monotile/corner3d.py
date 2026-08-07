"""Phase 0 probe: corner-marked Wang cubes at K=1 (PLAN-corner-cubes.md).

M-corner model: each cube corner carries one of T colors. A tiling is an
orientation field omega: Z^3 -> Rot(cube) (24 rotations, NO reflections)
such that at every lattice vertex the 8 incident corner colors satisfy a
packing rule:

  rule "equal"  — all 8 colors equal (the gain-structure semantics);
  rule "exact1" — exactly one of the 8 corners is a bump (color 1).
                  Physically: 8 corner tabs meeting at a vertex must pack.

Corners are 8-ary constraints (a lattice vertex is shared by 8 cubes), so
the face-track census machinery does not port — but at K=1 the decoration
space is tiny (23 rotation orbits at T=2, 333 at T=3), brute-force
classification suffices.

Encoder (SAT, Glucose3): one-hot orientation vars per cell; for "equal",
one-hot vertex-color vars with channeling clauses (cell c in orientation
o => vertex v takes the color o shows at that corner); for "exact1", a
bump literal per (cell, corner) tied to the orientations, with
exactly-one over the 8 incident corners per vertex.

Tiers per decoration (mirrors classify_color.py):
  torus sweep cap 4 -> box 3^3 -> box 4^3 -> torus cap 8 -> box 5^3
  -> SUSPICIOUS (the Phase-0 win condition: neither periodic nor empty).

Sanity checks (run always before classifying):
  * rotation group: 24 elements, closed, faithful on corners;
  * census sizes: 23 (T=2) / 333 (T=3) canonical decorations;
  * empty/full decorations tile at period 1 (equal);
  * single-marked corner: explicit period-2 construction from S = 2Z^3
    (every cube has exactly one even vertex) — the plan's parenthetical
    claimed no period-2 orientation map exists; there IS one, and both
    the construction and the solver confirm it;
  * single-marked under exact1: period-2 via a GL(3,2) shift;
  * box 2^3 (single-vertex) SAT results brute-force cross-checked for
    every canonical T=2 decoration.

Checkpointed append-only jsonl; safe to kill and relaunch.

Run:  ./runpy.sh corner3d.py [T=2] [workers=8]
"""
import itertools
import json
import multiprocessing as mp
import os
import sys
import time

import numpy as np
from pysat.solvers import Glucose3

T = int(sys.argv[1]) if len(sys.argv) > 1 else 2
WORKERS = int(sys.argv[2]) if len(sys.argv) > 2 else 8
CKPT = f"corner3d_T{T}_results.jsonl"

# ------------------------------------------------------------- geometry

CORNERS = list(itertools.product((0, 1), repeat=3))  # idx = x + 2y + 4z


def cidx(e):
    return e[0] + 2 * e[1] + 4 * e[2]


def gen_rots():
    """The 24 orientation-preserving signed permutation matrices."""
    rots = []
    for perm in itertools.permutations(range(3)):
        P = np.zeros((3, 3), dtype=int)
        for i, j in enumerate(perm):
            P[i, j] = 1
        for signs in itertools.product((1, -1), repeat=3):
            M = P * np.array(signs)[None, :]
            if round(np.linalg.det(M)) == 1:
                rots.append(M)
    assert len(rots) == 24
    return rots


ROTS = gen_rots()


def rot_corner(M, c):
    """Rotate cube corner c in {0,1}^3 about the cube center."""
    v = np.array([2 * c[i] - 1 for i in range(3)])
    w = M @ v
    return tuple(int((w[i] + 1) // 2) for i in range(3))


# SIG[o][c] = corner index that rotation o moves corner c to.
SIG = [[CORNERS.index(rot_corner(M, c)) for c in CORNERS] for M in ROTS]
SIGINV = []
for o in range(24):
    inv = [0] * 8
    for c in range(8):
        inv[SIG[o][c]] = c
    SIGINV.append(inv)


def show_table(dec):
    """show[o][p] = color a cell in orientation o shows at corner p."""
    return [tuple(dec[SIGINV[o][p]] for p in range(8)) for o in range(24)]


def canonical(dec):
    return min(tuple(dec[SIG[o][p]] for p in range(8)) for o in range(24))


def census(t):
    return sorted({canonical(dec)
                   for dec in itertools.product(range(t), repeat=8)})


# ------------------------------------------------------------- SAT core

def corner_sat(show, dims, rule, periodic, conf_budget=None):
    """Tri-state: (True, grid) / (False, None) / (None, None) on budget.

    grid maps cell -> orientation (cells in lexicographic order).
    """
    d1, d2, d3 = dims
    cells = [(x, y, z) for x in range(d1) for y in range(d2)
             for z in range(d3)]
    idx = {c: i for i, c in enumerate(cells)}

    def ovar(ci, o):
        return ci * 24 + o + 1

    if periodic:
        verts = list(cells)  # one fundamental vertex per cell
    else:  # box: constrain only vertices with all 8 incident cells present
        verts = [(x, y, z) for x in range(1, d1) for y in range(1, d2)
                 for z in range(1, d3)]

    def incident(v):
        for e in CORNERS:
            if periodic:
                c = ((v[0] - e[0]) % d1, (v[1] - e[1]) % d2,
                     (v[2] - e[2]) % d3)
            else:
                c = (v[0] - e[0], v[1] - e[1], v[2] - e[2])
            yield idx[c], cidx(e)

    cnf = []
    for ci in range(len(cells)):
        cnf.append([ovar(ci, o) for o in range(24)])
        for o1 in range(24):
            for o2 in range(o1 + 1, 24):
                cnf.append([-ovar(ci, o1), -ovar(ci, o2)])

    top = len(cells) * 24
    if rule == "equal":
        tmax = max(max(row) for row in show)

        def cvar(vi, t):
            return top + vi * (tmax + 1) + t + 1

        for vi, v in enumerate(verts):
            cnf.append([cvar(vi, t) for t in range(tmax + 1)])
            for t1 in range(tmax + 1):
                for t2 in range(t1 + 1, tmax + 1):
                    cnf.append([-cvar(vi, t1), -cvar(vi, t2)])
            for ci, p in incident(v):
                for o in range(24):
                    cnf.append([-ovar(ci, o), cvar(vi, show[o][p])])
    elif rule == "exact1":
        bumpers = [[o for o in range(24) if show[o][p] == 1]
                   for p in range(8)]

        def bvar(ci, p):
            return top + ci * 8 + p + 1

        for ci in range(len(cells)):
            for p in range(8):
                for o in bumpers[p]:
                    cnf.append([-ovar(ci, o), bvar(ci, p)])
                cnf.append([-bvar(ci, p)] + [ovar(ci, o)
                                             for o in bumpers[p]])
        for v in verts:
            lits = [bvar(ci, p) for ci, p in incident(v)]
            cnf.append(list(lits))
            for i in range(len(lits)):
                for j in range(i + 1, len(lits)):
                    cnf.append([-lits[i], -lits[j]])
    else:
        raise ValueError(rule)

    with Glucose3(bootstrap_with=cnf) as s:
        if conf_budget is None:
            r = s.solve()
        else:
            s.conf_budget(conf_budget)
            r = s.solve_limited()
        if r is None:
            return None, None
        if not r:
            return False, None
        pos = set(x for x in s.get_model() if x > 0)
        grid = {}
        for c in cells:
            ci = idx[c]
            grid[c] = next(o for o in range(24) if ovar(ci, o) in pos)
        return True, grid


def check_torus(show, dims, grid, rule):
    """Pure-python witness verification (mirrors color-track self-check)."""
    d1, d2, d3 = dims
    for vx in range(d1):
        for vy in range(d2):
            for vz in range(d3):
                vals = []
                for e in CORNERS:
                    c = ((vx - e[0]) % d1, (vy - e[1]) % d2,
                         (vz - e[2]) % d3)
                    vals.append(show[grid[c]][cidx(e)])
                if rule == "equal" and len(set(vals)) != 1:
                    return False
                if rule == "exact1" and sum(vals) != 1:
                    return False
    return True


# ------------------------------------------------------------- sanity

def sanity(decs2):
    # rotation group: 24 distinct, closed, faithful corner action
    assert len({tuple(M.flatten()) for M in ROTS}) == 24
    flat = {tuple(M.flatten()) for M in ROTS}
    for A in ROTS:
        for B in ROTS:
            assert tuple((A @ B).flatten()) in flat
    for o in range(24):
        assert sorted(SIG[o]) == list(range(8))
    print("  rotation group OK", flush=True)

    # census sizes (Burnside: 23 at T=2, 333 at T=3)
    assert len(decs2) == 23
    assert len(census(3)) == 333
    print("  census sizes OK (23 @ T=2, 333 @ T=3)", flush=True)

    # empty / full decorations tile at period 1 (equal)
    for dec in [(0,) * 8, (1,) * 8]:
        show = show_table(dec)
        ok, grid = corner_sat(show, (1, 1, 1), "equal", True, 10_000)
        assert ok and check_torus(show, (1, 1, 1), grid, "equal")
    print("  empty/full decorations: period-1 OK", flush=True)

    # single marked corner: explicit period-2 construction (S = 2Z^3:
    # every unit cube has exactly one all-even vertex; mark that corner)
    dec = (1,) + (0,) * 7
    show = show_table(dec)
    grid = {}
    for c in CORNERS:
        o = next(o for o in range(24) if SIG[o][0] == cidx(c))
        grid[c] = o
    assert check_torus(show, (2, 2, 2), grid, "equal")
    ok, grid2 = corner_sat(show, (2, 2, 2), "equal", True, 10_000)
    assert ok and check_torus(show, (2, 2, 2), grid2, "equal")
    print("  single-marked corner: period-2 (2Z^3) OK + solver agrees",
          flush=True)

    # single marked corner under exact1: period-2 via GL(3,2) shift.
    # Cube c marks corner (A-I)c mod 2, so vertex v receives marks from
    # cubes c with A c = v (mod 2) — exactly one, A invertible.
    A = ((0, 0, 1), (1, 0, 1), (0, 1, 0))
    assert len({tuple(sum(A[i][j] * c[j] for j in range(3)) % 2
                      for i in range(3)) for c in CORNERS}) == 8
    grid = {}
    for c in CORNERS:
        eps = tuple(sum((A[i][j] - (i == j)) * c[j]
                        for j in range(3)) % 2 for i in range(3))
        o = next(o for o in range(24) if SIG[o][0] == cidx(eps))
        grid[c] = o
    assert check_torus(show, (2, 2, 2), grid, "exact1")
    ok, grid2 = corner_sat(show, (2, 2, 2), "exact1", True, 10_000)
    assert ok and check_torus(show, (2, 2, 2), grid2, "exact1")
    print("  single-marked corner exact1: period-2 (GL(3,2)) OK", flush=True)

    # empty/full under exact1 can never tile (0 resp. 8 bumps per vertex)
    for dec in [(0,) * 8, (1,) * 8]:
        ok, _ = corner_sat(show_table(dec), (1, 1, 1), "exact1", True,
                           10_000)
        assert ok is False
    print("  empty/full exact1: UNSAT at 1x1x1 OK", flush=True)

    # box 2^3 (single constrained vertex) brute-force cross-check:
    # SAT iff exists color t with every corner slot able to show t.
    for dec in decs2:
        show = show_table(dec)
        brute = any(all(any(show[o][cidx(e)] == t for o in range(24))
                        for e in CORNERS) for t in range(2))
        ok, _ = corner_sat(show, (2, 2, 2), "equal", False, 10_000)
        assert bool(ok) == brute, (dec, ok, brute)
    print("  box 2x2x2 brute-force cross-check OK (23/23)", flush=True)


# ------------------------------------------------------------- classify

def torus_sweep(show, rule, cap, budget):
    """Rectangular tori, smallest volume first. Returns (dims, grid)."""
    dims = sorted(itertools.product(range(1, cap + 1), repeat=3),
                  key=lambda d: (d[0] * d[1] * d[2], d))
    for d in dims:
        ok, grid = corner_sat(show, d, rule, True, budget)
        if ok:
            return d, grid
    return None


def classify_one(job):
    i, dec, rule = job
    show = show_table(dec)
    hit = torus_sweep(show, rule, 4, 20_000)
    if hit:
        d, grid = hit
        assert check_torus(show, d, grid, rule)
        cells = sorted(grid)
        return {"i": i, "rule": rule, "verdict": "periodic",
                "d": list(d), "grid": [grid[c] for c in cells]}
    for n, budget in ((3, 200_000), (4, 2_000_000)):
        ok, _ = corner_sat(show, (n, n, n), rule, False, budget)
        if ok is False:
            return {"i": i, "rule": rule, "verdict": f"empty{n}"}
    hit = torus_sweep(show, rule, 8, 50_000)
    if hit:
        d, grid = hit
        assert check_torus(show, d, grid, rule)
        cells = sorted(grid)
        return {"i": i, "rule": rule, "verdict": "periodic-late",
                "d": list(d), "grid": [grid[c] for c in cells]}
    ok, _ = corner_sat(show, (5, 5, 5), rule, False, 20_000_000)
    if ok is False:
        return {"i": i, "rule": rule, "verdict": "empty5"}
    return {"i": i, "rule": rule, "verdict": "SUSPICIOUS"}


def main():
    t0 = time.time()
    decs = census(T)
    print(f"T={T}: {len(decs)} canonical decorations", flush=True)
    print("sanity ...", flush=True)
    sanity(census(2))
    print(f"sanity OK [{time.time() - t0:.0f}s]", flush=True)

    rules = ["equal", "exact1"] if T == 2 else ["equal"]
    jobs = [(i, dec, rule) for rule in rules for i, dec in enumerate(decs)]
    done = set()
    if os.path.exists(CKPT):
        for line in open(CKPT):
            try:
                r = json.loads(line)
                done.add((r["i"], r["rule"]))
            except Exception:
                pass
    jobs = [j for j in jobs if (j[0], j[2]) not in done]
    print(f"classify: {len(jobs)} to do ({len(done)} done)", flush=True)

    counts = {}
    with open(CKPT, "a") as out, mp.Pool(WORKERS) as pool:
        for k, rec in enumerate(pool.imap_unordered(classify_one, jobs,
                                                    chunksize=1)):
            counts[rec["verdict"]] = counts.get(rec["verdict"], 0) + 1
            out.write(json.dumps(rec) + "\n")
            if rec["verdict"] in ("SUSPICIOUS", "periodic-late"):
                out.flush()
                print(f"  *** {rec['verdict']}: decoration {rec['i']} "
                      f"({rec['rule']}) ***", flush=True)
            if (k + 1) % 50 == 0:
                out.flush()
                print(f"  {k + 1}/{len(jobs)} {counts} "
                      f"[{time.time() - t0:.0f}s]", flush=True)
    print(f"CLASSIFY DONE {counts} [{time.time() - t0:.0f}s]", flush=True)


if __name__ == "__main__":
    main()
