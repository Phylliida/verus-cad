"""Phase 0 probe, part 3: EDGE-marked Wang cubes at K=1
(PLAN-corner-cubes.md open question 2).

M-edge model: each of the cube's 12 edges carries one of T colors. A
tiling is an orientation field omega: Z^3 -> Rot(cube) (24 rotations, no
reflections) such that at every lattice edge the 4 incident cube-edge
colors satisfy a rule:

  rule "equal"  — all 4 colors equal (the equality/gain semantics);
  rule "exact1" — exactly one of the 4 is a bump (color 1).

Structure notes (why edges differ from corners):
  * Edge-adjacent cubes differ by (0,+-1,+-1)-type vectors — even parity.
    The constraint graph splits into TWO DECOUPLED components (even cells
    and odd cells, each an FCC lattice).
  * Counting rules are NOT trivially dead here (unlike corners): a d^3
    box has ~3d^3 lattice edges, so exact-k density forces m = 3k marks
    per cube, and the all-identity witness additionally needs the marks
    balanced k per axis direction. Unbalanced m=3 decorations under
    exact1 are a priori open — hence the exact1 mode.

Edge indexing: e = (a, u, v) with a the edge's axis, (u, v) the values of
the other two coordinates (sorted axis order); eidx = a*4 + u*2 + v.

Census: Burnside on edges gives (2^12 + 6*2^3 + 3*2^6 + 8*2^4 + 6*2^7)/24
= 218 canonical decorations at T=2 (orbit-enumeration asserted). For
exact1 only m=3 decorations are density-viable: C(12,3) = 220 subsets.

Tiers: torus cap 4 -> box 3^3 -> box 4^3 -> torus cap 8 -> box 5^3
-> SUSPICIOUS (same schedule as corner3d.py).

Sanity (runs before classifying):
  * rotation action on edges faithful;
  * census 218 at T=2;
  * empty/full tile at period 1 (equal), UNSAT at 1x1x1 (exact1);
  * single-marked edge under equal: explicit period-2 construction
    (S = x-parallel lattice edges at even y,z — every cube has exactly
    one) + solver agrees on the 2x2x2 torus;
  * axis-balanced 3-mark decoration under exact1: all-identity period-1;
  * encoder brute-force cross-checks: (1,1,1) torus for all canonicals,
    (1,1,2) torus (576 orientation pairs) on 60 random decorations.

Checkpointed jsonl; safe to kill and relaunch.

Run:  ./runpy.sh edge3d.py [T=2] [workers=8]
(exact1 m=3 campaign only runs at T=2; T=3 is equal-rule only)
"""
import itertools
import json
import multiprocessing as mp
import os
import random
import sys
import time

import numpy as np
from pysat.solvers import Glucose3

T = int(sys.argv[1]) if len(sys.argv) > 1 else 2
WORKERS = int(sys.argv[2]) if len(sys.argv) > 2 else 8
sys.argv = ["corner3d.py"]  # keep corner3d's module-level argv parse benign
import corner3d as C3

CKPT = f"edge3d_T{T}_results.jsonl"

ROTS, CORNERS = C3.ROTS, C3.CORNERS
rot_corner = C3.rot_corner

# ------------------------------------------------------------- geometry

EDGES = []  # (a, u, v); u along the smaller of the two non-a axes
for a in range(3):
    others = [b for b in range(3) if b != a]
    for u in (0, 1):
        for v in (0, 1):
            EDGES.append((a, u, v))


def eidx(e):
    return e[0] * 4 + e[1] * 2 + e[2]


def edge_endpoints(e):
    a, u, v = e
    others = [b for b in range(3) if b != a]
    p0 = [0, 0, 0]
    p0[others[0]] = u
    p0[others[1]] = v
    p1 = list(p0)
    p1[a] = 1
    return tuple(p0), tuple(p1)


def edge_of_endpoints(q0, q1):
    a = next(i for i in range(3) if q0[i] != q1[i])
    others = [b for b in range(3) if b != a]
    lo = tuple(min(q0[i], q1[i]) for i in range(3))
    return (a, lo[others[0]], lo[others[1]])


# SIGE[o][e] = edge index rotation o moves edge e to
SIGE = []
for M in ROTS:
    row = []
    for e in EDGES:
        p0, p1 = edge_endpoints(e)
        q0, q1 = rot_corner(M, p0), rot_corner(M, p1)
        row.append(eidx(edge_of_endpoints(q0, q1)))
    SIGE.append(row)
SIGEINV = []
for o in range(24):
    inv = [0] * 12
    for e in range(12):
        inv[SIGE[o][e]] = e
    SIGEINV.append(inv)


def show_table(dec):
    """show[o][p] = color a cell in orientation o shows at edge-position p."""
    return [tuple(dec[SIGEINV[o][p]] for p in range(12)) for o in range(24)]


def canonical(dec):
    return min(tuple(dec[SIGE[o][p]] for p in range(12)) for o in range(24))


def census(t, marks=None):
    out = set()
    for dec in itertools.product(range(t), repeat=12):
        if marks is not None and sum(dec) != marks:
            continue
        out.add(canonical(dec))
    return sorted(out)


def edge_incident(a, base, dims, periodic):
    """The 4 (cell, edge-position) pairs meeting at lattice edge (a, base)."""
    others = [b for b in range(3) if b != a]
    for i in (0, 1):
        for j in (0, 1):
            c = list(base)
            c[others[0]] -= i
            c[others[1]] -= j
            if periodic:
                c = tuple(c[k] % dims[k] for k in range(3))
            yield tuple(c), eidx((a, i, j))


def all_lattice_edges(dims, periodic):
    """Edges parallel to each axis. Box: only edges with all 4 incident
    cells present (non-a coords interior)."""
    out = []
    for a in range(3):
        others = [b for b in range(3) if b != a]
        ranges = []
        for k in range(3):
            if k == a:
                ranges.append(range(dims[k]))
            elif periodic:
                ranges.append(range(dims[k]))
            else:
                ranges.append(range(1, dims[k]))
        for base in itertools.product(*ranges):
            out.append((a, base))
    return out


# ------------------------------------------------------------- SAT core

def edge_sat(show, dims, rule, periodic, conf_budget=None):
    """Tri-state: (True, grid) / (False, None) / (None, None) on budget."""
    d1, d2, d3 = dims
    cells = [(x, y, z) for x in range(d1) for y in range(d2)
             for z in range(d3)]
    idx = {c: i for i, c in enumerate(cells)}
    edges = all_lattice_edges(dims, periodic)

    def ovar(ci, o):
        return ci * 24 + o + 1

    cnf = []
    for ci in range(len(cells)):
        cnf.append([ovar(ci, o) for o in range(24)])
        for o1 in range(24):
            for o2 in range(o1 + 1, 24):
                cnf.append([-ovar(ci, o1), -ovar(ci, o2)])

    top = len(cells) * 24
    if rule == "equal":
        tmax = max(max(row) for row in show)

        def evar(ei, t):
            return top + ei * (tmax + 1) + t + 1

        for ei, (a, base) in enumerate(edges):
            cnf.append([evar(ei, t) for t in range(tmax + 1)])
            for t1 in range(tmax + 1):
                for t2 in range(t1 + 1, tmax + 1):
                    cnf.append([-evar(ei, t1), -evar(ei, t2)])
            for c, p in edge_incident(a, base, dims, periodic):
                ci = idx[c]
                for o in range(24):
                    cnf.append([-ovar(ci, o), evar(ei, show[o][p])])
    elif rule == "exact1":
        bumpers = [[o for o in range(24) if show[o][p] == 1]
                   for p in range(12)]

        def bvar(ci, p):
            return top + ci * 12 + p + 1

        for ci in range(len(cells)):
            for p in range(12):
                for o in bumpers[p]:
                    cnf.append([-ovar(ci, o), bvar(ci, p)])
                cnf.append([-bvar(ci, p)] + [ovar(ci, o)
                                             for o in bumpers[p]])
        for a, base in edges:
            lits = [bvar(idx[c], p)
                    for c, p in edge_incident(a, base, dims, periodic)]
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
    """Pure-python witness verification."""
    for a, base in all_lattice_edges(dims, True):
        vals = [show[grid[c]][p]
                for c, p in edge_incident(a, base, dims, True)]
        if rule == "equal" and len(set(vals)) != 1:
            return False
        if rule == "exact1" and sum(vals) != 1:
            return False
    return True


# ------------------------------------------------------------- sanity

def sanity(decs2):
    for o in range(24):
        assert sorted(SIGE[o]) == list(range(12))
    assert len({tuple(row) for row in SIGE}) == 24  # faithful on edges
    print("  rotation action on edges OK (faithful, 24)", flush=True)

    want = {2: 218, 3: 22815}[T]
    assert len(decs2) == want, len(decs2)
    print(f"  census size OK ({want} @ T={T})", flush=True)

    for dec in [(0,) * 12, (1,) * 12]:
        show = show_table(dec)
        ok, grid = edge_sat(show, (1, 1, 1), "equal", True, 10_000)
        assert ok and check_torus(show, (1, 1, 1), grid, "equal")
        ok, _ = edge_sat(show, (1, 1, 1), "exact1", True, 10_000)
        assert ok is False  # m=0 / m=12 both != 3
    print("  empty/full: period-1 equal, UNSAT exact1 OK", flush=True)

    # single-marked edge under equal: period-2 construction.
    # S = x-parallel lattice edges at even (y, z); every unit cube has
    # exactly one. Cell c marks edge-position (0, c_y mod 2, c_z mod 2).
    dec = (1,) + (0,) * 11
    show = show_table(dec)
    grid = {}
    for c in CORNERS:
        target = eidx((0, c[1] % 2, c[2] % 2))
        o = next(o for o in range(24) if SIGE[o][0] == target)
        grid[c] = o
    assert check_torus(show, (2, 2, 2), grid, "equal")
    ok, grid2 = edge_sat(show, (2, 2, 2), "equal", True, 10_000)
    assert ok and check_torus(show, (2, 2, 2), grid2, "equal")
    print("  single-marked edge equal: period-2 OK + solver agrees",
          flush=True)

    # axis-balanced 3-mark decoration under exact1: all-identity works —
    # each lattice edge sees exactly the one mark of its axis.
    dec = tuple(1 if p in (0, 4, 8) else 0 for p in range(12))
    show = show_table(dec)
    grid = {c: 0 for c in CORNERS}  # orientation 0 everywhere
    assert check_torus(show, (2, 2, 2), grid, "exact1")
    ok, grid2 = edge_sat(show, (1, 1, 1), "exact1", True, 10_000)
    assert ok and check_torus(show, (1, 1, 1), grid2, "exact1")
    print("  balanced 3-mark exact1: period-1 (all-identity) OK",
          flush=True)

    # brute-force cross-checks (equal rule)
    for dec in decs2:
        show = show_table(dec)
        brute = any(check_torus(show, (1, 1, 1), {(0, 0, 0): o}, "equal")
                    for o in range(24))
        ok, _ = edge_sat(show, (1, 1, 1), "equal", True, 10_000)
        assert bool(ok) == brute
    print("  (1,1,1)-torus brute-force OK (218/218)", flush=True)

    rng = random.Random(11)
    for trial in range(60):
        dec = tuple(rng.randrange(2) for _ in range(12))
        show = show_table(dec)
        brute = False
        for o1, o2 in itertools.product(range(24), repeat=2):
            grid = {(0, 0, 0): o1, (0, 0, 1): o2}
            if check_torus(show, (1, 1, 2), grid, "equal"):
                brute = True
                break
        ok, grid = edge_sat(show, (1, 1, 2), "equal", True, 10_000)
        assert bool(ok) == brute, (dec, ok, brute)
    print("  (1,1,2)-torus brute-force OK (60/60)", flush=True)


# ------------------------------------------------------------- classify

def torus_sweep(show, rule, cap, budget):
    dims = sorted(itertools.product(range(1, cap + 1), repeat=3),
                  key=lambda d: (d[0] * d[1] * d[2], d))
    for d in dims:
        ok, grid = edge_sat(show, d, rule, True, budget)
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
        return {"i": i, "rule": rule, "verdict": "periodic",
                "d": list(d), "grid": [grid[c] for c in sorted(grid)]}
    for n, budget in ((3, 200_000), (4, 2_000_000)):
        ok, _ = edge_sat(show, (n, n, n), rule, False, budget)
        if ok is False:
            return {"i": i, "rule": rule, "verdict": f"empty{n}"}
    hit = torus_sweep(show, rule, 8, 50_000)
    if hit:
        d, grid = hit
        assert check_torus(show, d, grid, rule)
        return {"i": i, "rule": rule, "verdict": "periodic-late",
                "d": list(d), "grid": [grid[c] for c in sorted(grid)]}
    ok, _ = edge_sat(show, (5, 5, 5), rule, False, 20_000_000)
    if ok is False:
        return {"i": i, "rule": rule, "verdict": "empty5"}
    return {"i": i, "rule": rule, "verdict": "SUSPICIOUS"}


def main():
    t0 = time.time()
    decs_equal = census(T)
    decs_exact1 = census(2, marks=3) if T == 2 else []
    print(f"T={T}: {len(decs_equal)} canonical (equal)"
          + (f", {len(decs_exact1)} canonical m=3 (exact1)"
             if T == 2 else ""), flush=True)
    print("sanity ...", flush=True)
    sanity(decs_equal)
    print(f"sanity OK [{time.time() - t0:.0f}s]", flush=True)

    jobs = ([(i, dec, "equal") for i, dec in enumerate(decs_equal)]
            + [(i, dec, "exact1") for i, dec in enumerate(decs_exact1)])
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
