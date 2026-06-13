"""Deep offline autopsy for arena-2 'suspicious' candidates.

The in-loop verifier gives up quickly (small conflict budgets, lattice
index <= 96). This tool re-examines one decoration with generous
budgets, in three phases:

  A/B. per canonical vector: high-budget 6^3 identification, then a
       deep period-confirm (index <= 512, more lattice tries),
  C.   rank-2 probe: simultaneous identification under PAIRS of short
       vectors -- a SAT pair gives a doubly-invariant patch whose held
       vectors usually complete to a full-rank lattice; all-UNSAT means
       no rank-2 invariant patch exists at 6^3 at all,
  D.   plain 8^3 tileability.

Usage:
    python3 deep_confirm.py '<json list of 54 entries of +-1>'
    python3 deep_confirm.py --log N    # N-th suspicious entry in arena2_log.json
"""
import itertools
import json
import sys
import time

import arena2
from arena2 import (CANON3, Verifier, box_sat, box_solver_cnf,
                    extract_grid, held_vectors, implied_lattices,
                    solve_lattice_torus)
from pysat.solvers import Glucose3


def box_sat_multi(dims, bad, identify, conf_budget=None):
    """box_sat with identification under several vectors at once."""
    cnf, cells, idx, var = box_solver_cnf(dims, bad)
    for v in identify:
        for c in cells:
            c2 = (c[0] + v[0], c[1] + v[1], c[2] + v[2])
            if c2 in idx:
                ci, c2i = idx[c], idx[c2]
                for o in range(24):
                    cnf.append([-var(ci, o), var(c2i, o)])
                    cnf.append([var(ci, o), -var(c2i, o)])
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
        return True, extract_grid(s.get_model(), cells, idx, var)


def deep_confirm_grid(V, grid, maxc, tag):
    held = held_vectors(grid, maxc=maxc, min_pairs=6)
    lats = implied_lattices(held, max_index=512, max_tries=16,
                            max_held=64)
    for B in lats:
        if B in V.failed_lattices:
            continue
        sat, qgrid = solve_lattice_torus(B, V.bad, V.selfbad,
                                         conf_budget=300_000)
        if sat:
            return B, qgrid, held
        V.failed_lattices.add(B)
    print(f"    [{tag}] {len(held)} held, {len(lats)} lattices tried, "
          f"none tiles; shortest held {sorted(held, key=lambda w: w[0]**2 + w[1]**2 + w[2]**2)[:6]}")
    return None, None, held


def deep(dec):
    V = Verifier(dec)
    print(f"orbit size: {arena2.orbit_size(V.placed)}")
    print("--- phase A/B: per-vector 6^3 identification + deep confirm")
    V.det6 = V._detector((6, 6, 6))
    s, cells, idx, var, sels = V.det6
    still = []
    for v in CANON3:
        t = time.time()
        s.conf_budget(300_000)
        r = s.solve_limited(assumptions=[sels[v]])
        if r is False:
            print(f"  v={v}: refuted at 6^3 [{time.time()-t:.0f}s]")
            continue
        if r is None:
            print(f"  v={v}: budget-out at 300k conflicts "
                  f"[{time.time()-t:.0f}s]")
            still.append(v)
            continue
        grid = extract_grid(s.get_model(), cells, idx, var)
        B, qgrid, held = deep_confirm_grid(V, grid, maxc=5, tag=f"v={v}")
        if B is not None:
            ix = B[0][0] * B[1][1] * B[2][2]
            print(f"  v={v}: CONFIRMED PERIODIC lattice {B} index {ix} "
                  f"[{time.time()-t:.0f}s]")
            V.close()
            return ("periodic", B)
        print(f"  v={v}: 6^3 SAT, unconfirmed [{time.time()-t:.0f}s]")
        still.append(v)

    print(f"--- phase C: rank-2 pair probe (still suspicious: {still})")
    short = [(0, 0, 2), (0, 2, 0), (2, 0, 0),
             (0, 1, 1), (0, 1, -1), (1, 0, 1),
             (1, 0, -1), (1, 1, 0), (1, -1, 0)]
    sat_pairs = []
    for v, w in itertools.combinations(short, 2):
        t = time.time()
        r, grid = box_sat_multi((6, 6, 6), V.bad, [v, w],
                                conf_budget=150_000)
        if r is True:
            sat_pairs.append((v, w))
            B, qgrid, held = deep_confirm_grid(V, grid, maxc=5,
                                               tag=f"pair {v},{w}")
            if B is not None:
                ix = B[0][0] * B[1][1] * B[2][2]
                print(f"  pair {v},{w}: SAT -> CONFIRMED PERIODIC "
                      f"lattice {B} index {ix} [{time.time()-t:.0f}s]")
                V.close()
                return ("periodic", B)
            print(f"  pair {v},{w}: SAT, rank-2 patch, unconfirmed "
                  f"[{time.time()-t:.0f}s]")
        elif r is False:
            print(f"  pair {v},{w}: UNSAT [{time.time()-t:.0f}s]")
        else:
            print(f"  pair {v},{w}: budget-out [{time.time()-t:.0f}s]")
    print(f"  rank-2 summary: {len(sat_pairs)} SAT pairs: {sat_pairs}")

    print("--- phase D: plain 8^3 tileability")
    t = time.time()
    r, _ = box_sat((8, 8, 8), V.bad, conf_budget=2_000_000)
    word = "SAT" if r is True else ("UNSAT" if r is False else "budget-out")
    print(f"  8^3 box: {word} [{time.time()-t:.0f}s]")
    V.close()
    return ("suspicious", still)


if __name__ == "__main__":
    if sys.argv[1] == "--log":
        with open("arena2_log.json") as f:
            log = json.load(f)
        dec = tuple(log["suspicious"][int(sys.argv[2])][0])
    else:
        dec = tuple(json.loads(sys.argv[1]))
    assert len(dec) == arena2.NPTS and all(x in (1, -1) for x in dec)
    t0 = time.time()
    res = deep(dec)
    print(f"result: {res}  [total {time.time()-t0:.0f}s]")
