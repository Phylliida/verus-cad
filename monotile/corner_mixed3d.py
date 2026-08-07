"""Phase 0 probe, part 2: MIXED face+corner Wang cubes at K=1, T=2.

M-mixed (K=1): each cube carries 6 face colors AND 8 corner colors
(14 bits, T=2). Matching rules: at every shared face the two face colors
are equal (equal-color face semantics); at every lattice vertex the 8
incident corner colors are all equal. The two constraint sets are
independent; the decoration just has both parts. 776 rotation-canonical
decorations (Burnside cross-checked).

Encoder: one-hot orientation vars per cell; one-hot color vars per
interface (shared face) and per lattice vertex, with binary channeling
clauses from orientations. Same tier schedule as corner3d.py:
torus cap 4 -> box 3^3 -> box 4^3 -> torus cap 8 -> box 5^3 -> SUSPICIOUS.

Sanity: census count 776; empty/full tile at period 1; corner-only
projection (all faces color 0, single marked corner) reproduces the
corner3d period-2 witness; brute-force cross-check of the encoder on the
(1,1,2) torus (576 orientation pairs, self- and double-adjacency) for
200 random decorations.

Checkpointed jsonl; safe to kill and relaunch.

Run:  ./runpy.sh corner_mixed3d.py [workers=8]
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

sys.argv = ["corner3d.py"]  # keep corner3d's module-level argv parse benign
import corner3d as C3

WORKERS = int(sys.argv[1]) if len(sys.argv) > 1 else 8
CKPT = "corner_mixed3d_T2_results.jsonl"

SIG, CORNERS, ROTS = C3.SIG, C3.CORNERS, C3.ROTS
cidx = C3.cidx
show_corner = C3.show_table

# faces: f = 2*axis + (0 if +side else 1), matching faceeq3d's convention
FACES = []
for a in range(3):
    for s in (0, 1):
        v = [0, 0, 0]
        v[a] = 1 if s == 0 else -1
        FACES.append(tuple(v))


def face_index(v):
    a = max(range(3), key=lambda i: abs(v[i]))
    return 2 * a + (0 if v[a] > 0 else 1)


SIGF = [[face_index(tuple(int(x) for x in M @ np.array(f)))
         for f in FACES] for M in ROTS]
SIGFINV = []
for o in range(24):
    inv = [0] * 6
    for f in range(6):
        inv[SIGF[o][f]] = f
    SIGFINV.append(inv)


def show_tables(dec):
    """dec: 14-tuple (6 face colors, then 8 corner colors)."""
    fd = dec[:6]
    showf = [tuple(fd[SIGFINV[o][f]] for f in range(6)) for o in range(24)]
    return showf, show_corner(dec[6:])


def canonical(dec):
    fd, cd = dec[:6], dec[6:]
    return min(tuple(fd[SIGF[o][f]] for f in range(6))
               + tuple(cd[SIG[o][p]] for p in range(8))
               for o in range(24))


def census():
    return sorted({canonical(dec)
                   for dec in itertools.product((0, 1), repeat=14)})


# ------------------------------------------------------------- SAT core

def mixed_sat(showf, showc, dims, periodic, conf_budget=None):
    """Tri-state: (True, grid) / (False, None) / (None, None) on budget."""
    d1, d2, d3 = dims
    cells = [(x, y, z) for x in range(d1) for y in range(d2)
             for z in range(d3)]
    idx = {c: i for i, c in enumerate(cells)}
    ncell = len(cells)

    def ovar(ci, o):
        return ci * 24 + o + 1

    if periodic:
        verts = list(cells)
    else:
        verts = [(x, y, z) for x in range(1, d1) for y in range(1, d2)
                 for z in range(1, d3)]

    # interfaces: (cell, axis) -> neighbor in +axis direction
    ifaces = []
    for c in cells:
        for a in range(3):
            n = list(c)
            n[a] += 1
            if periodic:
                n[a] %= dims[a]
                ifaces.append((c, a, tuple(n)))
            elif n[a] < dims[a]:
                ifaces.append((c, a, tuple(n)))

    cnf = []
    for ci in range(ncell):
        cnf.append([ovar(ci, o) for o in range(24)])
        for o1 in range(24):
            for o2 in range(o1 + 1, 24):
                cnf.append([-ovar(ci, o1), -ovar(ci, o2)])

    top = ncell * 24

    def ivar(ii, t):
        return top + ii * 2 + t + 1

    for ii, (c, a, cn) in enumerate(ifaces):
        cnf.append([ivar(ii, 0), ivar(ii, 1)])
        cnf.append([-ivar(ii, 0), -ivar(ii, 1)])
        fa, fb = 2 * a, 2 * a + 1
        ci, cni = idx[c], idx[cn]
        for o in range(24):
            cnf.append([-ovar(ci, o), ivar(ii, showf[o][fa])])
            cnf.append([-ovar(cni, o), ivar(ii, showf[o][fb])])

    top += len(ifaces) * 2

    def cvar(vi, t):
        return top + vi * 2 + t + 1

    for vi, v in enumerate(verts):
        cnf.append([cvar(vi, 0), cvar(vi, 1)])
        cnf.append([-cvar(vi, 0), -cvar(vi, 1)])
        for e in CORNERS:
            if periodic:
                c = ((v[0] - e[0]) % d1, (v[1] - e[1]) % d2,
                     (v[2] - e[2]) % d3)
            else:
                c = (v[0] - e[0], v[1] - e[1], v[2] - e[2])
            ci = idx[c]
            p = cidx(e)
            for o in range(24):
                cnf.append([-ovar(ci, o), cvar(vi, showc[o][p])])

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


def check_torus(showf, showc, dims, grid):
    """Pure-python witness verification: faces AND corners."""
    d1, d2, d3 = dims
    for c in itertools.product(range(d1), range(d2), range(d3)):
        o = grid[c]
        for a in range(3):
            n = list(c)
            n[a] = (n[a] + 1) % dims[a]
            on = grid[tuple(n)]
            if showf[o][2 * a] != showf[on][2 * a + 1]:
                return False
        vals = set()
        for e in CORNERS:
            cc = ((c[0] - e[0]) % d1, (c[1] - e[1]) % d2,
                  (c[2] - e[2]) % d3)
            vals.add(showc[grid[cc]][cidx(e)])
        if len(vals) != 1:
            return False
    return True


# ------------------------------------------------------------- sanity

def sanity(decs):
    assert len(decs) == 776, len(decs)
    print("  census size OK (776 mixed canonical)", flush=True)

    for dec in [(0,) * 14, (1,) * 14]:
        showf, showc = show_tables(dec)
        ok, grid = mixed_sat(showf, showc, (1, 1, 1), True, 10_000)
        assert ok and check_torus(showf, showc, (1, 1, 1), grid)
    print("  empty/full mixed decorations: period-1 OK", flush=True)

    # corner-only projection: faces all 0, single marked corner must
    # reproduce the corner3d period-2 witness
    dec = (0,) * 6 + (1,) + (0,) * 7
    showf, showc = show_tables(dec)
    ok, grid = mixed_sat(showf, showc, (2, 2, 2), True, 10_000)
    assert ok and check_torus(showf, showc, (2, 2, 2), grid)
    print("  corner-only projection: period-2 OK", flush=True)

    # brute-force cross-check on the (1,1,2) torus: 576 orientation pairs
    rng = random.Random(7)
    for trial in range(200):
        dec = tuple(rng.randrange(2) for _ in range(14))
        showf, showc = show_tables(dec)
        brute = False
        for o1, o2 in itertools.product(range(24), repeat=2):
            grid = {(0, 0, 0): o1, (0, 0, 1): o2}
            if check_torus(showf, showc, (1, 1, 2), grid):
                brute = True
                break
        ok, grid = mixed_sat(showf, showc, (1, 1, 2), True, 10_000)
        assert bool(ok) == brute, (dec, ok, brute)
        if ok:
            assert check_torus(showf, showc, (1, 1, 2), grid)
    print("  (1,1,2)-torus brute-force cross-check OK (200/200)",
          flush=True)


# ------------------------------------------------------------- classify

def torus_sweep(showf, showc, cap, budget):
    dims = sorted(itertools.product(range(1, cap + 1), repeat=3),
                  key=lambda d: (d[0] * d[1] * d[2], d))
    for d in dims:
        ok, grid = mixed_sat(showf, showc, d, True, budget)
        if ok:
            return d, grid
    return None


def classify_one(job):
    i, dec = job
    showf, showc = show_tables(dec)
    hit = torus_sweep(showf, showc, 4, 20_000)
    if hit:
        d, grid = hit
        assert check_torus(showf, showc, d, grid)
        return {"i": i, "verdict": "periodic", "d": list(d),
                "grid": [grid[c] for c in sorted(grid)]}
    for n, budget in ((3, 200_000), (4, 2_000_000)):
        ok, _ = mixed_sat(showf, showc, (n, n, n), False, budget)
        if ok is False:
            return {"i": i, "verdict": f"empty{n}"}
    hit = torus_sweep(showf, showc, 8, 50_000)
    if hit:
        d, grid = hit
        assert check_torus(showf, showc, d, grid)
        return {"i": i, "verdict": "periodic-late", "d": list(d),
                "grid": [grid[c] for c in sorted(grid)]}
    ok, _ = mixed_sat(showf, showc, (5, 5, 5), False, 20_000_000)
    if ok is False:
        return {"i": i, "verdict": "empty5"}
    return {"i": i, "verdict": "SUSPICIOUS"}


def main():
    t0 = time.time()
    decs = census()
    print(f"mixed T=2: {len(decs)} canonical decorations", flush=True)
    print("sanity ...", flush=True)
    sanity(decs)
    print(f"sanity OK [{time.time() - t0:.0f}s]", flush=True)

    done = set()
    if os.path.exists(CKPT):
        for line in open(CKPT):
            try:
                done.add(json.loads(line)["i"])
            except Exception:
                pass
    jobs = [(i, dec) for i, dec in enumerate(decs) if i not in done]
    print(f"classify: {len(jobs)} to do ({len(done)} done)", flush=True)

    counts = {}
    with open(CKPT, "a") as out, mp.Pool(WORKERS) as pool:
        for k, rec in enumerate(pool.imap_unordered(classify_one, jobs,
                                                    chunksize=1)):
            counts[rec["verdict"]] = counts.get(rec["verdict"], 0) + 1
            out.write(json.dumps(rec) + "\n")
            if rec["verdict"] in ("SUSPICIOUS", "periodic-late"):
                out.flush()
                print(f"  *** {rec['verdict']}: decoration {rec['i']} ***",
                      flush=True)
            if (k + 1) % 100 == 0:
                out.flush()
                print(f"  {k + 1}/{len(jobs)} {counts} "
                      f"[{time.time() - t0:.0f}s]", flush=True)
    print(f"CLASSIFY DONE {counts} [{time.time() - t0:.0f}s]", flush=True)


if __name__ == "__main__":
    main()
