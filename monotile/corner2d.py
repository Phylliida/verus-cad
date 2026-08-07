"""2D warmup for the corner chirality conjecture (Phase B).

Vertex-marked Wang squares: each of the square's 4 corners carries one of
T colors; a tiling is an orientation field omega: Z^2 -> C4 (4 rotations,
NO reflections) such that at every lattice vertex the 4 incident corner
colors are all equal. Equivalently: vertex colorings ell: Z^2 -> [T]
where every unit square's 4-corner pattern is a rotation of the
decoration.

Conjecture (mirrors the 3D one): tileable <=> achiral <=> period-(2,2)
witness. Chiral decorations exist at T >= 3 (C4 orbits of T^4:
6 at T=2 — all achiral; 24 at T=3 with 3 chiral pairs; 70 at T=4).

Achirality here: mirror image (reverse cyclic order) is a rotation.

Tiers: torus sweep cap 4 -> box 3x3 -> box 4x4 -> torus cap 8 ->
box 5x5 -> SUSPICIOUS. Plus a direct check: achiral canonicals must have
period-(2,2) witnesses; chiral ones must not.

Sanity: census sizes (6/24/70), empty/full tile at period 1,
single-mark tiles at period 2 (2Z^2), encoder brute-force cross-check on
the (1,2) torus (16 orientation pairs) for 60 random decorations.

Run:  ./runpy.sh corner2d.py [T=3] [workers=8]
"""
import itertools
import json
import multiprocessing as mp
import os
import random
import sys
import time

from pysat.solvers import Glucose3

T = int(sys.argv[1]) if len(sys.argv) > 1 else 3
WORKERS = int(sys.argv[2]) if len(sys.argv) > 2 else 8
CKPT = f"corner2d_T{T}_results.jsonl"

# corners of the unit square: position p = x + 2y (x-fastest)
CORNERS = [(x, y) for y in (0, 1) for x in (0, 1)]


def cidx(e):
    return e[0] + 2 * e[1]


# C4 rotations on corners: rot o maps (x,y) corner; rot1: (x,y)->(y,1-x)
def rot_corner(o, c):
    x, y = c
    for _ in range(o):
        x, y = y, 1 - x
    return (x, y)


SIG = [[CORNERS.index(rot_corner(o, c)) for c in CORNERS] for o in range(4)]
SIGINV = []
for o in range(4):
    inv = [0] * 4
    for p in range(4):
        inv[SIG[o][p]] = p
    SIGINV.append(inv)

MIRROR = [CORNERS.index((1 - c[0], c[1])) for c in CORNERS]


def show_table(dec):
    return [tuple(dec[SIGINV[o][p]] for p in range(4)) for o in range(4)]


def canonical(dec):
    return min(tuple(dec[SIG[o][p]] for p in range(4)) for o in range(4))


def achiral(dec):
    mir = tuple(dec[MIRROR[p]] for p in range(4))
    return any(all(mir[p] == dec[SIG[o][p]] for p in range(4))
               for o in range(4))


def census(t):
    return sorted({canonical(dec)
                   for dec in itertools.product(range(t), repeat=4)})


def corner_sat(show, dims, periodic, conf_budget=None):
    """Tri-state: (True, grid) / (False, None) / (None, None)."""
    d1, d2 = dims
    cells = [(x, y) for x in range(d1) for y in range(d2)]
    idx = {c: i for i, c in enumerate(cells)}

    def ovar(ci, o):
        return ci * 4 + o + 1

    if periodic:
        verts = list(cells)
    else:  # box: vertices with all 4 incident cells present
        verts = [(x, y) for x in range(1, d1) for y in range(1, d2)]

    tmax = max(max(row) for row in show)
    top = len(cells) * 4

    def cvar(vi, t):
        return top + vi * (tmax + 1) + t + 1

    cnf = []
    for ci in range(len(cells)):
        cnf.append([ovar(ci, o) for o in range(4)])
        for o1 in range(4):
            for o2 in range(o1 + 1, 4):
                cnf.append([-ovar(ci, o1), -ovar(ci, o2)])
    for vi, v in enumerate(verts):
        cnf.append([cvar(vi, t) for t in range(tmax + 1)])
        for t1 in range(tmax + 1):
            for t2 in range(t1 + 1, tmax + 1):
                cnf.append([-cvar(vi, t1), -cvar(vi, t2)])
        for e in CORNERS:
            if periodic:
                c = ((v[0] - e[0]) % d1, (v[1] - e[1]) % d2)
            else:
                c = (v[0] - e[0], v[1] - e[1])
            ci = idx[c]
            p = cidx(e)
            for o in range(4):
                cnf.append([-ovar(ci, o), cvar(vi, show[o][p])])
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
            grid[c] = next(o for o in range(4) if ovar(ci, o) in pos)
        return True, grid


def check_torus(show, dims, grid):
    d1, d2 = dims
    for vx in range(d1):
        for vy in range(d2):
            vals = set()
            for e in CORNERS:
                c = ((vx - e[0]) % d1, (vy - e[1]) % d2)
                vals.add(show[grid[c]][cidx(e)])
            if len(vals) != 1:
                return False
    return True


def sanity(decs):
    want = {2: 6, 3: 24, 4: 70}[T]
    assert len(decs) == want, len(decs)
    print(f"  census size OK ({want} @ T={T})", flush=True)
    for dec in [(0,) * 4, (1,) * 4]:
        show = show_table(dec)
        ok, grid = corner_sat(show, (1, 1), True, 10_000)
        assert ok and check_torus(show, (1, 1), grid)
    # single mark: period-2 via 2Z^2
    dec = (1, 0, 0, 0)
    show = show_table(dec)
    grid = {}
    for c in CORNERS:
        o = next(o for o in range(4) if SIG[o][0] == cidx(c))
        grid[c] = o
    assert check_torus(show, (2, 2), grid)
    print("  empty/full/single-mark OK", flush=True)
    # brute-force cross-check on the (1,2) torus
    rng = random.Random(3)
    for _ in range(60):
        dec = tuple(rng.randrange(T) for _ in range(4))
        show = show_table(dec)
        brute = False
        for o1, o2 in itertools.product(range(4), repeat=2):
            grid = {(0, 0): o1, (0, 1): o2}
            if check_torus(show, (1, 2), grid):
                brute = True
                break
        ok, grid = corner_sat(show, (1, 2), True, 10_000)
        assert bool(ok) == brute, (dec, ok, brute)
    print("  (1,2)-torus brute-force OK (60/60)", flush=True)


def torus_sweep(show, cap, budget):
    dims = sorted(itertools.product(range(1, cap + 1), repeat=2),
                  key=lambda d: (d[0] * d[1], d))
    for d in dims:
        ok, grid = corner_sat(show, d, True, budget)
        if ok:
            return d, grid
    return None


def classify_one(job):
    i, dec = job
    show = show_table(dec)
    hit = torus_sweep(show, 4, 20_000)
    if hit:
        d, grid = hit
        assert check_torus(show, d, grid)
        return {"i": i, "verdict": "periodic", "d": list(d),
                "grid": [grid[c] for c in sorted(grid)],
                "achiral": achiral(dec)}
    for n, budget in ((3, 200_000), (4, 2_000_000)):
        ok, _ = corner_sat(show, (n, n), False, budget)
        if ok is False:
            return {"i": i, "verdict": f"empty{n}", "achiral": achiral(dec)}
    hit = torus_sweep(show, 8, 50_000)
    if hit:
        d, grid = hit
        assert check_torus(show, d, grid)
        return {"i": i, "verdict": "periodic-late", "d": list(d),
                "grid": [grid[c] for c in sorted(grid)],
                "achiral": achiral(dec)}
    ok, _ = corner_sat(show, (5, 5), False, 20_000_000)
    if ok is False:
        return {"i": i, "verdict": "empty5", "achiral": achiral(dec)}
    return {"i": i, "verdict": "SUSPICIOUS", "achiral": achiral(dec)}


def main():
    t0 = time.time()
    decs = census(T)
    print(f"T={T}: {len(decs)} canonical decorations "
          f"({sum(achiral(d) for d in decs)} achiral)", flush=True)
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
                print(f"  *** {rec['verdict']}: {rec['i']} ***", flush=True)
    print(f"CLASSIFY DONE {counts} [{time.time() - t0:.0f}s]", flush=True)

    # the conjecture check
    recs = [json.loads(l) for l in open(CKPT)]
    mism = [(r["i"], r["achiral"], r["verdict"]) for r in recs
            if r["achiral"] != r["verdict"].startswith("periodic")]
    late = [(r["i"], r["d"]) for r in recs
            if r["verdict"] == "periodic" and tuple(r["d"]) != (2, 2)
            and r["achiral"]]
    print(f"conjecture mismatches (achiral != periodic): {len(mism)}")
    for m in mism[:20]:
        print("   MISMATCH:", m)
    p2 = [r["i"] for r in recs if r["verdict"].startswith("periodic")
          and max(r["d"]) <= 2]
    print(f"periodic with period <= 2: {len(p2)} / "
          f"{sum(1 for r in recs if r['verdict'].startswith('periodic'))}")


if __name__ == "__main__":
    main()
