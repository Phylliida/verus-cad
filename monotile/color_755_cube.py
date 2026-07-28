"""canon 755 endgame: cube-and-conquer on the 7^3 box.

Monolithic 50M-conflict solve budgeted out (~50h). Same recipe as
cube_strag34.py: one-hot orientation vars + 5 phase-bit aux vars per
cell, split phase bits cell by cell, 200k conflicts per leaf, budget-
outs split deeper. Checkpointed to cube_755_done.jsonl (skip on
restart). A SAT leaf is an ALARM (it would mean 755 tiles 7^3 —
extract the patch!).

Run:  ./runpy.sh color_755_cube.py [workers=40]
"""
import json
import multiprocessing as mp
import os
import sys
import time

import arena2

WORKERS = int(sys.argv[1]) if len(sys.argv) > 1 else 40
CKPT = "cube_755_done.jsonl"
CONF_BUDGET = 200_000
DIMS = (7, 7, 7)

_S = {}


def build_cnf():
    canonical = json.load(open("color3d_canonical.json"))["canonical"]
    prof = canonical[755]
    census = json.load(open("faceeq3d_census.json"))
    T2E = {}
    for key, ei in census["triple_to_eq"].items():
        ax, o1, o2 = map(int, key.split(","))
        T2E[(ax, o1, o2)] = ei
    held = set(prof)
    bad = [[], [], []]
    for ax in range(3):
        for o1 in range(24):
            for o2 in range(24):
                if T2E[(ax, o1, o2)] not in held:
                    bad[ax].append((o1, o2))
    cnf, cells, idx, var = arena2.box_solver_cnf(DIMS, bad)
    ncells = len(cells)
    nbase = ncells * 24

    def bvar(ci, k):
        return nbase + ci * 5 + k + 1

    for ci in range(ncells):
        for o in range(24):
            v = var(ci, o)
            for k in range(5):
                if (o >> k) & 1:
                    cnf.append([-v, bvar(ci, k)])
                else:
                    cnf.append([-v, -bvar(ci, k)])
    return cnf, ncells, nbase, nbase + ncells * 5


def init_worker(cnf):
    from pysat.solvers import Cadical195
    _S["solver"] = Cadical195(bootstrap_with=cnf)


def solve_cube(cube):
    s = _S["solver"]
    s.conf_budget(CONF_BUDGET)
    r = s.solve_limited(assumptions=list(cube))
    if r is None:
        return (cube, "budget", None)
    if r:
        return (cube, "SAT", s.get_model())
    return (cube, "UNSAT", None)


def main():
    cnf, ncells, nbase, nvars = build_cnf()
    print(f"box {DIMS}: {nvars} vars, {len(cnf)} clauses", flush=True)
    order = [nbase + ci * 5 + k + 1
             for ci in range(ncells) for k in range(5)]
    done = set()
    if os.path.exists(CKPT):
        with open(CKPT) as f:
            for line in f:
                try:
                    done.add(tuple(json.loads(line)["cube"]))
                except Exception:
                    pass
        print(f"checkpoint: {len(done)} cubes done", flush=True)
    frontier = [()] if () not in done else []
    n_unsat, n_split = 0, 0
    t0 = time.time()
    with open(CKPT, "a") as out, \
            mp.Pool(WORKERS, initializer=init_worker,
                    initargs=(cnf,)) as pool:
        while frontier:
            batch, frontier = frontier, []
            for cube, verdict, model in pool.imap_unordered(
                    solve_cube, batch, chunksize=1):
                if verdict == "UNSAT":
                    n_unsat += 1
                    out.write(json.dumps({"cube": cube,
                                          "verdict": "UNSAT"}) + "\n")
                elif verdict == "SAT":
                    out.write(json.dumps({"cube": cube, "verdict": "SAT",
                                          "model": model}) + "\n")
                    out.flush()
                    print(f"*** ALARM: SAT cube {cube} — 755 TILES 7^3!",
                          flush=True)
                    return
                else:
                    d = len(cube)
                    if d >= len(order):
                        out.write(json.dumps(
                            {"cube": cube, "verdict": "budget-full"})
                            + "\n")
                        out.flush()
                        print(f"!!! budget-full at depth {d}: {cube}",
                              flush=True)
                        continue
                    n_split += 1
                    for sgn in (1, -1):
                        child = cube + (sgn * order[d],)
                        if child not in done:
                            frontier.append(child)
                out.flush()
            print(f"  unsat={n_unsat} splits={n_split} "
                  f"frontier={len(frontier)} [{time.time() - t0:.0f}s]",
                  flush=True)
    print(f"RESULT: UNSAT — canon 755 is EMPTY at 7^3 ({n_unsat} leaves) "
          f"[{time.time() - t0:.0f}s]", flush=True)


if __name__ == "__main__":
    main()
