"""anyk-02 endgame v2: cube-and-conquer on k2_static.cnf.

The monolithic --lrat run produced a 28GB partial cert in 15h (the K=3
lesson replayed: monolithic certs don't scale; per-cube certs are tiny).
This driver splits on the 24 decoration vars (assumptions-based, no file
juggling): base depth `D0` (2^D0 cubes), each cube solved with a conflict
budget; budget-outs split one var deeper, recursively. UNSAT leaves are
recorded (cert regeneration per leaf comes in the anyk-03 stage — tiny
DIMACS + cadical --lrat each). A SAT cube ends the run with the witness
decoration (a candidate the CEGIS missed — feed to the verifier).

Checkpointed: cube_k2_done.jsonl records finished cubes (skip on restart).

Run:  ./runpy.sh cube_k2.py [workers=20]
"""
import json
import multiprocessing as mp
import os
import sys
import time

WORKERS = int(sys.argv[1]) if len(sys.argv) > 1 else 20
CKPT = "cube_k2_done.jsonl"
CNF_FILE = "k2_static.cnf"
NPTS = 24
BASE_DEPTH = 6
CONF_BUDGET = 2_000_000

_S = {}


def init_worker():
    from pysat.formula import CNF
    from pysat.solvers import Cadical195
    cnf = CNF(from_file=CNF_FILE)
    _S["solver"] = Cadical195(bootstrap_with=cnf)


def solve_cube(cube):
    """cube: tuple of signed literals over vars 1..24. Returns
    (cube, verdict, model-or-None)."""
    s = _S["solver"]
    s.conf_budget(CONF_BUDGET)
    r = s.solve_limited(assumptions=list(cube))
    if r is None:
        return (cube, "budget", None)
    if r:
        model = s.get_model()
        dec = [1 if (i + 1) in set(x for x in model if x > 0) else -1
               for i in range(NPTS)]
        return (cube, "SAT", dec)
    return (cube, "UNSAT", None)


def main():
    done = set()
    if os.path.exists(CKPT):
        with open(CKPT) as f:
            for line in f:
                try:
                    done.add(tuple(json.loads(line)["cube"]))
                except Exception:
                    pass
    # base cubes: all sign patterns on vars 1..BASE_DEPTH
    frontier = []
    for bits in range(1 << BASE_DEPTH):
        cube = tuple((i + 1) if (bits >> i) & 1 else -(i + 1)
                     for i in range(BASE_DEPTH))
        if cube not in done:
            frontier.append(cube)
    print(f"base cubes {1 << BASE_DEPTH}, done {len(done)}, "
          f"todo {len(frontier)}", flush=True)
    t0 = time.time()
    n_unsat, n_split = 0, 0
    sat_hits = []
    out = open(CKPT, "a")
    with mp.Pool(WORKERS, initializer=init_worker) as pool:
        while frontier:
            batch, frontier = frontier, []
            for cube, verdict, dec in pool.imap_unordered(
                    solve_cube, batch, chunksize=1):
                if verdict == "UNSAT":
                    n_unsat += 1
                    out.write(json.dumps({"cube": cube,
                                          "verdict": "UNSAT"}) + "\n")
                    out.flush()
                elif verdict == "SAT":
                    sat_hits.append(dec)
                    print(f"*** SAT *** cube={cube} dec={dec}", flush=True)
                    out.write(json.dumps({"cube": cube, "verdict": "SAT",
                                          "dec": dec}) + "\n")
                    out.flush()
                else:
                    d = len(cube)
                    if d >= NPTS:
                        print(f"!!! budget-out at full depth: {cube}",
                              flush=True)
                        out.write(json.dumps({"cube": cube,
                                              "verdict": "budget-full"})
                                  + "\n")
                        continue
                    n_split += 1
                    frontier.append(cube + ((d + 1),))
                    frontier.append(cube + (-(d + 1),))
                print(f"  unsat={n_unsat} splits={n_split} "
                      f"frontier={len(frontier)} sat={len(sat_hits)} "
                      f"[{time.time() - t0:.0f}s]", flush=True)
            if sat_hits:
                break
    if sat_hits:
        print(f"RESULT: SAT — {len(sat_hits)} witness(es); "
              f"K=2 library incomplete, feed to verifier", flush=True)
    else:
        print(f"RESULT: UNSAT — K=2 search CLOSED "
              f"({n_unsat} cubes) [{time.time() - t0:.0f}s]", flush=True)


if __name__ == "__main__":
    main()
