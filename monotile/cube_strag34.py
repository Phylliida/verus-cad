"""anyk-M4 stragglers: cube-and-conquer on the 34 fat-tail maximal-empty
frontier masks (18 empty4 / 13 empty5 / 3 empty6; see
RESULTS-preflight-S1.md P2 — monolithic LRAT certs project to ~11.5 GB,
so each straggler is split into cubes with small per-leaf certs, the
K=3/K=2 recipe; per-leaf cert regeneration + cake_lpr streaming is the
follow-up stage, mirroring gen_cube_certs.py).

Per straggler the box CNF at its verdict tier (emptyK -> box K^3) is
built by arena2.box_solver_cnf (one-hot orientation vars), then extended
with 5 auxiliary phase bits per cell (bit k of the orientation index,
24*5 binary definitional clauses per cell) so that cube splits are truly
binary — splitting on one-hot vars directly gives a lopsided tree. The
extension is sat-equivalent (the base model determines the aux bits via
the at-least-one-orientation clause), so UNSAT of every cube implies
UNSAT of the base box CNF.

Split order: phase bits cell by cell, cells in lexicographic order.
Each cube solved with a conflict budget; budget-outs split one var
deeper (cube_k2 discipline). Checkpointed to cube_strag34_done.jsonl
(skip done on restart). A SAT cube is an ALARM (contradicts the
classify3d_all verdict — would mean a real bug).

Run:  ./runpy.sh cube_strag34.py [workers=20] [only=i1,i2,...]
"""
import json
import multiprocessing as mp
import os
import sys
import time

WORKERS = int(sys.argv[1]) if len(sys.argv) > 1 else 20
ONLY = None
if len(sys.argv) > 2 and sys.argv[2].startswith("only="):
    ONLY = set(int(x) for x in sys.argv[2][5:].split(","))

CKPT = "cube_strag34_done.jsonl"
CONF_BUDGET = 200_000

TIER_BOX = {"empty4": 4, "empty5": 5, "empty6": 6}

_S = {}


def straggler_data():
    """[(ci, verdict, held, dims)] for the 34 stragglers."""
    canonical = json.load(open("anyk3d_canonical.json"))["canonical"]
    census = json.load(open("faceeq3d_census.json"))
    t2e = {}
    for key, ei in census["triple_to_eq"].items():
        ax, o1, o2 = map(int, key.split(","))
        t2e[(ax, o1, o2)] = ei
    out = []
    for rec in json.load(open("frontier_tiers.json")):
        v = rec["verdict"]
        if v not in TIER_BOX:
            continue
        ci = rec["i"]
        if ONLY is not None and ci not in ONLY:
            continue
        held = set(canonical[ci])
        if sum(1 << e for e in held) != int(rec["mask"]):
            raise SystemExit(f"mask mismatch at canonical {ci}")
        bad = [[], [], []]
        for ax in range(3):
            for o1 in range(24):
                for o2 in range(24):
                    if t2e[(ax, o1, o2)] not in held:
                        bad[ax].append((o1, o2))
        t = TIER_BOX[v]
        out.append((ci, v, bad, (t, t, t)))
    return out


def build_cnf(bad, dims):
    """One-hot box CNF + 5 phase-bit aux vars per cell.

    Returns (clauses, ncells, nbase, nvars)."""
    import arena2
    cnf, cells, idx, var = arena2.box_solver_cnf(dims, bad)
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


def conquer(ci, verdict, cnf, ncells, nbase, done, out):
    """Run C&C on one straggler. Returns (n_unsat, n_split, sat_hit)."""
    order = [nbase + ci * 5 + k + 1
             for ci in range(ncells) for k in range(5)]
    frontier = [cube for cube in [()] if (ci, cube) not in done]
    n_unsat, n_split = 0, 0
    t0 = time.time()
    with mp.Pool(WORKERS, initializer=init_worker, initargs=(cnf,)) as pool:
        while frontier:
            batch, frontier = frontier, []
            for cube, res, model in pool.imap_unordered(
                    solve_cube, batch, chunksize=1):
                if res == "UNSAT":
                    n_unsat += 1
                    out.write(json.dumps({"i": ci, "cube": cube,
                                          "verdict": "UNSAT"}) + "\n")
                elif res == "SAT":
                    out.write(json.dumps({"i": ci, "cube": cube,
                                          "verdict": "SAT"}) + "\n")
                    out.flush()
                    print(f"*** ALARM: SAT cube in {ci} ({verdict}) "
                          f"cube={cube} — contradicts classify verdict!",
                          flush=True)
                    return n_unsat, n_split, True
                else:
                    d = len(cube)
                    if d >= len(order):
                        out.write(json.dumps(
                            {"i": ci, "cube": cube,
                             "verdict": "budget-full"}) + "\n")
                        out.flush()
                        print(f"!!! budget-out at full depth in {ci}: "
                              f"{cube}", flush=True)
                        continue
                    n_split += 1
                    for sgn in (1, -1):
                        child = cube + (sgn * order[d],)
                        if (ci, child) not in done:
                            frontier.append(child)
                out.flush()
            print(f"  [{ci} {verdict}] unsat={n_unsat} splits={n_split} "
                  f"[{time.time() - t0:.0f}s]", flush=True)
    return n_unsat, n_split, False


def main():
    strags = straggler_data()
    print(f"stragglers: {len(strags)} "
          f"(budget {CONF_BUDGET}, workers {WORKERS})", flush=True)
    done = set()
    if os.path.exists(CKPT):
        with open(CKPT) as f:
            for line in f:
                try:
                    r = json.loads(line)
                    done.add((r["i"], tuple(r["cube"])))
                except Exception:
                    pass
        print(f"checkpoint: {len(done)} cubes done", flush=True)
    t0 = time.time()
    with open(CKPT, "a") as out:
        for ci, verdict, bad, dims in strags:
            cnf, ncells, nbase, nvars = build_cnf(bad, dims)
            print(f"[{ci} {verdict}] box {dims}: {nvars} vars, "
                  f"{len(cnf)} clauses", flush=True)
            n_unsat, n_split, sat = conquer(ci, verdict, cnf, ncells,
                                            nbase, done, out)
            print(f"[{ci} {verdict}] DONE unsat={n_unsat} "
                  f"splits={n_split} [{time.time() - t0:.0f}s total]",
                  flush=True)
            if sat:
                print("RESULT: SAT ALARM — stop and investigate", flush=True)
                return
    print(f"RESULT: all stragglers CLOSED [{time.time() - t0:.0f}s]",
          flush=True)


if __name__ == "__main__":
    main()
