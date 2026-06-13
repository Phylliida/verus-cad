"""Third competitor: symmetry-broken cube-and-conquer on the frontier.

Two levers the sequential grinders lack:

1. LEX-LEADER SYMMETRY BREAKING. The frontier instance is invariant
   under the 48-element group (24 rotations x global flip) acting on
   the 54 H-bits: balance is symmetric, box-tileability transports
   along rotations, the flip preserves compat tables exactly, and the
   pattern-block set is conjugation-closed (block_pattern conjugates
   x24; XOR blocks are flip-invariant). So we may soundly restrict to
   lex-minimal orbit representatives: for each non-identity group
   element s, add H <=_lex s(H). Preserves SAT and UNSAT.

2. CUBE-AND-CONQUER. Split on the 6 center bits (their own channel by
   the Structure Lemma) + 4 corner bits -> 1024 cubes, solved in
   parallel by a pool of Cadical 1.9.5 workers (one persistent
   incremental solver per worker; cubes are assumption lists).
   Conflict-budget rounds 3M -> 30M -> unbounded keep any one cube
   from starving a worker. SAT -> verify with the full arena2 verdict
   + deep gauntlet and stop. All cubes UNSAT -> closure theorem.

Usage:
    python3 cube_conquer.py --smoke     # plumbing check, small budgets
    python3 cube_conquer.py [workers]   # the real thing (default 24)
"""
import json
import random
import sys
import time
from multiprocessing import Pool

from pysat.solvers import Cadical195

import arena2
from arena2 import Synth, Verifier, PATTERN_FILE, PERM, NPTS, PTS, \
    deep_check, pattern_pairs_lattice, PERMINV


def stamp():
    return time.strftime("%H:%M:%S")


# ------------------------------------------------ build the frontier CNF

class Collector:
    def __init__(self):
        self.clauses = []

    def add_clause(self, cl):
        self.clauses.append(list(cl))


def build_cnf():
    syn = Synth()                       # balance constraints included
    syn.solver.delete()
    col = Collector()
    syn.solver = col                    # evar defs + blocks now collected
    with open(PATTERN_FILE) as f:
        data = json.load(f)
    patterns = [frozenset((min(a, b), max(a, b)) for a, b in plist)
                for plist in data.get("patterns", [])]
    points = [tuple(d) for d in data.get("points", [])]
    seen = set()
    for S in patterns:
        syn.block_pattern(S, seen)
    for d in points:
        syn.block_point(d)
    # Synth pins H_0=True as its own flip-breaking convention; our lex
    # chains break the flip the other way (lex-min prefers H_0=False).
    # Drop the pin -- the chains own ALL symmetry breaking here.
    assert syn.cnf[0] == [1]
    cnf = syn.cnf[1:] + col.clauses
    nv = syn.next_var - 1
    nv = add_lex_leaders(cnf, nv)
    return cnf, nv, len(patterns), len(seen)


def add_lex_leaders(cnf, nv):
    """H <=_lex s(H) for all 47 non-identity group elements.
    s = (rotation g, sign flip f): s(H)_j = f * H[PERMINV[g][j]]
    (same relabeling convention as Synth.block_point)."""
    n0 = len(cnf)
    for g in range(24):
        for f in (1, -1):
            if g == 0 and f == 1:
                continue
            prev = None
            for j in range(NPTS):
                la = j + 1                       # H_j
                v = PERMINV[g][j] + 1
                lb = v if f == 1 else -v          # s(H)_j
                if la == lb:
                    continue                      # always equal here
                if la == -lb:
                    # equality impossible at this position:
                    # prev -> not la, then stop the chain
                    cnf.append([-la] if prev is None else [-prev, -la])
                    break
                cnf.append([-la, lb] if prev is None
                           else [-prev, -la, lb])
                nv += 1
                q = nv
                if prev is not None:
                    cnf.append([-q, prev])
                cnf.append([-q, -la, lb])
                cnf.append([-q, la, -lb])
                prev = q
    print(f"[{stamp()}] lex-leader: {len(cnf)-n0} clauses for 47 "
          f"symmetries", flush=True)
    return nv


def split_vars():
    """Initial split: 6 center bits + 4 corner bits. Extension pool for
    recursive splitting: remaining corners, then edge-midpoints."""
    centers, corners, edges = [], [], []
    for i, p in enumerate(PTS):
        ax = max(range(3), key=lambda k: abs(p[k]))
        tang = sorted(abs(p[k]) for k in range(3) if k != ax)
        if tuple(tang) == (0, 0):
            centers.append(i)
        elif tuple(tang) == (2, 2):
            corners.append(i)
        else:
            edges.append(i)
    return centers + corners[:4], corners[4:] + edges


# ------------------------------------------------------- worker pool

CNF = None
SOLVER = None


def init_worker(cnf):
    global SOLVER
    SOLVER = Cadical195(bootstrap_with=cnf)


def solve_cube(task):
    idx, cube, budget = task
    if budget is None:
        r = SOLVER.solve(assumptions=cube)
    else:
        SOLVER.conf_budget(budget)
        r = SOLVER.solve_limited(assumptions=cube)
    if r is True:
        model = SOLVER.get_model()
        pos = set(v for v in model if v > 0)
        dec = tuple(1 if (i + 1) in pos else -1 for i in range(NPTS))
        return (idx, "SAT", dec)
    if r is False:
        return (idx, "UNSAT", None)
    return (idx, "UNK", None)


def handle_sat(dec, logf):
    print(f"[{stamp()}] frontier SAT (cube): {dec}", flush=True)
    V = Verifier(dec)
    verdict, info, qgrid = V.verdict()
    if verdict == "survivor":
        verdict, info, qgrid = deep_check(V.bad, V.selfbad)
    V.close()
    rec = {"event": "SAT", "verdict": verdict, "dec": list(dec)}
    if verdict in ("periodic", "periodic-deep"):
        B = info
        idx = B[0][0] * B[1][1] * B[2][2]
        rec["lattice"] = [list(r_) for r_ in B]
        rec["index"] = idx
        print(f"[{stamp()}]   verdict: {verdict}, index {idx} -- a NEW "
              f"pattern family; add it and re-run", flush=True)
    else:
        rec["info"] = info
        word = ("DEEP SURVIVOR -- check immediately!"
                if verdict == "DEEP-SURVIVOR" else info)
        print(f"[{stamp()}]   verdict: {verdict} *** {word} ***",
              flush=True)
    logf.write(json.dumps(rec) + "\n")
    logf.flush()


BUDGETS = [200_000, 600_000, 2_000_000, 6_000_000, 20_000_000, None]

def main():
    smoke = "--smoke" in sys.argv
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    workers = int(args[0]) if args else (4 if smoke else 40)

    t0 = time.time()
    cnf, nv, npat, nconj = build_cnf()
    print(f"[{stamp()}] frontier CNF: {len(cnf)} clauses, {nv} vars, "
          f"{npat} patterns ({nconj} conjugates), build "
          f"{time.time()-t0:.0f}s", flush=True)

    base, ext = split_vars()
    wave = []
    for bits in range(1 << len(base)):
        wave.append([(v + 1) if (bits >> k) & 1 else -(v + 1)
                     for k, v in enumerate(base)])
    random.Random(7).shuffle(wave)
    if smoke:
        wave = wave[:64]
    print(f"[{stamp()}] {len(wave)} cubes on {base}, extension pool "
          f"{len(ext)} vars, {workers} workers", flush=True)

    logf = open("grind3_results.jsonl", "a")
    total_unsat = 0
    depth = 0
    with Pool(workers, initializer=init_worker, initargs=(cnf,)) as pool:
        while wave:
            budget = 30_000 if smoke else BUDGETS[min(depth,
                                                      len(BUDGETS) - 1)]
            word = "unbounded" if budget is None else f"{budget:,}"
            print(f"[{stamp()}] depth {depth}: {len(wave)} cubes, "
                  f"budget {word}", flush=True)
            tasks = [(i, c, budget) for i, c in enumerate(wave)]
            deferred = []
            n_unsat = 0
            done = 0
            t_r = time.time()
            for idx, res, dec in pool.imap_unordered(solve_cube, tasks,
                                                     chunksize=1):
                done += 1
                if res == "SAT":
                    handle_sat(dec, logf)
                    pool.terminate()
                    print(f"[{stamp()}] stopping: frontier candidate "
                          f"found (depth {depth})", flush=True)
                    return
                if res == "UNSAT":
                    n_unsat += 1
                else:
                    deferred.append(wave[idx])
                if done % 200 == 0 or done == len(tasks):
                    print(f"[{stamp()}]   depth {depth}: "
                          f"{done}/{len(tasks)} done, {n_unsat} unsat, "
                          f"{len(deferred)} deferred, "
                          f"{time.time()-t_r:.0f}s", flush=True)
            total_unsat += n_unsat
            logf.write(json.dumps({"depth": depth, "cubes": len(wave),
                                   "unsat": n_unsat,
                                   "deferred": len(deferred),
                                   "secs": round(time.time()-t_r, 1)})
                       + "\n")
            logf.flush()
            if smoke:
                print(f"[{stamp()}] smoke done: {n_unsat} unsat, "
                      f"{len(deferred)} deferred", flush=True)
                return
            if not deferred:
                break
            newvars = ext[depth * 4:depth * 4 + 4]
            if budget is not None and len(newvars) == 4:
                # split the hard region: each deferred cube x16 subcubes
                nxt = []
                for c in deferred:
                    for bits in range(16):
                        nxt.append(c + [(v + 1) if (bits >> k) & 1
                                        else -(v + 1)
                                        for k, v in enumerate(newvars)])
                if len(nxt) > 400_000:
                    print(f"[{stamp()}] wave blow-up ({len(nxt)}); "
                          f"continuing without split", flush=True)
                    nxt = deferred
                wave = nxt
            else:
                wave = deferred       # out of split vars: budgets only
            depth += 1
    if wave:
        print(f"[{stamp()}] ERROR: cubes left after final wave?!",
              flush=True)
        return
    print(f"[{stamp()}] " + "=" * 60, flush=True)
    print(f"[{stamp()}] ALL CUBES UNSAT (lex-broken, balanced):",
          flush=True)
    print(f"[{stamp()}] every balanced K=3 binary cube tiling a 4^3 box",
          flush=True)
    print(f"[{stamp()}] realizes a blocked periodic pattern. With "
          f"Lemma A:", flush=True)
    print(f"[{stamp()}] NO STRONGLY APERIODIC K=3 BINARY WANG CUBE "
          f"EXISTS.", flush=True)
    print(f"[{stamp()}] ARENA 2 CLOSED.", flush=True)
    print(f"[{stamp()}] " + "=" * 60, flush=True)
    logf.write(json.dumps({"event": "UNSAT-ALL-CUBES"}) + "\n")
    logf.flush()


if __name__ == "__main__":
    main()
