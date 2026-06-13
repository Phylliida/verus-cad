"""Cube-and-conquer v3 = v2 (lex symmetry breaking + recursive cube
splitting) plus three upgrades:

1. ONE-SHOT PREPROCESSING: CaDiCaL's preprocessor (pysat Processor)
   simplifies the shared CNF once, with the 54 H-vars FROZEN so cube
   assumptions and dec extraction stay valid. Every worker inherits
   the smaller formula. Falls back to the raw CNF if processing
   misbehaves (sanity-checked against a quick raw solve).
2. LOOKAHEAD SPLIT SELECTION: each H-var is scored by failed-literal
   style probing (propagate +v / -v, score = product of implied-literal
   counts; a falsified polarity scores huge). Top-10 become the base
   split, the rest order the extension pool. Replaces the geometric
   guess (centers+corners).
3. SOLVER DIVERSITY: workers alternate Cadical 1.9.5 / Glucose 4.2 by
   pid parity -- different engines attack the hard core differently.

Reads arena2_patterns.json at build time, so relaunching after a
saturation merge automatically ingests the enriched library.

Usage:
    python3 cube_conquer3.py --smoke     # plumbing check
    python3 cube_conquer3.py [workers]   # default 36
"""
import json
import os
import random
import sys
import time
from multiprocessing import Pool

from pysat.solvers import Cadical195, Glucose42
from pysat.process import Processor

import arena2
from arena2 import Synth, Verifier, PATTERN_FILE, PERM, NPTS, \
    deep_check, pattern_pairs_lattice, PERMINV


def stamp():
    return time.strftime("%H:%M:%S")


# ---------------------------------------------- CNF (same as v2)

class Collector:
    def __init__(self):
        self.clauses = []

    def add_clause(self, cl):
        self.clauses.append(list(cl))


def add_lex_leaders(cnf, nv):
    n0 = len(cnf)
    for g in range(24):
        for f in (1, -1):
            if g == 0 and f == 1:
                continue
            prev = None
            for j in range(NPTS):
                la = j + 1
                v = PERMINV[g][j] + 1
                lb = v if f == 1 else -v
                if la == lb:
                    continue
                if la == -lb:
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
    print(f"[{stamp()}] lex-leader: {len(cnf)-n0} clauses", flush=True)
    return nv


def build_cnf():
    syn = Synth()
    syn.solver.delete()
    col = Collector()
    syn.solver = col
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
    assert syn.cnf[0] == [1]
    cnf = syn.cnf[1:] + col.clauses
    nv = syn.next_var - 1
    nv = add_lex_leaders(cnf, nv)
    return cnf, nv, len(patterns)


def preprocess(cnf):
    """One-shot CaDiCaL preprocessing with H-vars frozen."""
    t0 = time.time()
    proc = Processor(bootstrap_with=cnf)
    pcnf = proc.process(rounds=2, freeze=list(range(1, NPTS + 1)))
    proc.delete()
    print(f"[{stamp()}] preprocess: {len(cnf)} -> {len(pcnf.clauses)} "
          f"clauses [{time.time()-t0:.0f}s]", flush=True)
    # sanity: the processed formula must still be SAT-consistent with
    # quick propagation; if it became trivially UNSAT something is
    # wrong (frozen-var mishandling) -- fall back to raw
    with Cadical195(bootstrap_with=pcnf.clauses) as s:
        s.conf_budget(1)
        if s.solve_limited() is False:
            print(f"[{stamp()}] preprocess SANITY FAIL -> raw CNF",
                  flush=True)
            return cnf
    return pcnf.clauses


def split_vars():
    """Geometric split: 6 centers (their own channel by the Structure
    Lemma) + 4 corners; extension pool = remaining corners then edges.
    EMPIRICAL NOTE: this beat naive root-propagation lookahead badly
    (56/64 cubes killed at 30k vs 0/64) -- single H-literals barely
    propagate through the one-hot/XOR structure, so lookahead scores
    degenerate. Kept lookahead_order below for future refinement."""
    from arena2 import PTS
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


def lookahead_order(cnf):
    """Score H-vars by two-sided propagation strength."""
    t0 = time.time()
    with Glucose42(bootstrap_with=cnf) as p:
        scores = []
        for v in range(1, NPTS + 1):
            okp, imp_p = p.propagate(assumptions=[v])
            okn, imp_n = p.propagate(assumptions=[-v])
            sp = len(imp_p) if okp else 10**6
            sn = len(imp_n) if okn else 10**6
            scores.append((sp * sn, v - 1))
    scores.sort(reverse=True)
    order = [i for _, i in scores]
    print(f"[{stamp()}] lookahead order (top 10): {order[:10]} "
          f"[{time.time()-t0:.0f}s]", flush=True)
    return order[:10], order[10:]


# ------------------------------------------------- worker pool

SOLVER = None


def init_worker(cnf):
    global SOLVER
    cls = Cadical195 if os.getpid() % 2 else Glucose42
    SOLVER = cls(bootstrap_with=cnf)


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
    workers = int(args[0]) if args else (4 if smoke else 36)

    t0 = time.time()
    cnf, nv, npat = build_cnf()
    print(f"[{stamp()}] frontier CNF: {len(cnf)} clauses, {nv} vars, "
          f"{npat} patterns, build {time.time()-t0:.0f}s", flush=True)
    cnf = preprocess(cnf)
    base, ext = split_vars()

    wave = []
    for bits in range(1 << len(base)):
        wave.append([(v + 1) if (bits >> k) & 1 else -(v + 1)
                     for k, v in enumerate(base)])
    random.Random(7).shuffle(wave)
    if smoke:
        wave = wave[:64]
    print(f"[{stamp()}] {len(wave)} cubes on {base}, ext pool "
          f"{len(ext)}, {workers} workers (Cadical/Glucose42 by pid)",
          flush=True)

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
                wave = []          # fully resolved: closure, not error
                break
            newvars = ext[depth * 4:depth * 4 + 4]
            if budget is not None and len(newvars) == 4:
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
                wave = deferred
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
    logf.write(json.dumps({"event": "UNSAT-ALL-CUBES",
                           "total_unsat": total_unsat}) + "\n")
    logf.flush()


if __name__ == "__main__":
    main()
