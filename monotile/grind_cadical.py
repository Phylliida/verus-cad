"""Portfolio partner to grind_unsat.py: same frontier instance, solved
by Cadical 1.9.5 instead of Glucose3 (monkeypatched in before any
construction). First grinder to answer wins.

Writes grind2_results.jsonl only -- does NOT touch the shared
arena2_patterns.json (avoids write races with the Glucose grinder; new
patterns are recoverable from the jsonl: re-derive a qgrid for the
logged lattice via solve_lattice_torus).

Run detached:  setsid nohup python3 -u grind_cadical.py >> grind2.log &
"""
import json
import time

import arena2
from pysat.solvers import Cadical195
arena2.Glucose3 = Cadical195                  # the whole engine runs Cadical

from arena2 import (Synth, Verifier, PATTERN_FILE, PERM, deep_check,
                    pattern_pairs_lattice)


def stamp():
    return time.strftime("%H:%M:%S")


with open(PATTERN_FILE) as f:
    data = json.load(f)
patterns = [frozenset((min(a, b), max(a, b)) for a, b in plist)
            for plist in data.get("patterns", [])]
points = [tuple(d) for d in data.get("points", [])]

library = []
libseen = set()
for S in patterns:
    for g in range(24):
        pg = PERM[g]
        Sg = frozenset((min(pg[a], pg[b]), max(pg[a], pg[b]))
                       for a, b in S)
        if Sg not in libseen:
            libseen.add(Sg)
            library.append(Sg)

print(f"[{stamp()}] [cadical] building synth, library: "
      f"{len(patterns)} patterns / {len(library)} conjugates, "
      f"{len(points)} points", flush=True)
syn = Synth()
seen = set()
for d in points:
    syn.block_point(d)

t0 = time.time()
cached = 0
while True:                                   # lazy absorption
    dec = syn.propose(deadline=time.time() + 30)
    if dec == "STALL":
        break                                 # frontier reached
    if dec is None:
        print(f"[{stamp()}] [cadical] UNSAT during absorption?!",
              flush=True)
        break
    hit = next((S for S in library
                if all(dec[a] != dec[b] for a, b in S)), None)
    if hit is None:
        break
    syn.block_pattern(hit, seen)
    cached += 1
print(f"[{stamp()}] [cadical] absorbed {cached} cached kills in "
      f"{time.time()-t0:.0f}s -- starting unbounded grind", flush=True)

logf = open("grind2_results.jsonl", "a")
event = 0
while True:
    event += 1
    t0 = time.time()
    r = syn.solver.solve()                    # UNBOUNDED
    dt = time.time() - t0
    if r is None:                             # defensive: a leaked budget
        print(f"[{stamp()}] [cadical] ANOMALY: unbounded solve returned "
              f"None; retrying", flush=True)
        continue
    if r is False:
        print(f"[{stamp()}] [cadical] " + "=" * 55, flush=True)
        print(f"[{stamp()}] [cadical] SYNTHESIZER UNSAT after "
              f"{dt/3600:.2f}h:", flush=True)
        print(f"[{stamp()}] [cadical] every balanced K=3 binary cube "
              f"tiling a 4^3 box", flush=True)
        print(f"[{stamp()}] [cadical] realizes a blocked periodic "
              f"pattern. With Lemma A:", flush=True)
        print(f"[{stamp()}] [cadical] NO STRONGLY APERIODIC K=3 BINARY "
              f"WANG CUBE EXISTS.", flush=True)
        print(f"[{stamp()}] [cadical] ARENA 2 CLOSED.", flush=True)
        print(f"[{stamp()}] [cadical] " + "=" * 55, flush=True)
        logf.write(json.dumps({"event": "UNSAT", "solve_s": dt}) + "\n")
        logf.flush()
        break
    model = syn.solver.get_model()
    pos = set(v for v in model if v > 0)
    dec = tuple(1 if (i + 1) in pos else -1 for i in range(54))
    print(f"[{stamp()}] [cadical] frontier SAT #{event} after {dt:.0f}s: "
          f"{dec}", flush=True)
    V = Verifier(dec)
    verdict, info, qgrid = V.verdict()
    if verdict == "survivor":
        verdict, info, qgrid = deep_check(V.bad, V.selfbad)
    V.close()
    rec = {"event": event, "solve_s": round(dt, 1), "verdict": verdict,
           "dec": list(dec)}
    if verdict in ("periodic", "periodic-deep"):
        B = info
        idx = B[0][0] * B[1][1] * B[2][2]
        rec["lattice"] = [list(r_) for r_ in B]
        rec["index"] = idx
        print(f"[{stamp()}] [cadical]   verdict: {verdict}, index {idx} "
              f"(a NEW pattern family beyond the 33)", flush=True)
        S = pattern_pairs_lattice(B, qgrid)
        syn.block_pattern(S, seen)
    else:
        rec["info"] = info
        print(f"[{stamp()}] [cadical]   verdict: {verdict} *** "
              f"{'DEEP SURVIVOR -- check immediately!' if verdict == 'DEEP-SURVIVOR' else info} ***",
              flush=True)
        syn.block_point(dec)
    logf.write(json.dumps(rec) + "\n")
    logf.flush()
