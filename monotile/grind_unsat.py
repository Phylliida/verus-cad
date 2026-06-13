"""Overnight frontier grind: resolve the 33-pattern wall.

Absorbs the saved pattern library lazily (cheap cached kills, warm
solver), then loops UNBOUNDED synthesizer solves:
  SAT   -> a decoration avoiding every known periodic pattern of this
           arena: verify it immediately, block it, log it, keep going.
  UNSAT -> closure theorem. With Lemma A (every space-tiler is balanced
           and tiles 4^3): every K=3 binary-face cube that tiles space
           realizes one of the blocked periodic patterns, i.e. admits a
           fully periodic tiling. No strongly aperiodic K=3 binary
           Wang cube exists. Arena 2 closed.

Run detached:  setsid nohup python3 -u grind_unsat.py >> grind.log &
Progress and results: grind.log + grind_results.jsonl +
arena2_patterns.json (shared persistence, saved after every event).
"""
import json
import time

from arena2 import (Synth, Verifier, PATTERN_FILE, PERM, deep_check,
                    pattern_pairs_lattice, save_blocks)


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

print(f"[{stamp()}] building synth (balance on), library: "
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
        print(f"[{stamp()}] UNSAT during absorption?!", flush=True)
        break
    hit = next((S for S in library
                if all(dec[a] != dec[b] for a, b in S)), None)
    if hit is None:
        break                                 # fresh already?! handle below
    syn.block_pattern(hit, seen)
    cached += 1
print(f"[{stamp()}] absorbed {cached} cached kills in "
      f"{time.time()-t0:.0f}s -- starting unbounded grind", flush=True)

logf = open("grind_results.jsonl", "a")
event = 0
while True:
    event += 1
    t0 = time.time()
    r = syn.solver.solve()                    # UNBOUNDED
    dt = time.time() - t0
    if r is None:                             # defensive: a leaked budget
        print(f"[{stamp()}] ANOMALY: unbounded solve returned None; "
              f"retrying", flush=True)
        continue
    if r is False:
        print(f"[{stamp()}] " + "=" * 60, flush=True)
        print(f"[{stamp()}] SYNTHESIZER UNSAT after {dt/3600:.2f}h:", flush=True)
        print(f"[{stamp()}] every balanced K=3 binary cube tiling a 4^3 box", flush=True)
        print(f"[{stamp()}] realizes a blocked periodic pattern. With Lemma A:", flush=True)
        print(f"[{stamp()}] NO STRONGLY APERIODIC K=3 BINARY WANG CUBE EXISTS.", flush=True)
        print(f"[{stamp()}] ARENA 2 CLOSED.", flush=True)
        print(f"[{stamp()}] " + "=" * 60, flush=True)
        logf.write(json.dumps({"event": "UNSAT", "solve_s": dt}) + "\n")
        logf.flush()
        save_blocks(patterns, points)
        break
    model = syn.solver.get_model()
    pos = set(v for v in model if v > 0)
    dec = tuple(1 if (i + 1) in pos else -1 for i in range(54))
    print(f"[{stamp()}] frontier SAT #{event} after {dt:.0f}s: {dec}",
          flush=True)
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
        print(f"[{stamp()}]   verdict: {verdict}, index {idx} "
              f"(a NEW pattern family beyond the 33)", flush=True)
        S = pattern_pairs_lattice(B, qgrid)
        if syn.block_pattern(S, seen):
            patterns.append(S)
    else:
        rec["info"] = info
        print(f"[{stamp()}]   verdict: {verdict} *** "
              f"{'DEEP SURVIVOR -- check immediately!' if verdict == 'DEEP-SURVIVOR' else info} ***",
              flush=True)
        syn.block_point(dec)
        points.append(dec)
    logf.write(json.dumps(rec) + "\n")
    logf.flush()
    save_blocks(patterns, points)
