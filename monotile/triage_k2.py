"""anyk-01: triage the parked K=2 suspicious decorations through deep_check.

The 2026-07-06 K=2 runs (arena2_progress_K2.jsonl, two runs; the final
arena2_log_K2.json is stale w.r.t. the second run) parked:
  - 4 distinct "suspicious" decorations (in-loop budget-outs, never deep-checked)
  - 4 "untileable8" decorations (already sound kills: true UNSAT at the 8^3
    free-boundary box, which any space-tiler would have to satisfy)

This script:
  0. validates the K=2 deep_check plumbing on a freshly-found periodic kill
  1. runs the deep_check gauntlet on the 4 suspicious decorations
  2. audit spot-checks one untileable8 by re-running the 8^3 box solve

Run:  ARENA_K=2 ./runpy.sh triage_k2.py
Results append to triage_k2_results.jsonl.
"""
import json
import os
import random
import time

assert os.environ.get("ARENA_K") == "2", "run with ARENA_K=2"

import arena2
from arena2 import (Verifier, deep_check, box_sat, pattern_pairs_lattice,
                    NPTS)

assert NPTS == 24, NPTS

SUSPICIOUS = [
    # it58 (run A) -- the one in arena2_log_K2.json, 11 unresolved vectors + box5
    [1, 1, -1, -1, -1, -1, 1, 1, -1, -1, 1, 1, -1, 1, -1, 1, 1, -1, 1, -1, 1, 1, -1, -1],
    # it57 (run B)
    [1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, -1, 1, -1, -1, 1, -1, 1, -1, 1, -1, 1],
    # it61 (run B)
    [1, -1, 1, -1, -1, -1, 1, 1, -1, -1, 1, 1, 1, 1, -1, -1, 1, -1, 1, -1, -1, -1, 1, 1],
    # it77 (run B)
    [1, -1, 1, -1, -1, -1, 1, 1, -1, -1, 1, 1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1],
]

UNTILEABLE8_SPOTCHECK = [
    # it60 (run B) -- re-verify the 8^3 UNSAT is reproducible
    [1, -1, -1, 1, -1, -1, 1, 1, -1, -1, 1, 1, 1, -1, 1, -1, 1, -1, -1, 1, -1, -1, 1, 1],
]

out = open("triage_k2_results.jsonl", "a")


def emit(rec):
    rec["t"] = round(time.time() - T0, 1)
    line = json.dumps(rec)
    print(line, flush=True)
    out.write(line + "\n")
    out.flush()


T0 = time.time()

# ---- 0. pipeline validation: deep_check must confirm a known-periodic kill
rng = random.Random(0)
val = None
for tries in range(200):
    dec = tuple(rng.choice((1, -1)) for _ in range(NPTS))
    V = Verifier(dec)
    verdict, info, qgrid = V.verdict()
    if verdict == "periodic":
        t1 = time.time()
        dv, dB, dqg = deep_check(V.bad, V.selfbad)
        val = {"stage": "validation", "tries": tries, "in_loop": "periodic",
               "in_loop_index": info[0][0] * info[1][1] * info[2][2],
               "deep": dv, "deep_secs": round(time.time() - t1, 1)}
        V.close()
        break
    V.close()
emit(val if val else {"stage": "validation", "error": "no periodic sample found"})
assert val and val["deep"] == "periodic-deep", \
    f"K=2 deep_check validation failed: {val} -- verdicts not trustworthy, aborting"

# ---- 1. the gauntlet on the 4 parked suspicious decorations
for i, dec in enumerate(SUSPICIOUS):
    dec = tuple(dec)
    V = Verifier(dec)
    t1 = time.time()
    dv, dB, dqg = deep_check(V.bad, V.selfbad)
    rec = {"stage": "suspicious", "i": i, "dec": list(dec), "deep": dv,
           "secs": round(time.time() - t1, 1)}
    if dv == "periodic-deep":
        rec["lattice"] = [list(r) for r in dB]
        rec["index"] = dB[0][0] * dB[1][1] * dB[2][2]
        rec["pattern_pairs"] = sorted(map(list, pattern_pairs_lattice(dB, dqg)))
    emit(rec)
    V.close()

# ---- 2. audit spot-check: reproduce one untileable8 refutation
for dec in UNTILEABLE8_SPOTCHECK:
    t1 = time.time()
    s8, _ = box_sat((8, 8, 8), Verifier(tuple(dec)).bad, conf_budget=2_000_000)
    emit({"stage": "untileable8-audit", "dec": dec,
          "box8": {True: "SAT?!", False: "unsat-confirmed", None: "budget-out"}[s8],
          "secs": round(time.time() - t1, 1)})

emit({"stage": "done"})
