"""anyk-01 escalation pass: re-judge the ext-timeout K=2 decorations with
~100x budgets.

Reads triage_k2_results.jsonl, picks every suspicious-stage dec whose deep
verdict was a timeout flavor (ext-timeout / box8-timeout / suspicious-ext),
and re-runs:
  1. the full in-loop Verifier.verdict() with escalated SEL/BOX/TORUS budgets
     (reuses the designed 19-vector + det6 + box5 pipeline, just slower)
  2. if still "survivor": an escalated deep_check -- lattice sweep to
     index 64 with 200k-conflict torus solves, EXTRA4 6^3 solves at 3M
     conflicts, 8^3 box at 20M conflicts.

Budget-outs remain "unresolved", never refutations (engine rule).

Run:  ARENA_K=2 ./runpy.sh triage_k2_escalate.py
Results append to triage_k2_escalate.jsonl.
"""
import json
import os
import time

assert os.environ.get("ARENA_K") == "2", "run with ARENA_K=2"

import arena2

# escalate the in-loop budgets ~100x (module globals, read at call time)
arena2.SEL4_CONF = 1_000_000
arena2.SEL6_CONF = 2_000_000
arena2.BOX5_CONF = 5_000_000
arena2.TORUS_CONF = 200_000
arena2.VERDICT_TIME_CAP = 7200.0

from arena2 import (Verifier, lattice_sweep, box_sat, held_vectors,
                    implied_lattices, rank2_completions, solve_lattice_torus,
                    pattern_pairs_lattice, EXTRA4, NPTS)

assert NPTS == 24

TIMEOUTY = {"ext-timeout", "box8-timeout", "suspicious-ext", "suspicious"}

targets = []
seen = set()
with open("triage_k2_results.jsonl") as f:
    for line in f:
        r = json.loads(line)
        if r.get("stage") == "suspicious" and r.get("deep") in TIMEOUTY:
            d = tuple(r["dec"])
            if d not in seen:
                seen.add(d)
                targets.append(d)
print(f"escalation targets: {len(targets)}", flush=True)

out = open("triage_k2_escalate.jsonl", "a")
T0 = time.time()


def emit(rec):
    rec["t"] = round(time.time() - T0, 1)
    line = json.dumps(rec)
    print(line, flush=True)
    out.write(line + "\n")
    out.flush()


def deep_check_hard(V):
    B, qg = lattice_sweep(V.bad, V.selfbad, max_index=64)
    if B is not None:
        return ("periodic-deep", B, qg)
    saw_timeout = False
    for v in EXTRA4:
        sv, gv = box_sat((6, 6, 6), V.bad, identify=v, conf_budget=3_000_000)
        if sv is None:
            saw_timeout = True
            continue                      # keep scanning other vectors
        if sv:
            held = held_vectors(gv, 4, 12)
            for B in implied_lattices(held, max_index=96)[:24]:
                ts, qg = solve_lattice_torus(B, V.bad, V.selfbad,
                                             conf_budget=200_000)
                if ts:
                    return ("periodic-deep", B, qg)
            for B in rank2_completions(held)[:24]:
                ts, qg = solve_lattice_torus(B, V.bad, V.selfbad,
                                             conf_budget=200_000)
                if ts:
                    return ("periodic-deep", B, qg)
            return ("suspicious-ext-hard", None, None)
    s8, _ = box_sat((8, 8, 8), V.bad, conf_budget=20_000_000)
    if s8 is False:
        return ("untileable8", None, None)
    if s8 is None or saw_timeout:
        return ("hard-timeout", None, None)
    return ("DEEP-SURVIVOR", None, None)


for i, dec in enumerate(targets):
    V = Verifier(dec)
    t1 = time.time()
    verdict, info, qgrid = V.verdict()
    rec = {"stage": "escalated-verdict", "i": i, "dec": list(dec),
           "verdict": verdict, "secs": round(time.time() - t1, 1)}
    if verdict == "periodic":
        rec["index"] = info[0][0] * info[1][1] * info[2][2]
        rec["lattice"] = [list(r) for r in info]
        rec["pattern_pairs"] = sorted(map(list,
                                          pattern_pairs_lattice(info, qgrid)))
    elif verdict == "suspicious":
        rec["info"] = {k: [list(x) if isinstance(x, tuple) else x
                           for x in v] if isinstance(v, list) else v
                       for k, v in info.items()}
    emit(rec)
    if verdict in ("survivor", "suspicious"):
        t1 = time.time()
        dv, dB, dqg = deep_check_hard(V)
        rec = {"stage": "escalated-deep", "i": i, "dec": list(dec),
               "deep": dv, "secs": round(time.time() - t1, 1)}
        if dv == "periodic-deep":
            rec["index"] = dB[0][0] * dB[1][1] * dB[2][2]
            rec["lattice"] = [list(r) for r in dB]
            rec["pattern_pairs"] = sorted(map(list,
                                              pattern_pairs_lattice(dB, dqg)))
        emit(rec)
    V.close()

emit({"stage": "done"})
