"""Which ingredient makes proposal 9 hard: balance, patterns, or both?

Times one propose() under the 2x2 grid {balance} x {loaded patterns},
each with a conflict budget, fresh Synth instances.
"""
import json
import time

from arena2 import Synth, PATTERN_FILE

BUDGET = 400_000

with open(PATTERN_FILE) as f:
    data = json.load(f)
plists = data.get("patterns", [])
print(f"{len(plists)} saved patterns, {len(data.get('points', []))} points")

for balance in (False, True):
    for load in (False, True):
        t0 = time.time()
        syn = Synth(balance=balance)
        t_build = time.time() - t0
        seen = set()
        if load:
            for plist in plists:
                S = frozenset((min(a, b), max(a, b)) for a, b in plist)
                syn.block_pattern(S, seen)
        t0 = time.time()
        syn.solver.conf_budget(BUDGET)
        r = syn.solver.solve_limited()
        dt = time.time() - t0
        word = {True: "SAT", False: "UNSAT", None: f"BUDGET-OUT({BUDGET})"}[r]
        print(f"balance={balance!s:5s} patterns={load!s:5s}: {word:18s} "
              f"propose {dt:6.1f}s  (build {t_build:.1f}s)")
        syn.solver.delete()
