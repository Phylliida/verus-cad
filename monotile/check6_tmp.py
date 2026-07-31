import os
os.environ["ARENA_K"] = "4"
import json
import time
import numpy as np
import arena2

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
t0 = time.time()
sb, grid = arena2.box_sat((6, 6, 6), bad, conf_budget=200_000_000)
print(f"box 6^3: {'SAT' if sb else ('UNSAT' if sb is False else 'budget-out')} "
      f"[{time.time() - t0:.0f}s]", flush=True)
if sb:
    json.dump({str(k): v for k, v in grid.items()}, open("/tmp/755_6box.json", "w"))
    print("wrote /tmp/755_6box.json")
