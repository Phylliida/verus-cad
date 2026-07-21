"""Deep probe for stalled 3D profiles (einstein suspects).

Per profile: torus sweep to index 64 (200k conflicts per class), then
big-budget boxes 4^3 / 5^3 / 6^3 (20M conflicts). Reports each stage
precisely — budget-outs are named, never conflated with refutations.

Run:  ./runpy.sh stallprobe3d.py <raw|canon> <index> [index...]
      (raw = index into anyk3d_profiles.json, canon = anyk3d_canonical.json)
"""
import json
import sys
import time

import arena2
from arena2 import box_sat, solve_lattice_torus
from skew import lattice_classes

mode = sys.argv[1]
indices = [int(x) for x in sys.argv[2:]]
if mode == "raw":
    profiles = json.load(open("anyk3d_profiles.json"))
else:
    profiles = json.load(open("anyk3d_canonical.json"))["canonical"]

census = json.load(open("faceeq3d_census.json"))
T2E = {}
for key, ei in census["triple_to_eq"].items():
    ax, o1, o2 = map(int, key.split(","))
    T2E[(ax, o1, o2)] = ei


def bad_of(prof):
    held = set(prof)
    bad = [[], [], []]
    selfbad = [[], [], []]
    for ax in range(3):
        for o1 in range(24):
            for o2 in range(24):
                if T2E[(ax, o1, o2)] not in held:
                    bad[ax].append((o1, o2))
                    if o1 == o2:
                        selfbad[ax].append(o1)
    return bad, selfbad


LAT64 = list(lattice_classes(64))
print(f"lattice classes <=64: {len(LAT64)}", flush=True)

for pi in indices:
    prof = profiles[pi]
    print(f"\n=== {mode} profile {pi} (held {len(prof)}: {prof}) ===",
          flush=True)
    bad, selfbad = bad_of(prof)
    t0 = time.time()
    found = None
    timeouts = 0
    for B in LAT64:
        ts = solve_lattice_torus(B, bad, selfbad, conf_budget=200_000)[0]
        if ts:
            found = B
            break
        if ts is None:
            timeouts += 1
    if found:
        print(f"  PERIODIC: lattice {found} index "
              f"{found[0][0] * found[1][1] * found[2][2]} "
              f"[{time.time() - t0:.0f}s]", flush=True)
        continue
    print(f"  no torus <=64 ({timeouts} budget-outs) "
          f"[{time.time() - t0:.0f}s]", flush=True)
    for dims in ((4, 4, 4), (5, 5, 5), (6, 6, 6)):
        t1 = time.time()
        sb, _ = box_sat(dims, bad, conf_budget=20_000_000)
        tag = {False: "UNSAT -> EMPTY", True: "SAT (tiles it)",
               None: "budget-out"}[sb]
        print(f"  box {dims}: {tag} [{time.time() - t1:.0f}s]", flush=True)
        if sb is False:
            break
        if sb is None:
            break
    print(f"  verdict: {'EMPTY' if sb is False else 'DEEP-SUSPECT'}",
          flush=True)
