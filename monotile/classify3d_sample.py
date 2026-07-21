"""anyk-08/12: calibration pass — classify a random sample of the 1.44M
3D achievable profiles as empty / periodic / stall.

Per profile: reconstruct the 1728-triple relation via faceeq3d's census
triple map, build bad tables, then:
  1. torus sweep, lattice classes index <= 8 (cheap SAT witnesses),
  2. box 3^3 then 4^3 UNSAT (budgeted) => empty,
  3. deeper torus sweep <= 32,
  4. else STALL (einstein-suspect pile — the interesting outcome).

Also records verdict box/torus sizes for the campaign design and the
monotone-frontier statistics.

Run:  ./runpy.sh classify3d_sample.py [n_sample]
"""
import json
import random
import sys
import time

import arena2
from arena2 import box_sat, solve_lattice_torus
from skew import lattice_classes

N = int(sys.argv[1]) if len(sys.argv) > 1 else 5000

census = json.load(open("faceeq3d_census.json"))
T2E = {}
for key, ei in census["triple_to_eq"].items():
    ax, o1, o2 = map(int, key.split(","))
    T2E[(ax, o1, o2)] = ei

profiles = json.load(open("anyk3d_profiles.json"))
rng = random.Random(42)
sample = rng.sample(range(len(profiles)), N)

LAT8 = list(lattice_classes(8))
LAT32 = list(lattice_classes(32))
print(f"lattice classes: {len(LAT8)} @8, {len(LAT32)} @32", flush=True)


def bad_of(profile):
    held = set(profile)
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


counts = {"periodic8": 0, "empty3": 0, "empty4": 0, "periodic32": 0,
          "STALL": 0}
stalls = []
t0 = time.time()
out = open("classify3d_sample.jsonl", "w")
for j, pi in enumerate(sample):
    prof = profiles[pi]
    bad, selfbad = bad_of(prof)
    verdict = None
    for B in LAT8:
        ts, _ = solve_lattice_torus(B, bad, selfbad, conf_budget=20_000)
        if ts:
            verdict = ("periodic8", B[0][0] * B[1][1] * B[2][2])
            break
    if verdict is None:
        sb, _ = box_sat((3, 3, 3), bad, conf_budget=200_000)
        if sb is False:
            verdict = ("empty3", None)
    if verdict is None:
        sb, _ = box_sat((4, 4, 4), bad, conf_budget=2_000_000)
        if sb is False:
            verdict = ("empty4", None)
    if verdict is None:
        for B in LAT32:
            ts, _ = solve_lattice_torus(B, bad, selfbad, conf_budget=20_000)
            if ts:
                verdict = ("periodic32", B[0][0] * B[1][1] * B[2][2])
                break
    if verdict is None:
        verdict = ("STALL", None)
        stalls.append(pi)
        print(f"  STALL: profile {pi} (held size {len(prof)})", flush=True)
    counts[verdict[0]] += 1
    out.write(json.dumps({"profile": pi, "verdict": verdict[0],
                          "index": verdict[1]}) + "\n")
    if (j + 1) % 250 == 0:
        out.flush()
        print(f"  {j + 1}/{N} {counts} [{time.time() - t0:.0f}s]",
              flush=True)
out.close()
print(f"DONE {counts} stalls={stalls[:20]} [{time.time() - t0:.0f}s]",
      flush=True)
