"""Canonicalize the 9.34M color profiles under the 24-rotation
conjugation action (orbits3d's eqperm — sign-free pair-set geometry,
identical for equal-color matching). Mirrors orbits3d.py's
canonicalization pass.

Run:  ./runpy.sh color_orbits.py
"""
import json
import time

EQPERM = json.load(open("anyk3d_canonical.json"))["eqperm"]

t0 = time.time()
profiles = json.load(open("color3d_profiles.json"))
canon = set()
hist = {}
for p in profiles:
    ims = {tuple(sorted(EQPERM[g][e] for e in p)) for g in range(24)}
    canon.add(min(ims))
    hist[len(ims)] = hist.get(len(ims), 0) + 1
print(f"profiles {len(profiles)} -> canonical {len(canon)} "
      f"[{time.time() - t0:.0f}s]", flush=True)
print(f"orbit-size histogram: {sorted(hist.items())}", flush=True)
json.dump({"eqperm": EQPERM, "canonical": sorted(list(p) for p in canon)},
          open("color3d_canonical.json", "w"))
print("wrote color3d_canonical.json", flush=True)
