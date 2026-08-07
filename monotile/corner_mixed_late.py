"""Inspect the periodic-late mixed decorations + summarize torus sizes.

Run:  ./runpy.sh corner_mixed_late.py
"""
import json
import sys
from collections import Counter

sys.argv = ["corner3d.py"]
import corner3d as C3  # noqa: F401  (geometry shared via corner_mixed3d)
import corner_mixed3d as M

decs = M.census()
recs = [json.loads(l) for l in open(M.CKPT)]
print("verdicts so far:", Counter(r["verdict"] for r in recs))
dims = Counter(tuple(r["d"]) for r in recs if "periodic" in r["verdict"])
print("torus sizes:", dict(sorted(dims.items(), key=lambda kv: -kv[1])))

for r in recs:
    if r["verdict"] == "periodic-late":
        dec = decs[r["i"]]
        faces = [M.FACES[f] for f in range(6) if dec[f] == 1]
        corners = [M.CORNERS[p] for p in range(8) if dec[6 + p] == 1]
        print(f"decoration {r['i']}: torus {r['d']}")
        print(f"  marked faces ({len(faces)}): {faces}")
        print(f"  marked corners ({len(corners)}): {corners}")
