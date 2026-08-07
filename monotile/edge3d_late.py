"""Analyze the edge3d T=2 verdicts: rule split, periodic-late tori,
and the exact1 m=3 campaign.

Run:  ./runpy.sh edge3d_late.py
"""
import json
import sys
from collections import Counter

sys.argv = ["corner3d.py"]
import corner3d as C3  # noqa: F401
import edge3d as E

recs = [json.loads(l) for l in open(E.CKPT)]
for rule in ("equal", "exact1"):
    rs = [r for r in recs if r["rule"] == rule]
    print(rule, Counter(r["verdict"] for r in rs))

print("\nperiodic torus sizes (equal):")
dims = Counter(tuple(r["d"]) for r in recs
               if r["rule"] == "equal" and "periodic" in r["verdict"])
for d, n in sorted(dims.items(), key=lambda kv: -kv[1]):
    print(f"  {d}: {n}")

decs = E.census(2)
print("\nperiodic-late decorations (equal):")
for r in sorted((r for r in recs if r["verdict"] == "periodic-late"),
                key=lambda r: r["i"]):
    dec = decs[r["i"]]
    marks = [E.EDGES[p] for p in range(12) if dec[p] == 1]
    print(f"  #{r['i']}: torus {r['d']}, {len(marks)} marks {marks}")

print("\nexact1 (m=3) verdicts:")
for r in sorted((r for r in recs if r["rule"] == "exact1"),
                key=lambda r: r["i"]):
    dec = E.census(2, marks=3)[r["i"]]
    marks = [E.EDGES[p] for p in range(12) if dec[p] == 1]
    per_axis = Counter(m[0] for m in marks)
    print(f"  #{r['i']}: {r['verdict']:15s} d={r.get('d')} "
          f"per-axis={dict(per_axis)}")
