"""Identify the empty equal-rule decorations (T=2: #10, #11) for the
RESULTS writeup.

Run:  ./runpy.sh corner3d_empties.py
"""
import sys

sys.argv = ["corner3d.py"]
import corner3d as C

decs = C.census(2)
for i in (10, 11):
    d = decs[i]
    marks = [C.CORNERS[p] for p in range(8) if d[p] == 1]
    print(f"decoration {i}: {d}")
    print(f"  {len(marks)} marks at {marks}")
