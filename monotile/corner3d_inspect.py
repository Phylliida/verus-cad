"""Inspect the two SUSPICIOUS exact1 decorations from the Phase-0 probe.

Run:  ./runpy.sh corner3d_inspect.py
"""
import sys

sys.argv = ["corner3d.py"]  # keep corner3d's argv parsing benign
import corner3d as C

decs = C.census(2)
for i in (1, 2, 3, 4):
    d = decs[i]
    marks = [C.CORNERS[p] for p in range(8) if d[p] == 1]
    print(f"decoration {i}: {d}")
    print(f"  {len(marks)} marked corners at {marks}")
    # adjacency structure of the marked set on the cube graph
    adj = 0
    for a in range(len(marks)):
        for b in range(a + 1, len(marks)):
            if sum(x != y for x, y in zip(marks[a], marks[b])) == 1:
                adj += 1
    print(f"  cube-edge adjacencies among marks: {adj}")
