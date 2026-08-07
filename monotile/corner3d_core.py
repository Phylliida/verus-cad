"""Hunt the 3D chirality obstruction: smallest UNSAT torus for the
chiral corner decorations #10/#11 (T=2), then inspect.

Run:  ./runpy.sh corner3d_core.py
"""
import itertools
import sys

sys.argv = ["corner3d.py"]
import corner3d as C

decs = C.census(2)
for idx in (10, 11):
    dec = decs[idx]
    show = C.show_table(dec)
    print(f"decoration #{idx}: {dec}")
    marks = [C.CORNERS[p] for p in range(8) if dec[p] == 1]
    print(f"  marks at {marks}")
    dims = sorted(itertools.product(range(1, 4), repeat=3),
                  key=lambda d: (d[0] * d[1] * d[2], d))
    for d in dims:
        ok, _ = C.corner_sat(show, d, "equal", True, 200_000)
        status = "SAT" if ok else "UNSAT" if ok is False else "?"
        print(f"  torus {d}: {status}", flush=True)
