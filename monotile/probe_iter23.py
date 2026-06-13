"""Verbose dissection of the iter-23 suspicious candidate: replicate the
in-loop verdict flow and print everything it sees at each step."""
import itertools
import json
import sys

import arena2
from arena2 import (CANON3, Verifier, extract_grid, held_vectors,
                    implied_lattices, solve_lattice_torus, orbit_size)

DEC = (1, -1, 1, 1, -1, -1, -1, 1, -1, 1, -1, -1, -1, 1, 1, 1, 1, -1,
       -1, 1, 1, 1, 1, -1, -1, -1, 1, 1, -1, 1, 1, -1, -1, -1, 1, -1,
       1, 1, -1, -1, 1, 1, 1, -1, -1, -1, 1, -1, 1, -1, -1, 1, -1, 1)

SUS = [(0, 0, 2), (0, 1, 1), (0, 1, 3), (0, 2, 2), (0, 3, 3)]

def lat_index(B):
    return B[0][0] * B[1][1] * B[2][2]

V = Verifier(DEC)
print("orbit size", orbit_size(V.placed))
V.det6 = V._detector((6, 6, 6))
s6, cells, idx, var, sels = V.det6

for v in SUS:
    s6.conf_budget(25_000)
    r = s6.solve_limited(assumptions=[sels[v]])
    print(f"\nv={v}: sel6 -> {r}")
    if r is not True:
        continue
    grid = extract_grid(s6.get_model(), cells, idx, var)
    held = held_vectors(grid, maxc=5, min_pairs=6)
    lats = implied_lattices(held, max_index=512, max_held=64)
    comps = arena2.rank2_completions(held)
    print(f"  held {len(held)}, implied {len(lats)}, "
          f"rank2 completions {len(comps)} "
          f"(indices {[lat_index(B) for B in comps[:12]]})")
    B, qgrid = V.confirm_period(grid, maxc=5, min_pairs=6)
    if B is None:
        print("  confirm_period: STILL UNCONFIRMED")
    else:
        print(f"  confirm_period: PERIODIC {B} index {lat_index(B)}")
        break
V.close()
