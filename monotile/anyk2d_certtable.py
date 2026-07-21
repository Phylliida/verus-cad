"""Build the 1024-entry certificate table for the 2D any-K Lean port.

For every held-equation subset (2^10), the induced relation mask gets:
  - 'empty6'  : no 6x6 free-boundary box tiling (true UNSAT), or
  - 'rect'    : an explicit rectangular torus tiling (a, d, grid),
                found via SAT on rectangular quotient tori (fast), or
  - 'PROBLEM' : neither (would break the superset approach; expect none).

Rect certs are preferred over skew for Lean simplicity (periods (a,0),(0,d),
component-wise mod, no reduce_vec). Grid stored row-major: grid[x*d + y].

Run:  ARENA2D_K=4 ./runpy.sh anyk2d_certtable.py   (K irrelevant, masks only)
"""
import json

from faceeq2d import EQ_IDX, EQ_OF, TRIPLES, eq_norm
from relations2d import mask_to_bad
from arena2d import box_sat, solve_lattice_torus, NORI
from pysat.solvers import Glucose3


def mask_of_held(held):
    m = 0
    for tr in TRIPLES:
        if EQ_IDX[eq_norm(EQ_OF[tr])] in held:
            ax, o1, o2 = tr
            m |= 1 << (ax * 16 + o1 * 4 + o2)
    return m


def rect_cert_sat(m, amax=6, dmax=6):
    """Find a rectangular torus tiling by SAT; returns (a, d, grid)."""
    bad, selfbad = mask_to_bad(m)
    for area in range(1, amax * dmax + 1):
        for a in range(1, amax + 1):
            if area % a or area // a > dmax:
                continue
            d = area // a
            cells = [(x, y) for x in range(a) for y in range(d)]
            idx = {c: i for i, c in enumerate(cells)}

            def var(ci, o):
                return ci * NORI + o + 1

            cnf = []
            for c in cells:
                ci = idx[c]
                cnf.append([var(ci, o) for o in range(NORI)])
                for o1 in range(NORI):
                    for o2 in range(o1 + 1, NORI):
                        cnf.append([-var(ci, o1), -var(ci, o2)])
                for ax in range(2):
                    nc = ((c[0] + (ax == 0)) % a, (c[1] + (ax == 1)) % d)
                    nci = idx[nc]
                    if nci == ci:
                        cnf.extend([-var(ci, o)] for o in selfbad[ax])
                    else:
                        cnf.extend([-var(ci, o1), -var(nci, o2)]
                                   for o1, o2 in bad[ax])
            with Glucose3(bootstrap_with=cnf) as s:
                if s.solve():
                    pos = set(x for x in s.get_model() if x > 0)
                    grid = [next(o for o in range(NORI)
                                 if var(idx[(x, y)], o) in pos)
                            for x in range(a) for y in range(d)]
                    return a, d, grid
    return None


results = {}
counts = {"empty6": 0, "rect": 0, "PROBLEM": 0}
for bits in range(1024):
    held = frozenset(i for i in range(10) if (bits >> i) & 1)
    m = mask_of_held(held)
    bad, _ = mask_to_bad(m)
    sb, _ = box_sat((6, 6), bad, conf_budget=500_000)
    if sb is False:
        results[bits] = {"mask": m, "cert": "empty6"}
        counts["empty6"] += 1
        continue
    rc = rect_cert_sat(m)
    if rc is not None:
        a, d, grid = rc
        results[bits] = {"mask": m, "cert": "rect", "a": a, "d": d,
                        "grid": grid}
        counts["rect"] += 1
        continue
    results[bits] = {"mask": m, "cert": "PROBLEM", "box6": sb}
    counts["PROBLEM"] += 1
    print(f"PROBLEM at held bits {bits} (box6={sb})", flush=True)
    if bits % 128 == 0:
        print(f"  {bits}/1024 {counts}", flush=True)
print("counts:", counts, flush=True)
json.dump(results, open("anyk2d_certtable.json", "w"))
print("wrote anyk2d_certtable.json", flush=True)
