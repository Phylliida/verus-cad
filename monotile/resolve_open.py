"""Resolve the old arena-2 OPEN cases with the modern toolkit:
4-class sheet scan (now covers diagonal planes) + brute lattice sweep.
The 24 previously sheet-decided cases should reconfirm; the 10
holdouts are the targets.

NOTE (local): needs forensics_log.json from the parallel claude.ai
session's outputs — not on this box yet."""
import json
import time
from collections import Counter

from arena2 import (placed_vectors, compat_tables, bad_tables,
                    sheet_scan, solve_lattice_torus, lattice_sweep,
                    box_sat)

if __name__ == "__main__":
    data = json.load(open("forensics_log.json"))
    opens = [tuple(d) for d, _ in data["open"]]
    print(f"{len(opens)} archived OPEN cases")
    results = Counter()
    still = []
    t0 = time.time()
    for i, dec in enumerate(opens):
        if time.time() - t0 > 200:
            print(f"(time cap after {i} cases)")
            break
        placed = placed_vectors(dec)
        compat = compat_tables(placed)
        bad, selfbad = bad_tables(compat)
        hit = sheet_scan(compat)
        if hit is not None:
            B, m = hit
            ts, _ = solve_lattice_torus(B, bad, selfbad)
            if ts:
                idx = B[0][0] * B[1][1] * B[2][2]
                results[f"sheet(idx {idx})"] += 1
                continue
        B, qg = lattice_sweep(bad, selfbad)
        if B is not None:
            idx = B[0][0] * B[1][1] * B[2][2]
            results[f"sweep(idx {idx})"] += 1
            print(f"  case {i}: periodic index {idx} (brute sweep)")
            continue
        results["still-open"] += 1
        still.append((i, dec))
        print(f"  case {i}: STILL OPEN (no sheets, no lattice <= 32)")
    print(f"\nresults: {dict(results)}  [{time.time()-t0:.0f}s]")
    if still:
        print(f"\nescalating {len(still)} still-open: 8^3 tileability")
        for i, dec in still:
            if time.time() - t0 > 240:
                break
            placed = placed_vectors(dec)
            compat = compat_tables(placed)
            bad, selfbad = bad_tables(compat)
            s8, _ = box_sat((8, 8, 8), bad, conf_budget=1_500_000)
            print(f"  case {i}: 8^3 tiles: {s8}")
