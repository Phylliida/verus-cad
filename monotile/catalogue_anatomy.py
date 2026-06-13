"""Anatomy of the 33-pattern catalogue, as input to the completeness
proof effort.

For each pattern S:
  compat_S[ax][o1][o2] = (no degenerate pair) and (all pairs of the
  interface lie in S) -- the SFT of tilings valid for EVERY decoration
  realizing S. Any compat_S tiling's pair-set is contained in S, so:
    * its minimal certifying lattice bounds where S "comes from";
    * if some tiling's pair-set is a PROPER subset, S is not minimal
      in the realizable-pattern poset.

Reports per pattern: |S|, sheet_scan verdict on compat_S (sheet class
+ lattice + index), minimal lattice_sweep index, and whether the
certifying tiling's own pattern is strictly smaller than S.

Also checks catalogue subsumption: S_i superset of any conjugate of
S_j (i != j) means S_i is redundant -- the TRUE minimal catalogue may
be smaller than 33 (dedupe was by equality only).
"""
import json

import numpy as np

from arena2 import (PAIRS, PERM, PATTERN_FILE, sheet_scan, bad_tables,
                    solve_lattice_torus, lattice_sweep,
                    pattern_pairs_lattice)


def compat_of(S):
    compat = np.zeros((3, 24, 24), dtype=bool)
    for ax in range(3):
        for o1 in range(24):
            for o2 in range(24):
                ps = PAIRS[ax][o1][o2]
                compat[ax, o1, o2] = all(
                    a != b and (min(a, b), max(a, b)) in S
                    for a, b in ps)
    return compat


def conjugates(S):
    out = []
    for g in range(24):
        pg = PERM[g]
        out.append(frozenset((min(pg[a], pg[b]), max(pg[a], pg[b]))
                             for a, b in S))
    return out


if __name__ == "__main__":
    with open(PATTERN_FILE) as f:
        data = json.load(f)
    pats = [frozenset((min(a, b), max(a, b)) for a, b in pl)
            for pl in data["patterns"]]
    print(f"{len(pats)} patterns; sizes "
          f"{sorted(len(S) for S in pats)}")

    # ---- subsumption among the catalogue
    redundant = set()
    for i, Si in enumerate(pats):
        for j, Sj in enumerate(pats):
            if i == j or j in redundant:
                continue
            if any(c <= Si for c in conjugates(Sj)):
                redundant.add(i)
                print(f"  pattern {i} (|S|={len(Si)}) SUBSUMED by "
                      f"pattern {j} (|S|={len(Sj)})")
                break
    print(f"subsumption-minimal catalogue: "
          f"{len(pats) - len(redundant)} of {len(pats)}\n")

    # ---- per-pattern certifying anatomy
    sheet_count = 0
    for i, S in enumerate(pats):
        compat = compat_of(S)
        bad, selfbad = bad_tables(compat)
        hit = sheet_scan(compat)
        word = "no-sheet"
        B = None
        if hit is not None:
            B0, m = hit
            ts, qg = solve_lattice_torus(B0, bad, selfbad,
                                         conf_budget=50_000)
            if ts:
                B, qgrid = B0, qg
                word = f"SHEET m={m}"
                sheet_count += 1
        if B is None:
            B, qgrid = lattice_sweep(bad, selfbad)
            if B is not None:
                word += " sweep"
        if B is None:
            print(f"  {i:2d}: |S|={len(S):3d}  NO certifying lattice "
                  f"<= 32 ?!")
            continue
        idx = B[0][0] * B[1][1] * B[2][2]
        Sown = pattern_pairs_lattice(B, qgrid)
        proper = Sown < S
        mark = "  PROPER-SUBSET (S not minimal!)" if proper else ""
        print(f"  {i:2d}: |S|={len(S):3d}  {word:14s} lattice {B} "
              f"idx {idx}  |S_tiling|={len(Sown)}{mark}")
    print(f"\nsheet-certified: {sheet_count}/{len(pats)}")
