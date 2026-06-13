"""Deep checks for the candidates that survived index<=16 + box5."""
import time
from collections import Counter
from skew import (lattice_classes, hnf_lattices, full_verify, bad_tables,
                  solve_lattice_torus)
from einstein_search import placed_vectors, compat_tables, solve_tiling
from cegis import PERMINV

FINALISTS = [
(1, 1, -1, 1, 1, 1, -1, 1, 1, 1, -1, 1, 1, -1, -1, -1, 1, -1, -1, -1, -1, -1, -1, 1),
(1, -1, -1, 1, 1, -1, 1, -1, 1, -1, -1, 1, -1, 1, -1, 1, 1, 1, -1, -1, -1, 1, -1, 1),
(1, 1, 1, -1, -1, -1, 1, -1, -1, 1, 1, 1, -1, -1, 1, -1, 1, 1, 1, -1, -1, -1, 1, -1),
]

def canon(dec):
    """Canonical representative under rotation x global flip."""
    best = None
    for g in range(24):
        dg = tuple(dec[PERMINV[g][j]] for j in range(24))
        for s in (1, -1):
            t = tuple(s * x for x in dg)
            if best is None or t < best:
                best = t
    return best

if __name__ == "__main__":
    cs = [canon(d) for d in FINALISTS]
    print("distinct tiles among finalists:", len(set(cs)))
    uniq = []
    seen = set()
    for d, c in zip(FINALISTS, cs):
        if c not in seen:
            seen.add(c)
            uniq.append(d)

    t0 = time.time()
    LC24 = lattice_classes(24)
    print(f"sublattice classes up to index 24: {len(LC24)} "
          f"(of {len(hnf_lattices(24))} raw, built in {time.time()-t0:.0f}s)")

    for i, dec in enumerate(uniq):
        t0 = time.time()
        verdict, B, grid = full_verify(dec, lattices=LC24, big_box=6)
        dt = time.time() - t0
        if verdict == "periodic":
            idx = B[0][0] * B[1][1] * B[2][2]
            print(f"finalist {i}: PERIODIC, lattice {B} (index {idx}) "
                  f"[{dt:.0f}s]")
            continue
        if verdict.startswith("untileable"):
            print(f"finalist {i}: {verdict} [{dt:.0f}s]")
            continue
        print(f"finalist {i}: STILL STANDING after index<=24 + box6 "
              f"[{dt:.0f}s]")
        placed = placed_vectors(dec)
        compat = compat_tables(placed)
        sat, grid = solve_tiling((5, 5, 5), False, compat)
        hist = Counter(grid.values())
        print(f"   orientations used in one 5^3 tiling: {len(hist)}/24, "
              f"histogram {sorted(hist.values(), reverse=True)}")
        print(f"   dec = {dec}")
