"""
General periodic tilings: a fully periodic tiling is one invariant under
a FULL-RANK sublattice L of Z^3, not necessarily rectangular. Enumerate
all sublattices up to a given index via row Hermite normal forms

    v1 = (a, b, c),  v2 = (0, d, e),  v3 = (0, 0, f),
    a,d,f >= 1,  0 <= b < d,  0 <= c,e < f,   index = a*d*f,

and SAT-check the quotient torus Z^3 / L for each.
"""
import itertools
from pysat.solvers import Glucose3
from einstein_search import placed_vectors, compat_tables, solve_tiling
from cegis import PAIRS

def hnf_lattices(max_index):
    out = []
    for n in range(1, max_index + 1):
        for a in range(1, n + 1):
            if n % a:
                continue
            m = n // a
            for d in range(1, m + 1):
                if m % d:
                    continue
                f = m // d
                for b in range(d):
                    for c in range(f):
                        for e in range(f):
                            out.append(((a, b, c), (0, d, e), (0, 0, f)))
    return out

# ----------------------------------------------- conjugacy dedupe

def _hnf(M):
    """Row HNF of an integer 3x3 matrix with nonzero determinant:
    upper triangular, positive diagonal, above-diagonal reduced."""
    M = [list(r) for r in M]

    def gcd_rows(i, j, col):
        # zero out M[j][col] using rows i, j (extended Euclid)
        while M[j][col]:
            q = M[i][col] // M[j][col]
            M[i] = [x - q * y for x, y in zip(M[i], M[j])]
            M[i], M[j] = M[j], M[i]

    for j in (1, 2):
        gcd_rows(0, j, 0)
    gcd_rows(1, 2, 1)
    for i in range(3):
        if M[i][i] < 0:
            M[i] = [-x for x in M[i]]
    q = M[0][1] // M[1][1]
    M[0] = [x - q * y for x, y in zip(M[0], M[1])]
    for i in (0, 1):
        q = M[i][2] // M[2][2]
        M[i] = [x - q * y for x, y in zip(M[i], M[2])]
    return tuple(tuple(r) for r in M)

def lattice_classes(max_index):
    """One representative per rotation-conjugacy class. Valid because the
    SFT is equivariant: it has an L-periodic point iff it has a
    gL-periodic point."""
    import numpy as np
    from einstein_search import ROTS
    seen = {}
    for B in hnf_lattices(max_index):
        Bm = np.array(B)
        canon = min(_hnf(Bm @ R.T) for R in ROTS)
        if canon not in seen:
            seen[canon] = B
    return sorted(seen.values(),
                  key=lambda B: B[0][0] * B[1][1] * B[2][2])

def reduce_vec(v, B):
    x, y, z = v
    a, b, c = B[0]
    d, e = B[1][1], B[1][2]
    f = B[2][2]
    k = x // a; x -= k * a; y -= k * b; z -= k * c
    k = y // d; y -= k * d; z -= k * e
    k = z // f; z -= k * f
    return (x, y, z)

def solve_lattice_torus(B, bad, selfbad):
    a, d, f = B[0][0], B[1][1], B[2][2]
    cells = [(x, y, z) for x in range(a) for y in range(d) for z in range(f)]
    idx = {c: i for i, c in enumerate(cells)}

    def var(ci, o):
        return ci * 24 + o + 1

    cnf = []
    for c in cells:
        ci = idx[c]
        cnf.append([var(ci, o) for o in range(24)])
        for o1 in range(24):
            for o2 in range(o1 + 1, 24):
                cnf.append([-var(ci, o1), -var(ci, o2)])
    for c in cells:
        ci = idx[c]
        for ax in range(3):
            nc = list(c)
            nc[ax] += 1
            nci = idx[reduce_vec(tuple(nc), B)]
            if nci == ci:
                cnf.extend([-var(ci, o)] for o in selfbad[ax])
                continue
            cnf.extend([-var(ci, o1), -var(nci, o2)]
                       for o1, o2 in bad[ax])
    with Glucose3(bootstrap_with=cnf) as s:
        if not s.solve():
            return False, None
        model = s.get_model()
    pos = set(v for v in model if v > 0)
    grid = {}
    for c in cells:
        ci = idx[c]
        for o in range(24):
            if var(ci, o) in pos:
                grid[c] = o
    return True, grid

def bad_tables(compat):
    import numpy as np
    bad = [[(int(o1), int(o2)) for o1, o2 in np.argwhere(~compat[ax])]
           for ax in range(3)]
    selfbad = [[o for o in range(24) if not compat[ax, o, o]]
               for ax in range(3)]
    return bad, selfbad

def pattern_pairs_lattice(B, grid):
    S = set()
    for c in grid:
        for ax in range(3):
            nc = list(c)
            nc[ax] += 1
            o1, o2 = grid[c], grid[reduce_vec(tuple(nc), B)]
            for a, b in PAIRS[ax][o1][o2]:
                S.add((min(a, b), max(a, b)))
    return frozenset(S)

LATTICE_CLASSES_16 = lattice_classes(16)

def full_verify(dec, lattices=LATTICE_CLASSES_16, big_box=5):
    placed = placed_vectors(dec)
    compat = compat_tables(placed)
    bad, selfbad = bad_tables(compat)
    for B in lattices:
        sat, grid = solve_lattice_torus(B, bad, selfbad)
        if sat:
            return ("periodic", B, grid)
    sat, _ = solve_tiling((big_box,) * 3, False, compat)
    if not sat:
        return (f"untileable{big_box}", None, None)
    return ("survivor", None, None)

SURVIVORS = [
(1,-1,-1,1,-1,-1,1,-1,1,1,1,-1,1,1,-1,-1,1,1,-1,-1,-1,1,-1,1),
(1,-1,1,-1,1,1,-1,-1,1,-1,-1,1,1,1,-1,-1,-1,-1,1,1,-1,1,-1,1),
(1,-1,1,-1,1,1,-1,-1,-1,-1,1,1,1,-1,-1,1,-1,-1,1,1,1,-1,1,-1),
(1,-1,1,-1,1,1,-1,-1,1,-1,-1,1,1,1,1,-1,1,-1,-1,1,1,-1,-1,-1),
(1,-1,1,-1,1,1,-1,-1,-1,1,-1,1,1,1,1,-1,1,-1,-1,1,1,-1,-1,-1),
(1,1,-1,1,1,1,-1,1,1,1,-1,1,1,-1,-1,-1,1,-1,-1,-1,-1,-1,-1,1),
(1,1,-1,-1,-1,1,1,-1,1,-1,1,-1,-1,1,1,-1,-1,1,-1,1,-1,-1,1,1),
(1,1,-1,-1,1,-1,1,-1,-1,-1,1,-1,-1,1,1,-1,1,-1,1,1,-1,1,-1,1),
(1,1,-1,-1,-1,1,-1,1,-1,1,1,-1,-1,-1,-1,-1,1,1,1,1,-1,1,-1,1),
(1,1,-1,-1,-1,1,-1,1,1,-1,1,-1,-1,-1,-1,-1,1,1,1,1,-1,1,1,-1),
(1,1,-1,-1,-1,1,-1,1,-1,1,1,-1,-1,-1,1,-1,-1,1,1,1,-1,1,-1,1),
(1,1,1,1,-1,1,1,-1,1,1,-1,-1,-1,-1,-1,-1,-1,-1,1,1,1,-1,1,-1),
(1,1,1,1,-1,-1,1,1,-1,1,1,-1,-1,-1,-1,-1,-1,-1,1,1,1,-1,1,-1),
(1,-1,-1,1,1,-1,1,-1,1,-1,-1,1,-1,1,-1,1,1,1,-1,-1,-1,1,-1,1),
(1,1,-1,-1,-1,1,-1,1,-1,1,-1,1,1,1,-1,-1,-1,1,-1,1,-1,-1,1,1),
(1,1,-1,1,1,1,-1,-1,-1,1,1,-1,-1,-1,-1,1,1,1,-1,-1,-1,1,-1,1),
(1,1,1,1,1,1,-1,-1,-1,1,1,-1,-1,-1,-1,-1,1,1,-1,-1,-1,1,-1,1),
(1,1,-1,-1,-1,1,-1,1,-1,1,-1,1,-1,1,1,-1,1,1,-1,-1,-1,1,-1,1),
(1,1,-1,-1,-1,1,-1,-1,-1,1,1,1,-1,1,1,-1,1,1,-1,-1,-1,1,-1,1),
(1,-1,-1,1,-1,-1,-1,1,1,1,-1,1,1,1,-1,-1,-1,-1,1,1,1,-1,1,-1),
(1,1,-1,-1,-1,-1,-1,1,1,1,-1,1,1,1,-1,-1,-1,-1,1,1,1,-1,1,-1),
(1,-1,-1,1,-1,1,-1,1,1,-1,1,-1,1,1,-1,-1,-1,1,-1,1,-1,-1,1,1),
(1,1,1,-1,-1,-1,1,-1,-1,1,1,1,-1,-1,1,-1,1,1,1,-1,-1,-1,1,-1),
(1,1,-1,-1,1,-1,1,-1,-1,1,-1,1,-1,-1,1,1,1,1,-1,-1,1,-1,1,-1),
(1,1,-1,-1,-1,1,-1,1,-1,1,-1,1,1,1,-1,-1,1,1,-1,-1,-1,1,-1,1),
(1,-1,-1,1,1,-1,1,-1,1,-1,1,-1,-1,-1,1,1,-1,-1,1,1,1,-1,1,-1),
]

if __name__ == "__main__":
    from collections import Counter
    import time
    print(f"sublattice classes up to index 16: {len(LATTICE_CLASSES_16)} "
          f"(of {len(hnf_lattices(16))} raw)")
    killers = Counter()
    still = []
    t0 = time.time()
    for i, dec in enumerate(SURVIVORS):
        verdict, B, grid = full_verify(dec)
        if verdict == "periodic":
            killers[B] += 1
            idx = B[0][0] * B[1][1] * B[2][2]
            print(f"  survivor {i:2d}: periodic, lattice {B} (index {idx})")
        else:
            print(f"  survivor {i:2d}: {verdict} <<<<")
            still.append(dec)
    print(f"  ({time.time()-t0:.0f}s total)")
    print()
    print("killer lattices:")
    for B, n in killers.most_common(10):
        print(f"   {B}: {n}")
    print(f"still standing: {len(still)}")
    for d in still:
        print("  ", d)
