"""N3 first probe: does the ONE-EDGE system detect chirality for every
decoration?

The one-edge system (corner3d_edge.py, Corner3DEdge.lean): the 4 cubes
around one lattice edge — positions (1,1), (1,2), (2,1), (2,2) of one
layer, around the edge from (2,2,0) to (2,2,1) — each showing a
rotation of the decoration d, with COLOR agreement at every lattice
vertex shared by >= 2 of them (10 groups). Any tiling of Z^3 restricts
to such a system around every edge (a vertex coloring is a function),
so edge-UNSAT implies d does not tile.

Key facts:
* every ACHIRAL decoration must be edge-SAT (it tiles, so any finite
  patch is consistent);
* for #10 the reduced dimer model (parity-flip class constraint) is
  exactly this direct system relabeled — edge-UNSAT holds (proven in
  Lean: Corner3DEdge.edge_unsat).

This probe computes, for every canonical decoration at T=2 (23) and
T=3 (333): chiral? edge-SAT? — and tabulates the correlation. A
perfect correlation at T=3 would reduce the full K=1 theorem to a
finite family of edge checks + the (already proven, decoration-generic)
transport machinery.

Run:  ./runpy.sh corner3d_edgeprobe.py
"""
import itertools
import sys

sys.argv = ["corner3d.py"]
import corner3d as C

MIR = [1, 0, 3, 2, 5, 4, 7, 6]

# the 10 shared-vertex groups of the one-edge system
# (cubes 0..3 = (1,1), (1,2), (2,1), (2,2); corners x-fastest)
GROUPS = [
    [(0, 2), (1, 0)],
    [(0, 1), (2, 0)],
    [(0, 3), (1, 1), (2, 2), (3, 0)],
    [(1, 3), (3, 2)],
    [(2, 3), (3, 1)],
    [(0, 6), (1, 4)],
    [(0, 5), (2, 4)],
    [(0, 7), (1, 5), (2, 6), (3, 4)],
    [(1, 7), (3, 6)],
    [(2, 7), (3, 5)],
]

# per cube pair, the groups that couple exactly that pair (for pruning)
PAIR_GROUPS = {(0, 1): [0, 5], (0, 2): [1, 6], (1, 3): [3, 8],
               (2, 3): [4, 9]}
CENTRAL = [2, 7]  # the 4-wise groups


def unique_patterns(d):
    """The rotation orbit of d as a set of 8-tuples."""
    return list({tuple(d[C.SIG[o][p]] for p in range(8))
                 for o in range(24)})


def pair_compat(p1, p2, i, j):
    """Patterns p1 (cube i) and p2 (cube j) agree on their shared
    vertices."""
    for g in PAIR_GROUPS[(i, j)]:
        grp = GROUPS[g]
        vals = {}
        for (c, e) in grp:
            v = (p1 if c == i else p2)[e]
            vals.setdefault(e if c == i else -e - 1, v)
        # simpler: both cubes' entries must be equal pairwise
        a = [p1[e] for (c, e) in grp if c == i]
        b = [p2[e] for (c, e) in grp if c == j]
        if a[0] != b[0]:
            return False
    return True


def edge_sat(d):
    """Brute force with pruning over the 4 cubes' patterns."""
    pats = unique_patterns(d)
    n = len(pats)
    # compatibility tables
    compat = {}
    for (i, j) in PAIR_GROUPS:
        tab = [[False] * n for _ in range(n)]
        for a in range(n):
            for b in range(n):
                tab[a][b] = pair_compat(pats[a], pats[b], i, j)
        compat[(i, j)] = tab

    def central_ok(a, b, c_, d_):
        for g in CENTRAL:
            grp = GROUPS[g]
            vals = []
            for (cb, e) in grp:
                vals.append((pats[a], pats[b], pats[c_], pats[d_])[cb][e])
            if len(set(vals)) > 1:
                return False
        return True

    c01, c02 = compat[(0, 1)], compat[(0, 2)]
    c13, c23 = compat[(1, 3)], compat[(2, 3)]
    for a in range(n):
        row01, row02 = c01[a], c02[a]
        for b in range(n):
            if not row01[b]:
                continue
            row23 = None
            for c_ in range(n):
                if not row02[c_]:
                    continue
                for d_ in range(n):
                    if not c13[b][d_] or not c23[c_][d_]:
                        continue
                    if central_ok(a, b, c_, d_):
                        return True
    return False


def achiral(d):
    dm = tuple(d[MIR[p]] for p in range(8))
    return C.canonical(dm) == C.canonical(d)


def probe(T):
    canons = C.census(T)
    rows = []
    for i, d in enumerate(canons):
        d = tuple(d)
        ach = achiral(d)
        esat = edge_sat(d)
        rows.append((i, d, ach, esat))
    # confusion matrix
    both = sum(1 for r in rows if r[2] and r[3])
    ach_edgeunsat = sum(1 for r in rows if r[2] and not r[3])
    ch_esat = sum(1 for r in rows if not r[2] and r[3])
    ch_eunsat = sum(1 for r in rows if not r[2] and not r[3])
    print(f"T={T}: {len(rows)} canonicals")
    print(f"  achiral & edge-SAT   : {both}   (consistent, expected)")
    print(f"  achiral & edge-UNSAT : {ach_edgeunsat}   (**BUG if >0**)")
    print(f"  chiral  & edge-SAT   : {ch_esat}   (edge too small for these)")
    print(f"  chiral  & edge-UNSAT : {ch_eunsat}   (one-edge obstruction)")
    if ach_edgeunsat:
        for r in rows:
            if r[2] and not r[3]:
                print(f"    BUG row: {r[0]} {r[1]}")
    if ch_esat:
        for r in rows:
            if not r[2] and r[3]:
                print(f"    chiral edge-SAT: {r[0]} {r[1]}")
    return rows


print("=== T=2 sanity (expect: 21 achiral SAT, #10/#11 chiral UNSAT) ===",
      flush=True)
probe(2)
print("=== T=3 ===", flush=True)
probe(3)
