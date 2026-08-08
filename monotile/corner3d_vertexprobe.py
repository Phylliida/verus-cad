"""N3 second probe: the ONE-VERTEX system — 8 cubes around a lattice
vertex — for the 30 chiral T=3 types that survive the one-edge system.

corner3d_edgeprobe.py showed the one-edge system detects chirality
exactly at T=2 and kills 102 of 132 chiral T=3 canonicals. The natural
next core: the 8 cubes around ONE lattice vertex (a 2x2x2 block), with
color agreement at every vertex shared by >= 2 of them (1 eight-wise
central vertex, 6 four-wise face vertices, 12 pairwise edge vertices —
all expressible as pairwise constraints). Any tiling restricts to this
system, so UNSAT implies the decoration does not tile.

Encoded as a binary CSP: per cube, one-hot over its distinct rotation
patterns; incompatibility clauses per cube pair per shared vertex.

Run:  ./runpy.sh corner3d_vertexprobe.py
"""
import itertools
import sys

sys.argv = ["corner3d.py"]
import corner3d as C
from pysat.solvers import Glucose3

MIR = [1, 0, 3, 2, 5, 4, 7, 6]

# the 8 cubes around vertex v=(0,0,0): positions -e for e in {0,1}^3
CUBES = [tuple(-x for x in e) for e in C.CORNERS]  # index by e = cidx

# shared vertices: for each pair of cubes, the lattice vertices they
# share, as ((i, corner_i), (j, corner_j)) pairs
PAIR_SHARED = {}
for i in range(8):
    for j in range(i + 1, 8):
        ci, cj = CUBES[i], CUBES[j]
        verts_i = {tuple(ci[k] + C.CORNERS[e][k] for k in range(3)): e
                   for e in range(8)}
        verts_j = {tuple(cj[k] + C.CORNERS[e][k] for k in range(3)): e
                   for e in range(8)}
        shared = [(verts_i[v], verts_j[v])
                  for v in verts_i if v in verts_j]
        if shared:
            PAIR_SHARED[(i, j)] = shared


def unique_patterns(d):
    return list({tuple(d[C.SIG[o][p]] for p in range(8))
                 for o in range(24)})


def vertex_sat(d):
    pats = unique_patterns(d)
    n = len(pats)

    def var(i, p):
        return i * n + p + 1

    cnf = []
    for i in range(8):
        cnf.append([var(i, p) for p in range(n)])
        for p in range(n):
            for q in range(p + 1, n):
                cnf.append([-var(i, p), -var(i, q)])
    for (i, j), shared in PAIR_SHARED.items():
        for p in range(n):
            for q in range(n):
                if any(pats[p][ei] != pats[q][ej] for (ei, ej) in shared):
                    cnf.append([-var(i, p), -var(j, q)])
    with Glucose3(bootstrap_with=cnf) as s:
        return bool(s.solve())


def achiral(d):
    dm = tuple(d[MIR[p]] for p in range(8))
    return C.canonical(dm) == C.canonical(d)


# the 30 chiral edge-SAT T=3 canonicals (from corner3d_edgeprobe.py)
EDGE_SAT_CHIRAL = [10, 11, 12, 13, 45, 49, 68, 73, 86, 89, 105, 109,
                   124, 128, 132, 136, 138, 139, 140, 142, 143, 144,
                   165, 169, 178, 182, 227, 231, 280, 286]

canons3 = [tuple(d) for d in C.census(3)]

print("=== sanity: achiral T=3 must all be vertex-SAT ===", flush=True)
bad = 0
for i, d in enumerate(canons3):
    if achiral(d) and not vertex_sat(d):
        bad += 1
        print(f"  **BUG: achiral vertex-UNSAT: {i} {d}")
print(f"  achiral vertex-UNSAT count: {bad} (must be 0)")

print("=== T=2 sanity: #10/#11 vertex-UNSAT, rest SAT ===", flush=True)
canons2 = [tuple(d) for d in C.census(2)]
for i in (10, 11):
    print(f"  #{i}: vertex-SAT {vertex_sat(canons2[i])} (expect False)")
print(f"  #0 (achiral): vertex-SAT {vertex_sat(canons2[0])} (expect True)")

print("=== the 30 chiral edge-SAT types vs the one-vertex system ===",
      flush=True)
killed, survived = [], []
for i in EDGE_SAT_CHIRAL:
    d = canons3[i]
    assert not achiral(d)
    if vertex_sat(d):
        survived.append(i)
    else:
        killed.append(i)
print(f"  vertex-UNSAT (killed): {len(killed)}: {killed}")
print(f"  vertex-SAT (survive) : {len(survived)}: {survived}")
