"""Minimal-cube-core hunt for the 4x4 mid-slice contradiction.

corner3d_transfer.py showed: the 4x4 mid slice (one W x H layer of the
reduced dimer model with BOTH plane interfaces channeled, bits free) is
UNSAT, while 3x3 and 3x4 are SAT. Since any #10 tiling of Z^3 restricts
to a 4x4x3 box whose middle layer is a mid slice, this single finite
fact IS the obstruction. Here we shrink it: activate cubes individually
and find minimal sets of cube positions whose constraints are already
contradictory — the candidate "local" contradiction for the proof.

Run:  ./runpy.sh corner3d_core_hunt.py
"""
import itertools
import sys

sys.argv = ["corner3d.py"]
import corner3d as C
from pysat.solvers import Glucose3

from corner3d_transfer import PAIRS, marked_by

W, H = 4, 4
cells = [(x, y) for x in range(W) for y in range(H)]
idx = {c: i for i, c in enumerate(cells)}


def build(kpar):
    """CNF for the mid slice with per-cube activation literals.

    Returns (cnf, act) where act[ci] is the activation var: clauses of
    cube ci (exactly-one pair, mark channeling, interface coupling) are
    all guarded by act[ci]. Vertex equality between a bit and cube ci's
    mark is guarded by act[ci] too (inactive cube = unconstrained).
    """
    n_pair = len(cells) * 12
    n_mark = n_pair + len(cells) * 8
    n_bot = n_mark + (W - 1) * (H - 1)
    n_top = n_bot + (W - 1) * (H - 1)

    def pvar(ci, j):
        return ci * 12 + j + 1

    def mvar(ci, e):
        return n_pair + ci * 8 + e + 1

    def bbit(x, y):
        return n_mark + (x - 1) + (W - 1) * (y - 1) + 1

    def tbit(x, y):
        return n_top + (x - 1) + (W - 1) * (y - 1) + 1

    def act(ci):
        return n_top + (W - 1) * (H - 1) + ci + 1

    cnf = []
    for ci, c in enumerate(cells):
        a = -act(ci)
        cnf.append([a] + [pvar(ci, j) for j in range(12)])
        for j1 in range(12):
            for j2 in range(j1 + 1, 12):
                cnf.append([a, -pvar(ci, j1), -pvar(ci, j2)])
        cp = (c[0] + c[1] + kpar) % 2
        for e in range(8):
            sup = [pvar(ci, j) for j in range(12)
                   if marked_by(e, PAIRS[cp][j], cp)]
            for lit in sup:
                cnf.append([a, -lit, mvar(ci, e)])
            cnf.append([a, -mvar(ci, e)] + sup)
    for plane, bit in ((0, bbit), (1, tbit)):
        for x in range(1, W):
            for y in range(1, H):
                b = bit(x, y)
                for i in (x - 1, x):
                    for j in (y - 1, y):
                        if (i, j) in idx:
                            ci = idx[(i, j)]
                            e = C.cidx((x - i, y - j, plane))
                            m = mvar(ci, e)
                            cnf.append([-act(ci), -m, b])
                            cnf.append([-act(ci), m, -b])
    return cnf, act


def core_for(kpar):
    cnf, act = build(kpar)
    all_on = [act(ci) for ci in range(len(cells))]
    with Glucose3(bootstrap_with=cnf) as s:
        assert not s.solve(assumptions=all_on), "expected UNSAT"
        core_vars = set(s.get_core())
    core = {ci for ci in range(len(cells)) if act(ci) in core_vars}
    # greedy deletion minimization over cubes
    changed = True
    while changed:
        changed = False
        for ci in sorted(core):
            trial = core - {ci}
            assum = ([act(i) for i in trial]
                     + [-act(i) for i in range(len(cells)) if i not in trial])
            with Glucose3(bootstrap_with=cnf) as s:
                if not s.solve(assumptions=assum):
                    core = trial
                    changed = True
                    break
    return sorted(core)


for kpar in (0, 1):
    core = core_for(kpar)
    pos = [cells[ci] for ci in core]
    print(f"kpar={kpar}: minimal cube core size {len(core)}: {pos}")
    # render
    grid = [["." for _ in range(W)] for _ in range(H)]
    for x, y in pos:
        grid[y][x] = "X"
    for row in grid:
        print("   " + "".join(row))
