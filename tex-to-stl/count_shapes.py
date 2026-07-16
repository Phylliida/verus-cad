#!/usr/bin/env python3
"""Count distinct piece shapes in a realization: pairwise congruence test
(direct isometries; mirror reported separately) over all same-type cell
pairs, then connected components = shape classes.

Usage: python3 count_shapes.py <coords.json> [tol]
"""
import json
import sys
from collections import defaultdict

from symmetric_metric_feasibility import (edge, sub, norm, load_complex)
from cell_congruence import build_structures, cell_edges
from congruent_pieces import cell_iso
from ref_match import horn_align


def main():
    coords_file = sys.argv[1]
    tol = float(sys.argv[2]) if len(sys.argv) > 2 else 0.01
    pos = {v: tuple(p) for v, p in json.load(open(coords_file)).items()}
    cells, kinds, class_id, orbit_id = build_structures()

    span = max(max(p[k] for p in pos.values())
               - min(p[k] for p in pos.values()) for k in range(3))
    atol = tol * span

    by_kind = defaultdict(list)
    for piece in sorted(cells):
        by_kind[kinds[piece]].append(piece)

    parent = {p: p for p in cells}

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(a, b):
        parent[find(a)] = find(b)

    print(f"congruence tolerance: {tol:.3%} of span ({atol:.4f})")
    for kind, pieces in sorted(by_kind.items()):
        for i in range(len(pieces)):
            for j in range(i + 1, len(pieces)):
                A, B = pieces[i], pieces[j]
                isos = cell_iso(cells[A], cells[B],
                                defaultdict(int), set(),
                                require_class=False)
                best_d = best_m = None
                for phi in isos:
                    ks = sorted(phi)
                    P = [pos[v] for v in ks]
                    Q = [pos[phi[v]] for v in ks]
                    rd, _t, _r = horn_align(P, Q, allow_reflection=False)
                    rm, _t2, _r2 = horn_align(P, Q, allow_reflection=True)
                    best_d = rd if best_d is None else min(best_d, rd)
                    best_m = rm if best_m is None else min(best_m, rm)
                verdict = ("CONGRUENT" if best_d < atol else
                           ("mirror-congruent" if best_m < atol else "-"))
                if verdict != "-":
                    print(f"  {A} ~ {B}: {verdict} "
                          f"(direct rms {best_d:.4f}, mirror {best_m:.4f})")
                if best_d < atol:
                    union(A, B)

    groups = defaultdict(list)
    for p in cells:
        groups[find(p)].append(p)
    shapes = sorted(groups.values(), key=lambda g: (-len(g), g[0]))
    print(f"\nDISTINCT SHAPES: {len(shapes)}")
    for s in shapes:
        print(f"  {'x'.join(str(len(s)) for _ in [0])} "
              f"[{kinds[s[0]]}] {sorted(s)}")


if __name__ == "__main__":
    main()
