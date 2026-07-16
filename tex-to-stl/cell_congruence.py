#!/usr/bin/env python3
"""Analyze congruence structure of the 14 cells:
- per-cell direction-class profiles (which of the 15 forced parallel classes
  each cell uses) -> which cells CAN be translates
- length-orbit sharing (parallelogram chains) -> which length equalities are
  already forced
- numerical congruence audit of a given realization

Usage: python3 cell_congruence.py [coords.json]
"""
import json
import math
import sys
from collections import defaultdict

from symmetric_metric_feasibility import (
    UF, edge, sub, dot, norm, unit,
    load_complex, forced_parallel_uf, boundary_structure)


def build_structures():
    _c, _f, cells = load_complex()
    uf, kinds = forced_parallel_uf(cells)
    _fg, corners, paths = boundary_structure(
        cells, "convex_product_coords.json")
    for path in paths:
        for i in range(len(path) - 2):
            uf.union(edge(path[i], path[i + 1]),
                     edge(path[i + 1], path[i + 2]))

    # length orbits: parallelogram merges only (directed, no path merges)
    luf = UF()
    for piece, flist in cells.items():
        kind = kinds[piece]
        if kind == "K5":
            continue
        for f in flist:
            if len(f) != 4:
                continue
            a, b, c, d = f
            luf.union(edge(a, b), edge(c, d))
            luf.union(edge(b, c), edge(a, d))

    all_edges = set()
    for piece, flist in cells.items():
        for f in flist:
            m = len(f)
            for i in range(m):
                all_edges.add(edge(f[i], f[(i + 1) % m]))
    all_edges = sorted(all_edges)

    class_id = {}
    for i, C in enumerate(sorted(uf.classes(all_edges),
                                 key=lambda c: sorted(c)[0])):
        for e in C:
            class_id[e] = i
    orbit_id = {}
    for i, C in enumerate(sorted(luf.classes(all_edges),
                                 key=lambda c: sorted(c)[0])):
        for e in C:
            orbit_id[e] = i
    return cells, kinds, class_id, orbit_id


def cell_edges(flist):
    es = set()
    for f in flist:
        m = len(f)
        for i in range(m):
            es.add(edge(f[i], f[(i + 1) % m]))
    return sorted(es)


def profiles(cells, kinds, class_id, orbit_id):
    print(f"{len(set(class_id.values()))} direction classes, "
          f"{len(set(orbit_id.values()))} length orbits\n")
    prof = {}
    for piece in sorted(cells):
        es = cell_edges(cells[piece])
        cls = defaultdict(list)
        for e in es:
            cls[class_id[e]].append(e)
        orbs = defaultdict(set)
        for e in es:
            orbs[class_id[e]].add(orbit_id[e])
        prof[piece] = (kinds[piece], dict(cls), dict(orbs))
        cls_summary = {c: (len(es_), sorted(orbs[c]))
                       for c, es_ in sorted(cls.items())}
        print(f"{piece} ({kinds[piece]}): classes "
              f"{{cls: (n_edges, orbits)}} = {cls_summary}")
    return prof


def translate_candidates(prof):
    """cells that use identical class sets (necessary for translates)."""
    print("\n=== translate candidates (same direction-class set) ===")
    by_classes = defaultdict(list)
    for piece, (kind, cls, orbs) in prof.items():
        by_classes[(kind, frozenset(cls))].append(piece)
    for (kind, cset), pieces in sorted(by_classes.items(),
                                       key=lambda kv: -len(kv[1])):
        if len(pieces) > 1:
            print(f"  {kind}: {pieces}  classes={sorted(cset)}")
    singles = [p for k, v in by_classes.items() if len(v) == 1 for p in v]
    print(f"  (unique-profile cells: {sorted(singles)})")
    return by_classes


def congruence_audit(cells, kinds, coords_file):
    pos = {v: tuple(p) for v, p in json.load(open(coords_file)).items()}
    print(f"\n=== numerical congruence audit: {coords_file} ===")

    def cell_invariant(piece):
        es = cell_edges(cells[piece])
        lens = sorted(round(norm(sub(pos[a], pos[b])), 4) for a, b in es)
        return lens

    by_kind = defaultdict(list)
    for piece in sorted(cells):
        by_kind[kinds[piece]].append(piece)

    for kind, pieces in sorted(by_kind.items()):
        print(f"  {kind}:")
        for p in pieces:
            inv = cell_invariant(p)
            print(f"    {p}: edge lengths {inv}")


if __name__ == "__main__":
    cells, kinds, class_id, orbit_id = build_structures()
    prof = profiles(cells, kinds, class_id, orbit_id)
    translate_candidates(prof)
    cf = sys.argv[1] if len(sys.argv) > 1 else "typical_look_coords.json"
    congruence_audit(cells, kinds, cf)
