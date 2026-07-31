"""Density lemma census-wide check: for each canonical color profile,
compute the allowed face-type pair relation and test for a deficient
class (A pairs only into a set P with |A| > |P|), which by the density
lemma forces emptiness at L > 6/(|A|-|P|). Cross-check against the
campaign verdicts.

NOTE (2026-07-31): the bound was sharpened from 6|P|/(|A|-|P|) (an
arithmetical slip in the original write-up) to 6/(|A|-|P|), as proved in
lean-flocq/LeanFlocq/ColorDensity.lean (`density_obstruction`:
(|A|-|P|)*L <= 6). The two agree when |P| = 1 (e.g. canon 755); the old
formula was conservative, so no past kill was unsound, but some bounds
drop (more boxes killed).

Run:  ./runpy.sh color_density_check.py
"""
import itertools
import json
import os
os.environ.setdefault("ARENA_K", "4")

import arena2
import faceeq3d

CENSUS = json.load(open("faceeq3d_census.json"))
T2E = {}
for key, ei in CENSUS["triple_to_eq"].items():
    ax, o1, o2 = map(int, key.split(","))
    T2E[(ax, o1, o2)] = ei

# sigma[o][w] = base face shown on world direction w (0..5) by orientation o
WORLDFACE = [(ax, s) for ax in range(3) for s in (1, -1)]
SIGMA = []
for o in range(24):
    row = []
    for ax, s in WORLDFACE:
        j = next(i for i, p in enumerate(arena2.PTS)
                 if p[ax] == s * arena2.K)
        row.append(faceeq3d.face_and_coords(arena2.PERMINV[o][j])[0])
    SIGMA.append(row)

# triples by (ax, o1, o2) -> (shown face of o1 on +ax, shown face of o2 on -ax)
TRIPLES = []
for ax in range(3):
    for o1 in range(24):
        for o2 in range(24):
            TRIPLES.append((ax, o1, o2,
                            SIGMA[o1][2 * ax], SIGMA[o2][2 * ax + 1]))


def deficient(prof):
    """Smallest deficiency bound found, or None.

    Sound form (2026-07-31): partners are the symmetrized partner set —
    an A-face pointing either way across an adjacency must land its
    partner in P (an earlier row-only version was unsound for
    non-symmetric relations; the export in color_density_export.py and
    the Lean checker use this sym form)."""
    held = set(prof)
    pair = [[False] * 6 for _ in range(6)]
    for ax, o1, o2, g, h in TRIPLES:
        if T2E[(ax, o1, o2)] in held:
            pair[g][h] = True
    best = None
    for r in range(1, 6):
        for A in itertools.combinations(range(6), r):
            partners = set()
            for g in A:
                partners |= {h for h in range(6) if pair[g][h]}
                partners |= {h for h in range(6) if pair[h][g]}
            if not partners:
                continue  # no adjacencies at all: empty immediately
            # A pairs only into partners; deficient if |A| > |partners|
            if len(A) > len(partners):
                # tileable needs (|A|-|P|)*L <= 6, i.e. L <= 6/(|A|-|P|)
                b = 6 // (len(A) - len(partners))
                if best is None or b < best:
                    best = b
    return best


def main():
    canonical = json.load(open("color3d_canonical.json"))["canonical"]
    verdicts = {}
    for line in open("classify_color.jsonl"):
        r = json.loads(line)
        verdicts[r["i"]] = r["verdict"]
    n = 0
    mismatches = []
    density_kills = {}
    for ci, prof in enumerate(canonical):
        b = deficient(prof)
        if b is not None:
            n += 1
            density_kills[b] = density_kills.get(b, 0) + 1
            v = verdicts.get(ci, "?")
            if not v.startswith("empty") and v != "?":
                mismatches.append((ci, b, v))
    print(f"density-deficient profiles: {n} / {len(canonical)}")
    print(f"bound histogram (max tileable L): {sorted(density_kills.items())}")
    print(f"mismatches (deficient but not empty-verdicted): "
          f"{len(mismatches)}")
    for ci, b, v in mismatches[:10]:
        print(f"  canon {ci}: bound {b}, verdict {v}")


if __name__ == "__main__":
    main()
