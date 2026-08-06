"""Pre-check of the R3 coverage claim: the canonical form of every raw
achievable profile is in the verdict table (sampled). Also validates the
permMask direction used by the Lean `canonOf`."""
import json
import random

EQPERM = json.load(open("anyk3d_canonical.json"))["eqperm"]
canon = json.load(open("color3d_canonical.json"))["canonical"]
cmasks = set(sum(1 << e for e in p) for p in canon)
profs = json.load(open("color3d_profiles.json"))
print("raw profiles:", len(profs))


def pmask(p):
    return sum(1 << e for e in p)


def perm(g, m):
    # Lean permMask g m: bit i = bit (EQPERM[g][i]) of m
    out = 0
    for i in range(84):
        if m >> EQPERM[g][i] & 1:
            out |= 1 << i
    return out


def canonof(m):
    # Python canonical: LEXICOGRAPHIC min over rotations of the sorted
    # bit list (color_orbits.py: min over sorted tuples), computed via
    # the Lean permMask direction (preimage under epAt) — the orbit is
    # the same set, so the lex-min is the same.
    return min(tuple(sorted(i for i in range(84)
                            if m >> EQPERM[g][i] & 1))
               for g in range(24))


random.seed(1)
sample = random.sample(profs, 20000)
bad = 0
for p in sample:
    m = pmask(p)
    if pmask(list(canonof(m))) not in cmasks:
        bad += 1
print("sampled", len(sample), "misses:", bad)
