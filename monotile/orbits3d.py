"""anyk-08: rotation-orbit reduction of the 3D profile census (v2).

v1 bug (kept for the record): using check_equivariance's transformation
gives the geometry's INTRINSIC symmetry — an identity inside every compat
table — under which every profile is trivially fixed. The action that
matters for orbit reduction is decoration CONJUGATION: profile(rotDec(g,d))
= pi_g(profile(d)). Here pi_g is derived concretely: an equation is a set
of unordered decoration-bit pairs {i, j} constrained to dec[i] = -dec[j];
conjugation transports pair-sets through PERMINV[g]; match the transported
set to the unique equation with that pair-set. (The global bit-complement
acts trivially: it preserves every such constraint.)

Sanity: pi_g must be a permutation of the 84 equations, the map g -> pi_g
a homomorphism-up-to-direction, and for random decorations
profile(rotDec(g,d)) == pi_g-image of profile(d) exactly.

Outputs anyk3d_canonical.json (canonical reps) + eqperm table for the
Lean transport layer.

Run:  ./runpy.sh orbits3d.py
"""
import itertools
import json
import random
import time

import arena2
from arena2 import PERMINV, NPTS, TANG, placed_vectors, compat_tables
from faceeq3d import (EQS, EQ_IDX, face_and_coords, tau_apply, PTS)

# point index of (face, (u,v))
PT_OF = {}
for i in range(NPTS):
    f, uv = face_and_coords(i)
    PT_OF[(f, uv)] = i


def eq_pairset(e):
    """The set of unordered bit-pairs the equation constrains."""
    g, h, tau = e
    return frozenset(
        frozenset((PT_OF[(g, uv)], PT_OF[(h, tau_apply(tau, uv))]))
        for uv in itertools.product(TANG, TANG))


PAIRSET = {eq_pairset(e): i for i, e in enumerate(EQS)}
assert len(PAIRSET) == len(EQS), "equations not determined by pair-sets"

EQPERM = []
for g in range(24):
    perm = []
    for e in EQS:
        moved = frozenset(
            frozenset(PERMINV[g][i] for i in pr) for pr in eq_pairset(e))
        perm.append(PAIRSET[moved])
    assert sorted(perm) == list(range(len(EQS))), f"not a perm at g={g}"
    EQPERM.append(perm)
nontriv = sum(1 for g in range(24)
              if EQPERM[g] != list(range(len(EQS))))
print(f"conjugation action computed; nontrivial for {nontriv}/24 rotations",
      flush=True)


# validation: profile(rotDec(g,d)) must equal pi_g-image of profile(d)
def profile_of(dec):
    import numpy as np
    F = {}
    for i in range(NPTS):
        f, uv = face_and_coords(i)
        F[(f, uv)] = dec[i]
    return frozenset(
        i for i, (g, h, tau) in enumerate(EQS)
        if all(F[(g, uv)] != F[(h, tau_apply(tau, uv))]
               for uv in itertools.product(TANG, TANG)))


rng = random.Random(9)
for _ in range(30):
    dec = tuple(rng.choice((1, -1)) for _ in range(NPTS))
    p0 = profile_of(dec)
    for g in range(24):
        rd = tuple(dec[PERMINV[g][i]] for i in range(NPTS))
        # e held for rd  <=>  transported pair-set held for dec
        expect = frozenset(i for i in range(len(EQS))
                           if EQPERM[g][i] in p0)
        assert profile_of(rd) == expect, f"action mismatch g={g}"
print("action validated on 30 random decorations x 24 rotations", flush=True)

t0 = time.time()
profiles = json.load(open("anyk3d_profiles.json"))
canon = set()
hist = {}
for p in profiles:
    ims = {tuple(sorted(EQPERM[g][e] for e in p)) for g in range(24)}
    canon.add(min(ims))
    hist[len(ims)] = hist.get(len(ims), 0) + 1
print(f"profiles {len(profiles)} -> canonical {len(canon)} "
      f"[{time.time() - t0:.0f}s]", flush=True)
print(f"orbit-size histogram: {sorted(hist.items())}", flush=True)
json.dump({"eqperm": EQPERM,
           "canonical": sorted(list(p) for p in canon)},
          open("anyk3d_canonical.json", "w"))
print("wrote anyk3d_canonical.json", flush=True)
