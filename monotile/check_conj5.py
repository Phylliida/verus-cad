import itertools, json, random
import numpy as np
import arena2
from arena2 import ROTS, PERMINV, NPTS, placed_vectors, compat_tables
from faceeq3d import EQS, EQ_IDX, EQ_OF, eq_norm, face_and_coords, tau_apply, PTS

PI = json.load(open("anyk3d_tripleperm.json"))
EQPERM = json.load(open("anyk3d_canonical.json"))["eqperm"]

def profile_of(dec):
    F = {}
    for i in range(NPTS):
        f, uv = face_and_coords(i)
        F[(f, uv)] = dec[i]
    return frozenset(
        i for i, (g, h, tau) in enumerate(EQS)
        if all(F[(g, uv)] != F[(h, tau_apply(tau, uv))]
               for uv in itertools.product([-2, 0, 2], repeat=2)))

rng = random.Random(7)
mism_pi = mism_ep = 0
for _ in range(20):
    dec = tuple(rng.choice((1, -1)) for _ in range(NPTS))
    p0 = profile_of(dec)
    for g in range(1, 24):
        rd = tuple(dec[PERMINV[g][i]] for i in range(NPTS))
        prd = profile_of(rd)
        if prd != frozenset(i for i in range(84) if PI[g][i] in p0):
            mism_pi += 1
        if prd != frozenset(i for i in range(84) if EQPERM[g][i] in p0):
            mism_ep += 1
print(f"profile(rotDec) vs pi-image mismatches: {mism_pi}")
print(f"profile(rotDec) vs EQPERM-image mismatches: {mism_ep} (orbits3d validated 0)")
