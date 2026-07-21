"""anyk-08: the 3D slot algebra — face-equation structure of the cube arena.

3D analogue of faceeq2d.py. Each Compat(ax, o1, o2) should be one face
equation

    E(g, h, tau):   F_g = not (F_h o tau)

between two of the 6 base face-grids F_f : TANG^2 -> {+-1}, with tau one of
the 8 grid isometries (signed swaps of (u, v)). This script:

  1. derives (g, h, tau) for all 3*24*24 = 1728 triples from the REAL arena
     geometry (PERMINV + IFACE_PAIRS), asserting every induced grid map is
     a signed swap;
  2. normalizes equations (E(g,h,tau) == E(h,g,tau^-1)), reports the census:
     distinct equation count (the 2D analogue was 10 — decides whether the
     certify-the-whole-superset trick survives in 3D), tau histogram,
     self-equations;
  3. reconstruction validation: rebuilds the full compat table from the
     equations for random decorations and compares with arena2's
     compat_tables — the twist-bookkeeping test against ground truth;
  4. conjugation check: is the equation profile rotation-invariant (2D: yes);
  5. self-gain feasibility table: for each tau, fixed cells of tau on the
     K x K grid by K parity — determines which forced symmetries
     F = -F o tau are satisfiable at which K (the K0-bound raw material).

Run:  ./runpy.sh faceeq3d.py           (K=3 arena)
"""
import itertools
import json
import random

import numpy as np

import arena2
from arena2 import (K, NPTS, PTS, TANG, IFACE_PAIRS, PERM, PERMINV, ROTS,
                    placed_vectors, compat_tables)

NFACE = 6


def face_and_coords(i):
    """Base point index -> (face index, (u, v) tangential coords).
    Faces: axis*2 + (0 if +side else 1); (u, v) along the sorted other axes."""
    p = PTS[i]
    axis = max(range(3), key=lambda k_: abs(p[k_]))
    rest = [k_ for k_ in range(3) if k_ != axis]
    return axis * 2 + (0 if p[axis] > 0 else 1), (p[rest[0]], p[rest[1]])


# ---- the 8 grid isometries: tau = (swap, s1, s2), (u,v) -> signed swap
TAUS = [(sw, s1, s2) for sw in (0, 1) for s1 in (1, -1) for s2 in (1, -1)]


def tau_apply(tau, uv):
    sw, s1, s2 = tau
    u, v = (uv[1], uv[0]) if sw else uv
    return (s1 * u, s2 * v)


def tau_compose(t1, t2):
    """(t1 o t2): apply t2 first."""
    for t in TAUS:
        if all(tau_apply(t, uv) == tau_apply(t1, tau_apply(t2, uv))
               for uv in itertools.product(TANG, TANG)):
            return t
    raise AssertionError


def tau_inv(t):
    for ti in TAUS:
        if tau_compose(ti, t) == (0, 1, 1):
            return ti
    raise AssertionError


def derive_equation(ax, o1, o2):
    maps = {}
    g = h = None
    for pA, pB in IFACE_PAIRS[ax]:
        iA, iB = PERMINV[o1][pA], PERMINV[o2][pB]
        fA, uvA = face_and_coords(iA)
        fB, uvB = face_and_coords(iB)
        g = fA if g is None else g
        h = fB if h is None else h
        assert fA == g and fB == h, "face points scattered"
        maps[uvA] = uvB
    for tau in TAUS:
        if all(tau_apply(tau, uv) == maps[uv] for uv in maps):
            return (g, h, tau)
    raise AssertionError(f"grid map not a signed swap: ax={ax} o1={o1} o2={o2}")


def eq_norm(e):
    g, h, tau = e
    if g < h:
        return (g, h, tau)
    if g > h:
        return (h, g, tau_inv(tau))
    return (g, g, min(tau, tau_inv(tau)))


TRIPLES = [(ax, o1, o2) for ax in range(3)
           for o1 in range(24) for o2 in range(24)]
print("deriving 1728 equations ...", flush=True)
EQ_OF = {tr: derive_equation(*tr) for tr in TRIPLES}
EQS = sorted({eq_norm(e) for e in EQ_OF.values()})
EQ_IDX = {e: i for i, e in enumerate(EQS)}
print(f"distinct equations: {len(EQS)} (2D had 10)", flush=True)
selfeqs = [e for e in EQS if e[0] == e[1]]
print(f"self-equations (g==h): {len(selfeqs)}", flush=True)
from collections import Counter
tau_hist = Counter(e[2] for e in EQS)
print(f"tau histogram: {dict(tau_hist)}", flush=True)
face_pairs = Counter((e[0], e[1]) for e in EQS)
print(f"face-pair multiplicities: {dict(face_pairs)}", flush=True)


# ---- reconstruction validation against the real arena tables
def F_of(dec):
    F = [dict() for _ in range(NFACE)]
    for i in range(NPTS):
        f, uv = face_and_coords(i)
        F[f][uv] = dec[i]
    return F


def compat_via_equations(dec):
    F = F_of(dec)
    hv = {}
    for e in EQS:
        g, h, tau = e
        hv[e] = all(F[g][uv] != F[h][tau_apply(tau, uv)]
                    for uv in itertools.product(TANG, TANG))
    compat = np.zeros((3, 24, 24), dtype=bool)
    for tr in TRIPLES:
        compat[tr] = hv[eq_norm(EQ_OF[tr])]
    return compat


def validate(n=200, seed=5):
    rng = random.Random(seed)
    for j in range(n):
        dec = tuple(rng.choice((1, -1)) for _ in range(NPTS))
        # arena2 compat_tables wants +-1 ints; equations compare bits
        ok = (compat_via_equations(dec) ==
              compat_tables(placed_vectors(dec))).all()
        assert ok, f"reconstruction mismatch at sample {j}"
    print(f"reconstruction OK on {n} random decorations", flush=True)


validate()


# ---- conjugation invariance of the equation profile
def profile(dec):
    F = F_of(dec)
    return tuple(all(F[g][uv] != F[h][tau_apply(tau, uv)]
                     for uv in itertools.product(TANG, TANG))
                 for (g, h, tau) in EQS)


def rot_dec(g, dec):
    return tuple(dec[PERMINV[g][i]] for i in range(NPTS))


rng = random.Random(6)
inv = 0
for _ in range(50):
    dec = tuple(rng.choice((1, -1)) for _ in range(NPTS))
    p0 = profile(dec)
    if all(profile(rot_dec(g, dec)) == p0 for g in range(24)):
        inv += 1
print(f"equation-profile rotation-invariance: {inv}/50 decorations "
      f"(2D was 50/50 — masks C4-invariant)", flush=True)


# ---- self-gain feasibility: fixed cells of each tau by K parity
print("\nself-gain table (F = -F o tau satisfiable iff tau has no fixed "
      "cell; orbits are 1/2/4-cycles):", flush=True)
for tau in TAUS:
    fixed_odd = sum(1 for uv in itertools.product(TANG, TANG)
                    if tau_apply(tau, uv) == uv)
    # K-even grid: TANG has no 0; recompute abstractly for even K via K=2
    tang2 = [-1, 1]
    fixed_even = sum(1 for uv in itertools.product(tang2, tang2)
                     if tau_apply(tau, uv) == uv)
    print(f"  tau={tau}: fixed cells K-odd={fixed_odd} K-even={fixed_even} "
          f"-> F=-F∘tau {'UNSAT' if fixed_odd else 'ok'}(odd) "
          f"{'UNSAT' if fixed_even else 'ok'}(even)", flush=True)

json.dump({"n_equations": len(EQS),
           "equations": [[g, h, list(t)] for (g, h, t) in EQS],
           "triple_to_eq": {f"{ax},{o1},{o2}": EQ_IDX[eq_norm(EQ_OF[tr])]
                            for tr in TRIPLES
                            for (ax, o1, o2) in [tr]}},
          open("faceeq3d_census.json", "w"))
print("\nwrote faceeq3d_census.json", flush=True)
