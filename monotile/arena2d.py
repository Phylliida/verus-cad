"""arena2d: the 2D analogue arena (anyk-06).

Model: one unit square tile, each edge carries K bump/dent bits (an edge is
1-D, so K bits per edge, NPTS = 4K total; the tile space is 2^(4K)).
Orientation group C4 (the 4 rotations; no reflections, matching the 3D
arena's choice). Tilings of Z^2, matching = bitwise complementarity on
touching edges. A decoration is an einstein iff it tiles Z^2 but never
periodically (invariance under a rank-2 lattice).

Purpose (board card anyk-06/07): sweep K upward and watch whether
single-orbit aperiodicity ever switches on as decoration bits grow --
calibration evidence for the 3D any-K question.

v1 = exhaustive classifier (K <= 5 feasible): every canonical decoration is
individually classified, so closure needs no pattern library:
    unbalanced    -- not a space-tiler by the 2D Balance Law (below)
    untileableB   -- box UNSAT (free boundary => sound refutation)
    periodic      -- an explicit quotient-torus tiling found (index recorded)
    SUSPICIOUS    -- none of the above at the sweep bounds; escalate

2D Balance Law (the 3D Lemma A telescoped one dimension down): in an n x n
box tiling, opposite-face point sums cancel across every interior adjacency,
so for any rotation-closed, matching-closed set U of decoration positions,
n^2 * (sum of dec over U) is bounded by the O(n) boundary => the sum is 0.
In C4 the matching couples the orbit of tangential t with the orbit of -t
(unlike the 24-element 3D group, where orbits are matching-closed on their
own), so the correct U's are the orbit-PAIR unions orbit(t) u orbit(-t)
(t=0: the orbit alone). Asserted structurally at import.

Geometry mirrors arena2.py: square side 2K, face coordinate +-K, tangential
offsets {-(K-1), -(K-1)+2, ..., K-1} (K of them; no corner sharing since
K-1 < K). Rotations act on actual point coordinates, so PERM tables are
correct by construction.

Run:  ARENA2D_K=3 ./runpy.sh arena2d.py         # exhaustive sweep
      ARENA2D_K=3 ./runpy.sh arena2d.py test    # self-test only
Results: arena2d_K{K}_results.jsonl + arena2d_K{K}_summary.json
"""
import itertools
import json
import os
import sys
import time

import numpy as np
from pysat.solvers import Glucose3

K = int(os.environ.get("ARENA2D_K", 3))
M = K
TANG = list(range(-(K - 1), K, 2))
assert len(TANG) == K

DIRS = [(1, 0), (0, 1), (-1, 0), (0, -1)]
PTS = []
for d in DIRS:
    for t in TANG:
        # M*d + t*perp(d), perp = 90deg CCW
        PTS.append((M * d[0] - t * d[1], M * d[1] + t * d[0]))
NPTS = 4 * K
PT_IDX = {p: i for i, p in enumerate(PTS)}
assert len(PT_IDX) == NPTS, "corner sharing -- geometry bug"

ROTS = [np.array([[1, 0], [0, 1]]), np.array([[0, -1], [1, 0]]),
        np.array([[-1, 0], [0, -1]]), np.array([[0, 1], [-1, 0]])]
NORI = 4

PERM = [[PT_IDX[tuple(R @ np.array(p))] for p in PTS] for R in ROTS]
PERMINV = [[0] * NPTS for _ in range(NORI)]
for o in range(NORI):
    for i in range(NPTS):
        PERMINV[o][PERM[o][i]] = i

# touching faces: +ax point of the left tile coincides with the -ax point of
# the right tile at the same world position: (M,y)<->(-M,y), (x,M)<->(x,-M)
IFACE_PAIRS = []
for ax in range(2):
    pairs = []
    for t in TANG:
        if ax == 0:
            pairs.append((PT_IDX[(M, t)], PT_IDX[(-M, t)]))
        else:
            pairs.append((PT_IDX[(t, M)], PT_IDX[(t, -M)]))
    IFACE_PAIRS.append(pairs)

# ---- rotation orbits and the balance unions
ORBITS = []
_seen = set()
for i in range(NPTS):
    if i in _seen:
        continue
    orb = {PERM[o][i] for o in range(NORI)}
    _seen |= orb
    ORBITS.append(sorted(orb))
_orbit_of = {}
for oi, orb in enumerate(ORBITS):
    for i in orb:
        _orbit_of[i] = oi

# matching must couple orbits by a well-defined involution
_partner = {}
for pairs in IFACE_PAIRS:
    for a, b in pairs:
        oa, ob = _orbit_of[a], _orbit_of[b]
        assert _partner.setdefault(oa, ob) == ob
        assert _partner.setdefault(ob, oa) == oa
BALANCE_UNIONS = []
_done = set()
for oi, oj in _partner.items():
    key = (min(oi, oj), max(oi, oj))
    if key in _done:
        continue
    _done.add(key)
    U = sorted(set(ORBITS[oi]) | set(ORBITS[oj]))
    assert len(U) % 2 == 0
    BALANCE_UNIONS.append(U)


def balanced(dec):
    return all(sum(dec[i] for i in U) == 0 for U in BALANCE_UNIONS)


# ---- decorations / compat
def placed_vectors(dec):
    out = np.zeros((NORI, NPTS), dtype=np.int8)
    for o in range(NORI):
        for i in range(NPTS):
            out[o, PERM[o][i]] = dec[i]
    return out


def compat_tables(placed):
    compat = np.zeros((2, NORI, NORI), dtype=bool)
    for ax in range(2):
        for o1 in range(NORI):
            for o2 in range(NORI):
                compat[ax, o1, o2] = all(
                    placed[o1][i] + placed[o2][j] == 0
                    for i, j in IFACE_PAIRS[ax])
    return compat


def bad_tables(compat):
    bad = [[(int(o1), int(o2)) for o1, o2 in np.argwhere(~compat[ax])]
           for ax in range(2)]
    selfbad = [[o for o in range(NORI) if not compat[ax, o, o]]
               for ax in range(2)]
    return bad, selfbad


def check_equivariance(compat):
    E = np.eye(2, dtype=int)
    key = {tuple(R.flatten()): o for o, R in enumerate(ROTS)}
    for g in range(NORI):
        gmap = [key[tuple((ROTS[g] @ ROTS[o]).flatten())]
                for o in range(NORI)]
        for ax in range(2):
            w = ROTS[g] @ E[ax]
            bx = int(np.flatnonzero(w)[0])
            sign = int(w[bx])
            for o1 in range(NORI):
                for o2 in range(NORI):
                    lhs = compat[ax, o1, o2]
                    rhs = (compat[bx, gmap[o1], gmap[o2]] if sign == 1
                           else compat[bx, gmap[o2], gmap[o1]])
                    if lhs != rhs:
                        return False
    return True


# ---- solvers
def box_sat(dims, bad, conf_budget=None):
    """Free-boundary box tiling: (True,grid) / (False,None) / (None,None)."""
    cells = list(itertools.product(range(dims[0]), range(dims[1])))
    idx = {c: i for i, c in enumerate(cells)}

    def var(ci, o):
        return ci * NORI + o + 1

    cnf = []
    for c in cells:
        ci = idx[c]
        cnf.append([var(ci, o) for o in range(NORI)])
        for o1 in range(NORI):
            for o2 in range(o1 + 1, NORI):
                cnf.append([-var(ci, o1), -var(ci, o2)])
        for ax in range(2):
            nc = (c[0] + (ax == 0), c[1] + (ax == 1))
            if nc in idx:
                nci = idx[nc]
                cnf.extend([-var(ci, o1), -var(nci, o2)]
                           for o1, o2 in bad[ax])
    with Glucose3(bootstrap_with=cnf) as s:
        if conf_budget is None:
            r = s.solve()
        else:
            s.conf_budget(conf_budget)
            r = s.solve_limited()
        if r is None:
            return None, None
        if not r:
            return False, None
        pos = set(x for x in s.get_model() if x > 0)
        return True, {c: o for c in cells for o in range(NORI)
                      if var(idx[c], o) in pos}


def _hnf2(v1, v2):
    Mrows = [list(map(int, v1)), list(map(int, v2))]
    while Mrows[1][0]:
        q = Mrows[0][0] // Mrows[1][0]
        Mrows[0] = [x - q * y for x, y in zip(Mrows[0], Mrows[1])]
        Mrows[0], Mrows[1] = Mrows[1], Mrows[0]
    for i in range(2):
        if Mrows[i][i] < 0:
            Mrows[i] = [-x for x in Mrows[i]]
    assert Mrows[0][0] > 0 and Mrows[1][1] > 0, "rank-deficient lattice"
    q = Mrows[0][1] // Mrows[1][1]
    Mrows[0] = [x - q * y for x, y in zip(Mrows[0], Mrows[1])]
    return ((Mrows[0][0], Mrows[0][1]), (0, Mrows[1][1]))


def reduce_vec(v, B):
    x, y = v
    a, b = B[0]
    d = B[1][1]
    k = x // a
    x -= k * a
    y -= k * b
    y -= (y // d) * d
    return (x, y)


def lattice_classes(max_index):
    """All finite-index sublattices of Z^2 up to max_index, via unique row
    HNF ((a,b),(0,d)), 0 <= b < d, sorted by index a*d."""
    out = []
    for a in range(1, max_index + 1):
        for d in range(1, max_index // a + 1):
            for b in range(d):
                out.append(((a, b), (0, d)))
    out.sort(key=lambda B: B[0][0] * B[1][1])
    return out


def solve_lattice_torus(B, bad, selfbad, conf_budget=None):
    a, d = B[0][0], B[1][1]
    cells = [(x, y) for x in range(a) for y in range(d)]
    idx = {c: i for i, c in enumerate(cells)}

    def var(ci, o):
        return ci * NORI + o + 1

    cnf = []
    for c in cells:
        ci = idx[c]
        cnf.append([var(ci, o) for o in range(NORI)])
        for o1 in range(NORI):
            for o2 in range(o1 + 1, NORI):
                cnf.append([-var(ci, o1), -var(ci, o2)])
        for ax in range(2):
            nc = (c[0] + (ax == 0), c[1] + (ax == 1))
            nci = idx[reduce_vec(nc, B)]
            if nci == ci:
                cnf.extend([-var(ci, o)] for o in selfbad[ax])
                continue
            cnf.extend([-var(ci, o1), -var(nci, o2)]
                       for o1, o2 in bad[ax])
    with Glucose3(bootstrap_with=cnf) as s:
        if conf_budget is None:
            r = s.solve()
        else:
            s.conf_budget(conf_budget)
            r = s.solve_limited()
        return bool(r) if r is not None else None


# ---- exhaustive classifier
GROUP = [(g, f) for g in range(NORI) for f in (1, -1)]


def canon_key(dec):
    return min(tuple(f * dec[PERMINV[g][i]] for i in range(NPTS))
               for g, f in GROUP)


def classify(dec, box_dims=(6, 6), max_index=32, box_conf=200_000,
             torus_conf=20_000):
    """Verdict for one decoration. Budget-outs escalate, never refute."""
    if not balanced(dec):
        return {"verdict": "unbalanced"}
    placed = placed_vectors(dec)
    bad, selfbad = bad_tables(compat_tables(placed))
    sb, _ = box_sat(box_dims, bad, conf_budget=box_conf)
    if sb is False:
        return {"verdict": f"untileable{box_dims[0]}"}
    unresolved = sb is None
    for B in lattice_classes(max_index):
        ts = solve_lattice_torus(B, bad, selfbad, conf_budget=torus_conf)
        if ts:
            return {"verdict": "periodic", "index": B[0][0] * B[1][1],
                    "lattice": [list(B[0]), list(B[1])]}
        if ts is None:
            unresolved = True
    # escalate once: bigger box, deeper sweep
    sb8, _ = box_sat((8, 8), bad, conf_budget=2_000_000)
    if sb8 is False:
        return {"verdict": "untileable8"}
    for B in lattice_classes(64):
        if B[0][0] * B[1][1] <= max_index:
            continue
        ts = solve_lattice_torus(B, bad, selfbad, conf_budget=torus_conf)
        if ts:
            return {"verdict": "periodic", "index": B[0][0] * B[1][1],
                    "lattice": [list(B[0]), list(B[1])]}
        if ts is None:
            unresolved = True
    return {"verdict": "SUSPICIOUS", "unresolved_budgets": unresolved}


def self_test():
    for o in range(NORI):
        assert sorted(PERM[o]) == list(range(NPTS))
    assert PERM[0] == list(range(NPTS))
    # trivial +faces-bumps decoration: identity translation tiling, index 1
    dec = [0] * NPTS
    for di, d in enumerate(DIRS):
        for t in TANG:
            i = PT_IDX[(M * d[0] - t * d[1], M * d[1] + t * d[0])]
            dec[i] = 1 if di in (0, 1) else -1
    dec = tuple(dec)
    assert balanced(dec)
    bad, selfbad = bad_tables(compat_tables(placed_vectors(dec)))
    assert solve_lattice_torus(((1, 0), (0, 1)), bad, selfbad) is True
    r = classify(dec)
    assert r["verdict"] == "periodic" and r["index"] == 1, r
    # equivariance on a handful of random decorations
    import random
    rng = random.Random(1)
    for _ in range(5):
        dd = tuple(rng.choice((1, -1)) for _ in range(NPTS))
        assert check_equivariance(compat_tables(placed_vectors(dd)))
    print(f"self-test OK (K={K}, NPTS={NPTS}, orbits={len(ORBITS)}, "
          f"balance unions={[len(U) for U in BALANCE_UNIONS]})", flush=True)


def run():
    t0 = time.time()
    reps = []
    for bits in range(1 << NPTS):
        dec = tuple(1 if (bits >> i) & 1 else -1 for i in range(NPTS))
        if canon_key(dec) == dec:
            reps.append(dec)
    print(f"K={K}: {1 << NPTS} decorations, {len(reps)} canonical reps "
          f"[{time.time() - t0:.0f}s]", flush=True)
    logf = open(f"arena2d_K{K}_results.jsonl", "w")
    counts, idx_hist, suspicious = {}, {}, []
    for n, dec in enumerate(reps):
        r = classify(dec)
        v = r["verdict"]
        counts[v] = counts.get(v, 0) + 1
        if v == "periodic":
            idx_hist[r["index"]] = idx_hist.get(r["index"], 0) + 1
        rec = {"dec": list(dec), **r}
        logf.write(json.dumps(rec) + "\n")
        if v == "SUSPICIOUS":
            suspicious.append(list(dec))
            print(f"  *** SUSPICIOUS *** {list(dec)}", flush=True)
        if (n + 1) % 200 == 0:
            print(f"  {n + 1}/{len(reps)} {counts} [{time.time() - t0:.0f}s]",
                  flush=True)
            logf.flush()
    logf.close()
    summary = {"K": K, "reps": len(reps), "counts": counts,
               "indices": {str(k): v for k, v in sorted(idx_hist.items())},
               "suspicious": suspicious,
               "secs": round(time.time() - t0, 1)}
    with open(f"arena2d_K{K}_summary.json", "w") as f:
        json.dump(summary, f, indent=1)
    print(json.dumps(summary), flush=True)


if __name__ == "__main__":
    self_test()
    if len(sys.argv) > 1 and sys.argv[1] == "test":
        sys.exit(0)
    run()
