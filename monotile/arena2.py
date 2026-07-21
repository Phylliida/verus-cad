"""
Arena 2: equivariant aperiodic Wang cube search with k x k binary faces.

Default K = 3: each face carries a 3x3 grid of bumps/dents, 54 decoration
bits total, decoration space 2^54 -- CEGIS only.

Verifier upgrade (the arena-1 lesson): instead of enumerating period
lattices and praying the index bound is high enough, the verifier runs a
PERIOD-FINDER:
  1. one box solver per candidate with selector-guarded identification
     constraints x[c] == x[c+v] for the 19 canonical vector orbits
     (|coords| <= 3); solving under assumption sel_v detects a
     v-invariant patch,
  2. the patch's full internal symmetry is extracted,
  3. the implied full-rank lattice is verified on its quotient torus,
  4. a confirmed kill becomes a conjugated XOR pattern-block that removes
     EVERY decoration realizing that periodic pattern.
Identification UNSAT is a sound refutation: no tiling anywhere is
invariant under any vector in that orbit (covers rank-1 and rank-2).
"""
import itertools
import json
import os
import sys
import time
from collections import Counter
import numpy as np
from pysat.solvers import Glucose3
from pysat.card import CardEnc, EncType

K = int(os.environ.get("ARENA_K", 3))
KSUF = "" if K == 3 else f"_K{K}"
NPTS = 6 * K * K

# ---------------------------------------------------------------- geometry

def rotation_group():
    mats = []
    for perm in itertools.permutations(range(3)):
        for signs in itertools.product((1, -1), repeat=3):
            M = np.zeros((3, 3), dtype=int)
            for i, (p, s) in enumerate(zip(perm, signs)):
                M[i, p] = s
            if round(np.linalg.det(M)) == 1:
                mats.append(M)
    return mats

ROTS = rotation_group()
ROT_KEY = {tuple(M.flatten()): i for i, M in enumerate(ROTS)}

def surface_points(k):
    """Face coordinate +/-k, tangential coords in {-(k-1),...,k-1} step 2."""
    tang = list(range(-(k - 1), k, 2))
    pts = []
    for axis in range(3):
        for s in (k, -k):
            rest = [i for i in range(3) if i != axis]
            for a in tang:
                for b in tang:
                    p = [0, 0, 0]
                    p[axis] = s
                    p[rest[0]] = a
                    p[rest[1]] = b
                    pts.append(tuple(p))
    return pts

PTS = surface_points(K)
PT_INDEX = {p: i for i, p in enumerate(PTS)}
assert len(PTS) == NPTS

def face_point(axis, val, a, b):
    rest = [i for i in range(3) if i != axis]
    p = [0, 0, 0]
    p[axis] = val
    p[rest[0]] = a
    p[rest[1]] = b
    return tuple(p)

TANG = list(range(-(K - 1), K, 2))
IFACE_PAIRS = []
for ax in range(3):
    pairs = []
    for a in TANG:
        for b in TANG:
            pairs.append((PT_INDEX[face_point(ax, K, a, b)],
                          PT_INDEX[face_point(ax, -K, a, b)]))
    IFACE_PAIRS.append(pairs)

PERM = [[PT_INDEX[tuple(R @ np.array(p))] for p in PTS] for R in ROTS]
PERMINV = []
for o in range(24):
    inv = [0] * NPTS
    for i, j in enumerate(PERM[o]):
        inv[j] = i
    PERMINV.append(inv)

PAIRS = [[[None] * 24 for _ in range(24)] for _ in range(3)]
for ax in range(3):
    for o1 in range(24):
        for o2 in range(24):
            PAIRS[ax][o1][o2] = [(PERMINV[o1][jA], PERMINV[o2][jB])
                                 for jA, jB in IFACE_PAIRS[ax]]

# ---------------------------------------------------------- decorations

def placed_vectors(dec):
    out = np.zeros((24, NPTS), dtype=np.int8)
    for o in range(24):
        for i in range(NPTS):
            out[o, PERM[o][i]] = dec[i]
    return out

def compat_tables(placed):
    compat = np.zeros((3, 24, 24), dtype=bool)
    for ax in range(3):
        pairs = IFACE_PAIRS[ax]
        for o1 in range(24):
            v1 = placed[o1]
            for o2 in range(24):
                v2 = placed[o2]
                compat[ax, o1, o2] = all(v1[i] + v2[j] == 0
                                         for i, j in pairs)
    return compat

def bad_tables(compat):
    bad = [[(int(o1), int(o2)) for o1, o2 in np.argwhere(~compat[ax])]
           for ax in range(3)]
    selfbad = [[o for o in range(24) if not compat[ax, o, o]]
               for ax in range(3)]
    return bad, selfbad

def orbit_size(placed):
    return len({tuple(row) for row in placed})

def check_equivariance(compat):
    E = np.eye(3, dtype=int)
    for g in ROTS:
        gmap = [ROT_KEY[tuple((g @ ROTS[o]).flatten())] for o in range(24)]
        for ax in range(3):
            w = g @ E[ax]
            bx = int(np.flatnonzero(w)[0])
            sign = int(w[bx])
            for o1 in range(24):
                for o2 in range(24):
                    lhs = compat[ax, o1, o2]
                    rhs = (compat[bx, gmap[o1], gmap[o2]] if sign == 1
                           else compat[bx, gmap[o2], gmap[o1]])
                    if lhs != rhs:
                        return False
    return True

# ------------------------------------------------------- generic solvers

def box_solver_cnf(dims, bad):
    cells = list(itertools.product(*[range(d) for d in dims]))
    idx = {c: i for i, c in enumerate(cells)}

    def var(ci, o):
        return ci * 24 + o + 1

    cnf = []
    for c in cells:
        ci = idx[c]
        cnf.append([var(ci, o) for o in range(24)])
        for o1 in range(24):
            for o2 in range(o1 + 1, 24):
                cnf.append([-var(ci, o1), -var(ci, o2)])
    for c in cells:
        ci = idx[c]
        for ax in range(3):
            nc = list(c)
            nc[ax] += 1
            if nc[ax] == dims[ax]:
                continue
            nci = idx[tuple(nc)]
            cnf.extend([-var(ci, o1), -var(nci, o2)] for o1, o2 in bad[ax])
    return cnf, cells, idx, var

def extract_grid(model, cells, idx, var):
    pos = set(x for x in model if x > 0)
    grid = {}
    for c in cells:
        ci = idx[c]
        for o in range(24):
            if var(ci, o) in pos:
                grid[c] = o
    return grid

def lsolve(s, conf, assumptions=()):
    """Tri-state solve: True / False / None (conflict budget exceeded).
    Compatibility shim for the parallel branch's arena3/arena4 code."""
    s.conf_budget(conf)
    return s.solve_limited(assumptions=list(assumptions))

def box_sat(dims, bad, identify=None, conf_budget=None):
    """Returns (True, grid) / (False, None) / (None, None) on budget-out."""
    cnf, cells, idx, var = box_solver_cnf(dims, bad)
    if identify is not None:
        v = identify
        for c in cells:
            c2 = (c[0] + v[0], c[1] + v[1], c[2] + v[2])
            if c2 in idx:
                ci, c2i = idx[c], idx[c2]
                for o in range(24):
                    cnf.append([-var(ci, o), var(c2i, o)])
                    cnf.append([var(ci, o), -var(c2i, o)])
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
        return True, extract_grid(s.get_model(), cells, idx, var)

def _hnf(M):
    M = [[int(x) for x in r] for r in M]

    def gcd_rows(i, j, col):
        while M[j][col]:
            q = M[i][col] // M[j][col]
            M[i] = [x - q * y for x, y in zip(M[i], M[j])]
            M[i], M[j] = M[j], M[i]

    for j in (1, 2):
        gcd_rows(0, j, 0)
    gcd_rows(1, 2, 1)
    for i in range(3):
        if M[i][i] < 0:
            M[i] = [-x for x in M[i]]
    q = M[0][1] // M[1][1]
    M[0] = [x - q * y for x, y in zip(M[0], M[1])]
    for i in (0, 1):
        q = M[i][2] // M[2][2]
        M[i] = [x - q * y for x, y in zip(M[i], M[2])]
    return tuple(tuple(r) for r in M)

def reduce_vec(v, B):
    x, y, z = v
    a, b, c = B[0]
    d, e = B[1][1], B[1][2]
    f = B[2][2]
    k = x // a; x -= k * a; y -= k * b; z -= k * c
    k = y // d; y -= k * d; z -= k * e
    k = z // f; z -= k * f
    return (x, y, z)

def solve_lattice_torus(B, bad, selfbad, conf_budget=None):
    a, d, f = B[0][0], B[1][1], B[2][2]
    cells = [(x, y, z) for x in range(a) for y in range(d)
             for z in range(f)]
    idx = {c: i for i, c in enumerate(cells)}

    def var(ci, o):
        return ci * 24 + o + 1

    cnf = []
    for c in cells:
        ci = idx[c]
        cnf.append([var(ci, o) for o in range(24)])
        for o1 in range(24):
            for o2 in range(o1 + 1, 24):
                cnf.append([-var(ci, o1), -var(ci, o2)])
    for c in cells:
        ci = idx[c]
        for ax in range(3):
            nc = list(c)
            nc[ax] += 1
            nci = idx[reduce_vec(tuple(nc), B)]
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
        if r is None:
            return None, None
        if not r:
            return False, None
        return True, extract_grid(s.get_model(), cells, idx, var)

# ------------------------------------------------------- period finder

def canonical_vectors(maxc):
    return [(a, b, c) for a in range(maxc + 1)
            for b in range(a, maxc + 1)
            for c in range(b, maxc + 1) if (a, b, c) != (0, 0, 0)]

# sorted by norm: short vectors mean tight periods, small quotient tori
# and early cheap kills -- probe them first
CANON3 = sorted(canonical_vectors(3),
                key=lambda v: v[0] * v[0] + v[1] * v[1] + v[2] * v[2])

# ------------------------------------------- rank-2 sheet decision
# Reduction Lemma: a tiling invariant under a rank-2 lattice L2 yields,
# via the 1D quotient SFT, a fully periodic tiling. Conversely the
# quotient digraph has a biinfinite walk iff it has a cycle, so rank-2
# sheet invariance is DECIDABLE. One representative per rotation-
# conjugacy class suffices by equivariance.

def _min_cycle(nstates, succ):
    best = None
    for s in range(nstates):
        dist = [-1] * nstates
        frontier = list(succ[s])
        for j in frontier:
            if dist[j] < 0:
                dist[j] = 1
        while frontier and dist[s] < 0:
            nxt = []
            for x in frontier:
                for y in succ[x]:
                    if dist[y] < 0:
                        dist[y] = dist[x] + 1
                        nxt.append(y)
            frontier = nxt
        if dist[s] > 0 and (best is None or dist[s] < best):
            best = dist[s]
    return best

def sheet_scan(compat, max_states=200):
    """Try the 4 sheet classes; return (B, m) for a confirmed full-rank
    lattice from a cycle, or None."""
    # class 1: full coordinate plane, transverse x
    states = [o for o in range(24)
              if compat[1, o, o] and compat[2, o, o]]
    sidx = {a: i for i, a in enumerate(states)}
    succ = [[sidx[b] for b in states if compat[0, a, b]]
            for a in states]
    m = _min_cycle(len(states), succ)
    if m:
        return _hnf(((m, 0, 0), (0, 1, 0), (0, 0, 1))), m
    # class 2: coordinate D2 plane (fiber 2), transverse x
    st2 = [(o0, o1) for o0 in range(24) for o1 in range(24)
           if compat[1, o0, o1] and compat[1, o1, o0]
           and compat[2, o0, o1] and compat[2, o1, o0]]
    if len(st2) <= max_states:
        sidx = {s: i for i, s in enumerate(st2)}
        succ = [[sidx[(b0, b1)] for (b0, b1) in st2
                 if compat[0, a0, b0] and compat[0, a1, b1]]
                for (a0, a1) in st2]
        m = _min_cycle(len(st2), succ)
        if m:
            return _hnf(((m, 0, 0), (0, 1, 1), (0, 1, -1))), m
    # class 3: face-diagonal plane ker(x+y); e_z in-plane
    st3 = [o for o in range(24) if compat[2, o, o]]
    sidx = {a: i for i, a in enumerate(st3)}
    succ = [[sidx[b] for b in st3
             if compat[0, a, b] and compat[1, a, b]] for a in st3]
    m = _min_cycle(len(st3), succ)
    if m:
        return _hnf(((m, 0, 0), (1, -1, 0), (0, 0, 1))), m
    # class 4: body-diagonal plane ker(x+y+z)
    succ = [[b for b in range(24)
             if compat[0, a, b] and compat[1, a, b] and compat[2, a, b]]
            for a in range(24)]
    m = _min_cycle(24, succ)
    if m:
        return _hnf(((m, 0, 0), (1, -1, 0), (0, 1, -1))), m
    return None

def held_vectors(grid, maxc, min_pairs):
    held = []
    rng = range(-maxc, maxc + 1)
    for w in itertools.product(rng, rng, rng):
        if w == (0, 0, 0) or w < tuple(-x for x in w):
            continue
        npairs = 0
        ok = True
        for c in grid:
            c2 = (c[0] + w[0], c[1] + w[1], c[2] + w[2])
            if c2 in grid:
                npairs += 1
                if grid[c] != grid[c2]:
                    ok = False
                    break
        if ok and npairs >= min_pairs:
            held.append(w)
    return held

def det3i(u, v, w):
    return (u[0] * (v[1] * w[2] - v[2] * w[1])
            - u[1] * (v[0] * w[2] - v[2] * w[0])
            + u[2] * (v[0] * w[1] - v[1] * w[0]))

def norm2(v):
    return v[0] * v[0] + v[1] * v[1] + v[2] * v[2]

def cross3i(a, b):
    return (a[1] * b[2] - a[2] * b[1],
            a[2] * b[0] - a[0] * b[2],
            a[0] * b[1] - a[1] * b[0])

def implied_lattices(held, max_index=96, max_tries=None, max_held=40):
    """Small-index lattices spanned by held vectors, sorted by index.

    held is capped to the max_held shortest vectors: a high-symmetry
    patch can hold ~350 vectors and C(350,3) determinants is a
    multi-minute tarpit, while every small-index lattice we can verify
    is already generated by short vectors. Missing one is sound: the
    caller just fails to confirm and the candidate is logged.
    """
    held = sorted(held, key=norm2)[:max_held]
    cands = {}
    for trip in itertools.combinations(held, 3):
        d = abs(det3i(*trip))
        if 0 < d <= max_index:
            B = _hnf(trip)
            if B not in cands:
                cands[B] = d
    out = [B for B, d in sorted(cands.items(), key=lambda kv: kv[1])]
    return out if max_tries is None else out[:max_tries]

def held_plane_basis(held):
    """If held spans a rank-2 plane, return two short independent
    vectors from it; None if rank != 2."""
    base = []
    for v in sorted(held, key=norm2):
        if not base:
            base.append(v)
        elif len(base) == 1:
            if cross3i(base[0], v) != (0, 0, 0):
                base.append(v)
        elif det3i(base[0], base[1], v) != 0:
            return None                     # rank 3
    return base if len(base) == 2 else None

def rank2_completions(held, max_index=64, max_held=12, max_u=2):
    """Slab-locked patches hold only coplanar vectors, so no triple of
    held vectors is full-rank and implied_lattices is structurally
    blind. Complete pairs of short held vectors with enumerated short
    OUT-OF-PLANE third vectors u instead; sorted by index."""
    base = held_plane_basis(held)
    if base is None:
        return []
    n = cross3i(base[0], base[1])
    held_s = sorted(held, key=norm2)[:max_held]
    cands = {}
    rng = range(-max_u, max_u + 1)
    for u in itertools.product(rng, rng, rng):
        if u[0] * n[0] + u[1] * n[1] + u[2] * n[2] == 0:
            continue
        for hi, hj in itertools.combinations(held_s, 2):
            d = abs(det3i(hi, hj, u))
            if 0 < d <= max_index:
                B = _hnf((hi, hj, u))
                if B not in cands:
                    cands[B] = d
    return [B for B, d in sorted(cands.items(), key=lambda kv: kv[1])]

EXTRA4 = [v for v in canonical_vectors(4) if max(v) > 3]

_LC = {}

def lattice_sweep(bad, selfbad, max_index=32):
    """Brute sweep over ALL sublattice classes up to max_index
    (rotation-conjugacy reps from skew). Decisive backstop for anything
    the held-vector heuristics miss at small index."""
    if max_index not in _LC:
        from skew import lattice_classes
        _LC[max_index] = list(lattice_classes(max_index))
    for B in _LC[max_index]:
        ts, qg = solve_lattice_torus(B, bad, selfbad,
                                     conf_budget=TORUS_CONF)
        if ts:
            return B, qg
    return None, None

def deep_check(bad, selfbad):
    """Gauntlet for in-loop survivors: brute lattices <= 32, extended
    vectors with a coordinate 4 at 6^3, then an 8^3 box. Only what
    passes ALL of it earns the name DEEP-SURVIVOR."""
    B, qg = lattice_sweep(bad, selfbad)
    if B is not None:
        return ("periodic-deep", B, qg)
    for v in EXTRA4:
        sv, gv = box_sat((6, 6, 6), bad, identify=v,
                         conf_budget=300_000)
        if sv is None:
            return ("ext-timeout", None, None)
        if sv:
            held = held_vectors(gv, 4, 12)
            for B in implied_lattices(held)[:12]:
                ts, qg = solve_lattice_torus(B, bad, selfbad,
                                             conf_budget=TORUS_CONF)
                if ts:
                    return ("periodic-deep", B, qg)
            return ("suspicious-ext", None, None)
    s8, _ = box_sat((8, 8, 8), bad, conf_budget=2_000_000)
    if s8 is False:
        return ("untileable8", None, None)
    if s8 is None:
        return ("box8-timeout", None, None)
    return ("DEEP-SURVIVOR", None, None)

def pattern_pairs_lattice(B, grid):
    S = set()
    for c in grid:
        for ax in range(3):
            nc = list(c)
            nc[ax] += 1
            o1, o2 = grid[c], grid[reduce_vec(tuple(nc), B)]
            for a, b in PAIRS[ax][o1][o2]:
                S.add((min(a, b), max(a, b)))
    return frozenset(S)

SEL4_CONF = 10_000      # selector solve at the 4^3 detector
SEL6_CONF = 25_000      # selector solve at the 6^3 detector
BOX5_CONF = 50_000      # 5^3 tileability check
BOX8_CONF = 5_000_000   # 8^3 tileability backstop (looser matchings, K<3)
TORUS_CONF = 10_000     # quotient-torus solve per candidate lattice
VERDICT_TIME_CAP = 240.0  # wall-clock safety net per candidate

class Verifier:
    """Per-candidate verifier with integrated period finder.

    Every SAT call is conflict-budgeted so a single candidate can never
    wedge the CEGIS loop. A budget-out is NOT treated as a refutation:
    the vector is marked unresolved, the candidate gets point-blocked
    and logged. Refutations ("v holds nowhere") still require true
    UNSAT, so all kills remain sound.
    """

    def __init__(self, dec, det_dims=(4, 4, 4)):
        self.dec = dec
        self.placed = placed_vectors(dec)
        self.compat = compat_tables(self.placed)
        self.bad, self.selfbad = bad_tables(self.compat)
        self.det4 = self._detector(det_dims)
        self.det6 = None                  # built lazily; most candidates
                                          # die at the 4^3 stage
        self.failed_lattices = set()      # UNSAT/budget-out tori, shared
                                          # across all 19 vectors
        self.phase = Counter()

    def _detector(self, dims):
        """Incremental box instance with one identification selector
        per canonical vector: solve(assumptions=[sel_v]) searches for a
        v-invariant patch; UNSAT refutes v everywhere."""
        cnf, cells, idx, var = box_solver_cnf(dims, self.bad)
        sels = {}
        nv = len(cells) * 24
        for v in CANON3:
            nv += 1
            sels[v] = nv
            for c in cells:
                c2 = (c[0] + v[0], c[1] + v[1], c[2] + v[2])
                if c2 in idx:
                    ci, c2i = idx[c], idx[c2]
                    for o in range(24):
                        cnf.append([-nv, -var(ci, o), var(c2i, o)])
                        cnf.append([-nv, var(ci, o), -var(c2i, o)])
        return (Glucose3(bootstrap_with=cnf), cells, idx, var, sels)

    def close(self):
        self.det4[0].delete()
        if self.det6 is not None:
            self.det6[0].delete()

    def _sel_solve(self, det, v, budget):
        s, cells, idx, var, sels = det
        s.conf_budget(budget)
        r = s.solve_limited(assumptions=[sels[v]])
        if r is None or r is False:
            return r, None
        return True, extract_grid(s.get_model(), cells, idx, var)

    def confirm_period(self, grid, maxc, min_pairs, max_tries=8,
                       max_held=48, completions=True):
        held = held_vectors(grid, maxc, min_pairs)
        cands = implied_lattices(held, max_held=max_held)
        if not cands and completions:
            # coplanar held set (slab-locked patch): complete the
            # plane with enumerated out-of-plane vectors instead.
            # These tori are tiny (small index), so dig much deeper:
            # the true lattice often ranks behind dozens of fakes.
            cands = rank2_completions(held)
            max_tries = max(max_tries, 48)
        tries = 0
        for B in cands:
            if B in self.failed_lattices:
                continue                  # don't burn a try on a
                                          # known-failed lattice
            if tries >= max_tries:
                break
            tries += 1
            sat, qgrid = solve_lattice_torus(B, self.bad, self.selfbad,
                                             conf_budget=TORUS_CONF)
            if sat:
                return B, qgrid
            self.failed_lattices.add(B)
        return None, None

    def verdict(self):
        if orbit_size(self.placed) < 24:
            return ("symmetric", None, None)
        t0 = time.time()
        # stage 0: exact sheet decision on the compat tables -- catches
        # the dominant sheet-periodic families in milliseconds, before
        # any SAT work
        hit = sheet_scan(self.compat)
        self.phase["sheet"] += time.time() - t0
        if hit is not None:
            B, m = hit
            sat, qgrid = solve_lattice_torus(B, self.bad, self.selfbad,
                                             conf_budget=TORUS_CONF)
            if sat:
                return ("periodic", B, qgrid)
        suspicious, unresolved = [], []
        for v in CANON3:
            if time.time() - t0 > VERDICT_TIME_CAP:
                unresolved.append(("timecap", v))
                continue
            t = time.time()
            r, grid = self._sel_solve(self.det4, v, SEL4_CONF)
            self.phase["sel4"] += time.time() - t
            if r is False:
                continue                   # v refuted at detector box
            if r is None:
                unresolved.append(("det4", v))
                continue
            t = time.time()
            # implied-only at 4^3: the small noisy held sets make
            # completions here duplicate the 6^3 stage's work
            B, qgrid = self.confirm_period(grid, maxc=3, min_pairs=4,
                                           completions=False)
            self.phase["confirm4"] += time.time() - t
            if B is not None:
                return ("periodic", B, qgrid)
            if self.det6 is None:
                t = time.time()
                self.det6 = self._detector((6, 6, 6))
                self.phase["build6"] += time.time() - t
            t = time.time()
            r, grid6 = self._sel_solve(self.det6, v, SEL6_CONF)
            self.phase["sel6"] += time.time() - t
            if r is False:
                continue                   # v refuted at 6^3
            if r is None:
                unresolved.append(("det6", v))
                continue
            t = time.time()
            B, qgrid = self.confirm_period(grid6, maxc=5, min_pairs=6)
            self.phase["confirm6"] += time.time() - t
            if B is not None:
                return ("periodic", B, qgrid)
            suspicious.append(v)
        # Rank-2 escalation: the solver returns SOME v-invariant patch,
        # and a messy one can hide its full lattice from the held-vector
        # reader. A patch invariant under TWO canonical vectors at once
        # almost never can. The selectors already exist, so pairs cost
        # one budgeted solve each, only on suspicious candidates.
        if len(suspicious) >= 2 and self.det6 is not None:
            for v, w in itertools.combinations(suspicious, 2):
                if time.time() - t0 > VERDICT_TIME_CAP:
                    break
                s6, cells, idx, var, sels = self.det6
                t = time.time()
                s6.conf_budget(SEL6_CONF)
                r = s6.solve_limited(assumptions=[sels[v], sels[w]])
                self.phase["pair6"] += time.time() - t
                if r is not True:
                    continue
                grid6 = extract_grid(s6.get_model(), cells, idx, var)
                t = time.time()
                B, qgrid = self.confirm_period(grid6, maxc=5,
                                               min_pairs=6)
                self.phase["confirmP"] += time.time() - t
                if B is not None:
                    return ("periodic", B, qgrid)
        t = time.time()
        sat, _ = box_sat((5, 5, 5), self.bad, conf_budget=BOX5_CONF)
        self.phase["box5"] += time.time() - t
        if sat is False:
            return ("untileable5", None, None)
        if sat is None:
            unresolved.append(("box5", None))
        if suspicious or unresolved:
            # bigger-box tileability first: at looser matchings (K<3) a
            # non-tiler can pass 5^3 yet fail 8^3 -- cheap, decisive UNSAT
            # that the 5^3 check (which even times out here) never sees.
            t = time.time()
            s8, _ = box_sat((8, 8, 8), self.bad, conf_budget=BOX8_CONF)
            self.phase["box8"] += time.time() - t
            if s8 is False:
                return ("untileable8", None, None)
            # decisive backstop: brute-sweep every lattice class <= 32
            # before conceding a suspicious verdict
            t = time.time()
            B, qgrid = lattice_sweep(self.bad, self.selfbad)
            self.phase["sweep"] += time.time() - t
            if B is not None:
                return ("periodic", B, qgrid)
            info = {"suspicious": [list(w) for w in suspicious],
                    "unresolved": [[tag, list(w) if w else None]
                                   for tag, w in unresolved]}
            return ("suspicious", info, None)
        return ("survivor", None, None)

# ---------------------------------------------------------- synthesizer

SYNTH_DIMS = (4, 4, 4)

class Synth:
    def __init__(self, balance=True, balance_enc=EncType.seqcounter):
        self.balance_enc = balance_enc
        self.next_var = NPTS + 1
        cells = list(itertools.product(*[range(d) for d in SYNTH_DIMS]))
        self.cell_idx = {c: i for i, c in enumerate(cells)}
        self.xbase = self.next_var
        self.next_var += len(cells) * 24
        self.aux = {}
        self.cnf = [[1]]                       # H_0 = True
        self.balance = balance
        self._build(cells)
        self.solver = Glucose3()
        self.solver.append_formula(self.cnf)
        self.n_base = len(self.cnf)

    def xvar(self, ci, o):
        return self.xbase + ci * 24 + o

    def evar(self, a, b):
        key = (a, b) if a < b else (b, a)
        v = self.aux.get(key)
        if v is None:
            v = self.next_var
            self.next_var += 1
            self.aux[key] = v
            Ha, Hb = key[0] + 1, key[1] + 1
            defs = [[-v, Ha, Hb], [-v, -Ha, -Hb],
                    [v, Ha, -Hb], [v, -Ha, Hb]]
            if hasattr(self, "solver"):
                for cl in defs:
                    self.solver.add_clause(cl)
            else:
                self.cnf.extend(defs)
        return v

    def _build(self, cells):
        # Lemma A (balance law): any space-tiler has height-sum zero on
        # each rotation orbit of surface points. Sound pruning: enforce
        # exactly half bumps per orbit.
        if self.balance:
            orbits = []
            seen = set()
            for i in range(NPTS):
                if i in seen:
                    continue
                orb = {PERM[o][i] for o in range(24)}
                seen |= orb
                orbits.append(sorted(orb))
            for pairs in IFACE_PAIRS:              # matching respects orbits
                for a, b in pairs:
                    oa = next(o for o in orbits if a in o)
                    assert b in oa
            for orb in orbits:
                assert len(orb) % 2 == 0
                enc = CardEnc.equals(lits=[i + 1 for i in orb],
                                     bound=len(orb) // 2,
                                     top_id=self.next_var - 1,
                                     encoding=self.balance_enc)
                self.next_var = enc.nv + 1
                self.cnf.extend(enc.clauses)
        for c in cells:
            ci = self.cell_idx[c]
            self.cnf.append([self.xvar(ci, o) for o in range(24)])
            for o1 in range(24):
                for o2 in range(o1 + 1, 24):
                    self.cnf.append([-self.xvar(ci, o1),
                                     -self.xvar(ci, o2)])
        for c in cells:
            ci = self.cell_idx[c]
            for ax in range(3):
                nc = list(c)
                nc[ax] += 1
                if nc[ax] == SYNTH_DIMS[ax]:
                    continue
                nci = self.cell_idx[tuple(nc)]
                for o1 in range(24):
                    x1 = self.xvar(ci, o1)
                    for o2 in range(24):
                        x2 = self.xvar(nci, o2)
                        es = set()
                        dead = False
                        for a, b in PAIRS[ax][o1][o2]:
                            if a == b:
                                dead = True
                                break
                            es.add(self.evar(a, b))
                        if dead:
                            self.cnf.append([-x1, -x2])
                        else:
                            for e in es:
                                self.cnf.append([-x1, -x2, e])

    def propose(self, deadline=None):
        # escalate in budget slices so a hard-but-solvable proposal
        # keeps the run alive; give up only at the wall deadline
        while True:
            self.solver.conf_budget(500_000)
            r = self.solver.solve_limited()
            if r is not None:
                break
            if deadline is not None and time.time() > deadline:
                return "STALL"
        if not r:
            return None
        model = self.solver.get_model()
        pos = set(v for v in model if v > 0)
        return tuple(1 if (i + 1) in pos else -1 for i in range(NPTS))

    def block_pattern(self, pair_set, seen):
        added = 0
        for g in range(24):
            pg = PERM[g]
            Sg = frozenset((min(pg[a], pg[b]), max(pg[a], pg[b]))
                           for a, b in pair_set)
            if Sg in seen:
                continue
            seen.add(Sg)
            self.solver.add_clause([-self.evar(a, b) for a, b in Sg])
            added += 1
        return added

    def block_point(self, dec):
        # the global flip -dec induces the SAME compat tables
        # (complementarity is preserved by negating both sides), so
        # block it too -- it realizes exactly the same tilings.
        for g in range(24):
            for s in (1, -1):
                dg = [s * dec[PERMINV[g][j]] for j in range(NPTS)]
                self.solver.add_clause(
                    [-(i + 1) if dg[i] == 1 else (i + 1)
                     for i in range(NPTS)])

# ---------------------------------------------------------------- tests

def self_test():
    rng = np.random.default_rng(5)
    dec = tuple(int(x) for x in rng.choice((-1, 1), NPTS))
    compat = compat_tables(placed_vectors(dec))
    assert check_equivariance(compat)
    print(f"[test] equivariance at K={K}: OK")

    if K != 3:
        return  # the stacker-control test below is tuned to K=3 coordinates

    dec_p = []
    for p in PTS:
        ax = max(range(3), key=lambda i: abs(p[i]))
        dec_p.append(1 if p[ax] > 0 else -1)
    # break rotational symmetry while preserving identity self-stacking:
    # flip matched pairs (+x face point, -x face point at same tangential
    # position) -- the x-interface stays complementary.
    for a, b in [(2, 0), (-2, 2), (0, -2)]:
        if orbit_size(placed_vectors(tuple(dec_p))) == 24:
            break
        for val in (K, -K):
            i = PT_INDEX[face_point(0, val, a, b)]
            dec_p[i] = -dec_p[i]
    assert orbit_size(placed_vectors(tuple(dec_p))) == 24
    V = Verifier(tuple(dec_p))
    verdict, B, qgrid = V.verdict()
    V.close()
    assert verdict == "periodic", verdict
    idx = B[0][0] * B[1][1] * B[2][2]
    print(f"[test] stacker control: period-finder verdict 'periodic', "
          f"lattice index {idx}: OK")

# ---------------------------------------------------------------- loop

PATTERN_FILE = f"arena2_patterns{KSUF}.json"

def save_blocks(patterns, points):
    # atomic: a kill mid-write must never truncate the library
    tmp = PATTERN_FILE + ".tmp"
    with open(tmp, "w") as f:
        json.dump({"patterns": [sorted(map(list, S)) for S in patterns],
                   "points": [list(d) for d in points]}, f)
    os.replace(tmp, PATTERN_FILE)

def load_blocks(syn, seen_patterns):
    """Load pattern/point blocks from previous runs. Pattern blocks
    are universally sound (each came from a confirmed periodic tiling)
    but are NOT preloaded into the synthesizer: ~800 wide clauses over
    XOR-defined e-vars on a cold solver make proposals brutally hard
    (measured: instant -> 400k+ conflicts). Instead they become a
    conjugate-expanded LIBRARY checked in Python per proposal -- a hit
    kills the candidate instantly and only then teaches the solver
    that one block (lazy clause loading). Point blocks are few and
    narrow; those stay eager."""
    try:
        with open(PATTERN_FILE) as f:
            data = json.load(f)
    except FileNotFoundError:
        return [], [], [], set()
    except json.JSONDecodeError as e:
        # never silently start with an empty library -- that would
        # quietly discard every past kill
        raise RuntimeError(f"{PATTERN_FILE} is corrupt ({e}); restore "
                           f"it or move it aside deliberately")
    patterns = [frozenset((min(a, b), max(a, b)) for a, b in plist)
                for plist in data.get("patterns", [])]
    points = [tuple(d) for d in data.get("points", [])]
    library = []
    libseen = set()
    for S in patterns:
        for g in range(24):
            pg = PERM[g]
            Sg = frozenset((min(pg[a], pg[b]), max(pg[a], pg[b]))
                           for a, b in S)
            if Sg not in libseen:
                libseen.add(Sg)
                library.append(Sg)
    for d in points:
        syn.block_point(d)
    print(f"  library: {len(patterns)} saved patterns "
          f"({len(library)} conjugates), {len(points)} point blocks "
          f"from {PATTERN_FILE}")
    return patterns, points, library, libseen

def run(time_budget):
    t0 = time.time()
    print(f"building synthesizer {SYNTH_DIMS}, K={K} ...")
    syn = Synth()
    print(f"  base clauses {syn.n_base}, vars {syn.next_var}, "
          f"build {time.time()-t0:.0f}s")
    kills = Counter()
    index_hist = Counter()
    seen_patterns = set()
    survivors, sus = [], []
    patterns, points, library, libseen = load_blocks(syn, seen_patterns)
    logf = open(f"arena2_progress{KSUF}.jsonl", "a")
    it = 0
    while time.time() - t0 < time_budget:
        it += 1
        dec = syn.propose(deadline=t0 + time_budget)
        if dec == "STALL":
            print(f"\nsynthesizer conflict budget exceeded at iter {it}")
            save_blocks(patterns, points)
            return ("SYNTH_BUDGET", kills, index_hist, survivors, sus,
                    it - 1)
        if dec is None:
            print()
            print("=" * 60)
            print("SYNTHESIZER UNSAT: arena 2 closed -- every K=3 binary")
            print("cube tiling a 4^3 box realizes a blocked periodic")
            print("pattern (or is a logged point-blocked candidate).")
            print("=" * 60)
            save_blocks(patterns, points)
            return "UNSAT", kills, index_hist, survivors, sus, it - 1
        # library check: a proposal realizing a saved pattern is dead --
        # kill instantly and teach the solver just that one block
        hitS = next((S for S in library
                     if all(dec[a] != dec[b] for a, b in S)), None)
        if hitS is not None:
            syn.block_pattern(hitS, seen_patterns)
            kills["cached"] += 1
            logf.write(json.dumps({"it": it, "verdict": "cached"}) + "\n")
            logf.flush()
            if it % 10 == 0:
                print(f"  iter {it}: {time.time()-t0:.0f}s "
                      f"kills={dict(kills)} indices={dict(index_hist)}")
            if it % 25 == 0:
                save_blocks(patterns, points)
            continue
        t_it = time.time()
        V = Verifier(dec)
        verdict, info, qgrid = V.verdict()
        t_it = time.time() - t_it
        if t_it > 30:
            ph = {k: round(x, 1) for k, x in V.phase.items()}
            print(f"  iter {it}: SLOW verdict={verdict} {t_it:.0f}s "
                  f"phases={ph} dec={dec}")
        rec = {"it": it, "verdict": verdict}
        if verdict == "periodic":
            B = info
            idx = B[0][0] * B[1][1] * B[2][2]
            index_hist[idx] += 1
            rec["index"] = idx
            S = pattern_pairs_lattice(B, qgrid)
            if syn.block_pattern(S, seen_patterns) and S not in libseen:
                patterns.append(S)        # don't re-save loaded patterns
        elif verdict == "suspicious":
            print(f"  iter {it}: SUSPICIOUS {info} dec={dec}")
            sus.append((dec, info))
            rec["dec"] = list(dec)
            syn.block_point(dec)
            points.append(dec)
        elif verdict == "survivor":
            dverdict, dB, dqgrid = deep_check(V.bad, V.selfbad)
            verdict = dverdict
            rec["verdict"] = verdict
            if dverdict == "periodic-deep":
                idx = dB[0][0] * dB[1][1] * dB[2][2]
                index_hist[idx] += 1
                rec["index"] = idx
                S = pattern_pairs_lattice(dB, dqgrid)
                if syn.block_pattern(S, seen_patterns) \
                        and S not in libseen:
                    patterns.append(S)
            elif dverdict == "DEEP-SURVIVOR":
                print(f"  iter {it}: *** DEEP SURVIVOR *** dec={dec}")
                survivors.append(dec)
                rec["dec"] = list(dec)
                syn.block_point(dec)
                points.append(dec)
            else:
                print(f"  iter {it}: survivor -> {dverdict} dec={dec}")
                sus.append((dec, dverdict))
                rec["dec"] = list(dec)
                syn.block_point(dec)
                points.append(dec)
        else:
            syn.block_point(dec)
            points.append(dec)
        kills[verdict] += 1
        logf.write(json.dumps(rec) + "\n")
        logf.flush()
        V.close()
        if it % 25 == 0:
            save_blocks(patterns, points)

        if it <= 3:
            assum = [(i + 1) if dec[i] == 1 else -(i + 1)
                     for i in range(NPTS)]
            assert not syn.solver.solve(assumptions=assum)

        if it % 10 == 0:
            print(f"  iter {it}: {time.time()-t0:.0f}s "
                  f"kills={dict(kills)} indices={dict(index_hist)}")
    print(f"\nbudget reached: {it} iterations, {time.time()-t0:.0f}s")
    save_blocks(patterns, points)
    return "BUDGET", kills, index_hist, survivors, sus, it

if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "test":
        self_test()
        sys.exit(0)
    budget = float(sys.argv[1]) if len(sys.argv) > 1 else 150.0
    self_test()
    status, kills, idxh, survivors, sus, iters = run(budget)
    print()
    print("status:", status, "| iterations:", iters)
    print("verdicts:", dict(kills))
    print("confirmed period indices:", dict(sorted(idxh.items())))
    print("survivors:", len(survivors), "suspicious:", len(sus))
    with open(f"arena2_log{KSUF}.json", "w") as f:
        json.dump({"status": status, "iters": iters,
                   "kills": {str(k): v for k, v in kills.items()},
                   "indices": {str(k): v for k, v in idxh.items()},
                   "survivors": [list(d) for d in survivors],
                   "suspicious": [[list(d), info] for d, info in sus]},
                  f)
