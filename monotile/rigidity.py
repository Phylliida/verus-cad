"""
Rigidity-layer existence experiments (positive-construction Layer 1).

Question: does a +/-1 sub-decoration r on ONE orbit channel exist such
that the induced channel-compatibility has prescribed block structure?

Spec v1 (capacity probe, H = {id}): compat = exactly the diagonal
  (self-stack allowed in every axis for every orientation, every mixed
  pair forbidden in every axis). Note: useless for an einstein on its
  own (forces constant fields), but calibrates channel capacity.

Spec v2 (the useful lock, H = stab(z-axis), |H| = 8): adjacency allowed
  only within left cosets o1 H = o2 H (tiles must agree on which body
  axis carries the z-frame); cross-coset forbidden in every axis;
  viability: identity self-stacks in every axis. Within-coset entries
  left free. Plus the Balance Law (12 bumps / 12 dents) so the layer is
  embeddable in a space-tiler.
"""
import itertools
import numpy as np
from pysat.solvers import Glucose3
from pysat.card import CardEnc, EncType

from arena2 import PTS, ROTS, PERM, PERMINV, PAIRS, placed_vectors

def point_class(p):
    ax = max(range(3), key=lambda i: abs(p[i]))
    tang = sorted(abs(p[i]) for i in range(3) if i != ax)
    return {(2, 2): "corner", (0, 2): "edge", (0, 0): "center"}[tuple(tang)]

CH = {}
for i, p in enumerate(PTS):
    CH.setdefault(point_class(p), []).append(i)

H_AXIS = [o for o in range(24)
          if ROTS[o][0][2] == 0 and ROTS[o][1][2] == 0]
assert len(H_AXIS) == 8
HSET = set(H_AXIS)
ROT_KEY = {tuple(M.flatten()): i for i, M in enumerate(ROTS)}
INV = [ROT_KEY[tuple(np.linalg.inv(ROTS[o]).round().astype(int).flatten())]
       for o in range(24)]

def coset(o):
    """Which body axis carries the z-frame for orientation o."""
    col = [ROTS[o][r][2] for r in range(3)]
    return max(range(3), key=lambda r: abs(col[r]))

def channel_pairs(ax, o1, o2, channel):
    chset = set(CH[channel])
    return [(a, b) for a, b in PAIRS[ax][o1][o2] if a in chset]

def solve_spec(channel, spec):
    idxs = CH[channel]
    n = len(idxs)
    var_of = {g: i + 1 for i, g in enumerate(idxs)}     # channel bit vars
    next_var = n + 1
    aux = {}
    cnf = []

    def evar(a, b):
        nonlocal next_var
        key = (min(a, b), max(a, b))
        v = aux.get(key)
        if v is None:
            v = next_var
            next_var += 1
            aux[key] = v
            Ha, Hb = var_of[key[0]], var_of[key[1]]
            cnf.extend([[-v, Ha, Hb], [-v, -Ha, -Hb],
                        [v, Ha, -Hb], [v, -Ha, Hb]])
        return v

    def require_compat(ax, o1, o2):
        for a, b in channel_pairs(ax, o1, o2, channel):
            if a == b:
                return False                      # impossible
            cnf.append([evar(a, b)])
        return True

    def forbid_compat(ax, o1, o2):
        cl = []
        for a, b in channel_pairs(ax, o1, o2, channel):
            if a == b:
                return                            # already impossible
            cl.append(-evar(a, b))
        cnf.append(cl)

    ok = True
    for ax in range(3):
        for o1 in range(24):
            for o2 in range(24):
                same_coset = (ROT_KEY[tuple(
                    (ROTS[INV[o2]] @ ROTS[o1]).flatten())] in HSET) \
                    if spec == "v2" else (o1 == o2)
                if spec == "v1":
                    if o1 == o2:
                        ok &= require_compat(ax, o1, o2)
                    else:
                        forbid_compat(ax, o1, o2)
                else:                              # v2
                    if not same_coset:
                        forbid_compat(ax, o1, o2)
                    elif o1 == o2 == 0:
                        ok &= require_compat(ax, o1, o2)
    if not ok:
        return None
    # Balance Law
    enc = CardEnc.equals(lits=list(range(1, n + 1)), bound=n // 2,
                         top_id=next_var - 1,
                         encoding=EncType.seqcounter)
    cnf.extend(enc.clauses)
    with Glucose3(bootstrap_with=cnf) as s:
        if not s.solve():
            return None
        model = set(v for v in s.get_model() if v > 0)
    r = {g: (1 if var_of[g] in model else -1) for g in idxs}
    return r

def channel_compat(r, channel):
    compat = np.zeros((3, 24, 24), dtype=bool)
    for ax in range(3):
        for o1 in range(24):
            for o2 in range(24):
                compat[ax, o1, o2] = all(
                    a != b and r[a] + r[b] == 0
                    for a, b in channel_pairs(ax, o1, o2, channel))
    return compat

def verify(r, channel, spec):
    c = channel_compat(r, channel)
    for ax in range(3):
        for o1 in range(24):
            for o2 in range(24):
                allowed = bool(c[ax, o1, o2])
                if spec == "v1":
                    want_forbidden = (o1 != o2)
                else:
                    want_forbidden = (ROT_KEY[tuple(
                        (ROTS[INV[o2]] @ ROTS[o1]).flatten())]
                        not in HSET)
                if want_forbidden and allowed:
                    return False, (ax, o1, o2)
    # viability: identity self-stacks
    if not all(c[ax, 0, 0] for ax in range(3)):
        return False, "no-self-stack"
    return True, None

if __name__ == "__main__":
    for channel in ("corner", "edge"):
        for spec in ("v1", "v2"):
            r = solve_spec(channel, spec)
            if r is None:
                print(f"{channel:6s} {spec}: UNSAT -- no such layer")
                continue
            ok, w = verify(r, channel, spec)
            n_allowed = int(channel_compat(r, channel).sum())
            print(f"{channel:6s} {spec}: SAT, verified={ok}, "
                  f"allowed pairs total={n_allowed}/1728")
            if spec == "v2" and ok:
                bits = [r[g] for g in CH[channel]]
                print(f"        lock found! r = {bits}")
