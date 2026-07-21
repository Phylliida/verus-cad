"""anyk-08/12 dress rehearsal, step 2: the face-equation characterization.

Derives, from the geometry alone, the finite equation structure behind
Compat: each triple (ax, o1, o2) corresponds to one face equation

    E(g, h, sigma):   F_g = not (F_h o sigma)        sigma in {id, mirror}

between two of the 4 base edge-functions F_e : TANG -> {+-1}. Then:

  1. RECONSTRUCTION VALIDATION (the twist-bookkeeping test): for random
     decorations, Compat computed via the equations must equal
     arena2d.compat_tables exactly. This is where an error in the
     orientation-reversing identifications would show up.

  2. ABSTRACT ACHIEVABILITY: enumerate which equation-assignments are
     satisfiable by ANY functions at ANY K, via gain-graph closure over the
     group Z2(mirror) x Z2(negation) on the 4 edge nodes:
       - held equations are edges with gain (sigma, neg);
       - closure conflicts: a cycle forcing F = -F (unsat at every K) or
         F = -F o mirror (unsat exactly when K odd: fixed slot t=0);
       - non-held equations must not be implied by the closure;
       - whatever is not forced is realizable at K0 (verified by brute
         search for a witness decoration at small K rather than assumed).
     Predicted achievable relation set must equal the collected
     relations2d union (= R4, 99 relations).

Run:  ARENA2D_K=4 ./runpy.sh faceeq2d.py
"""
import itertools
import json
import random

import numpy as np

from arena2d import (K, NPTS, NORI, M, TANG, DIRS, PTS, PT_IDX, PERM,
                     PERMINV, placed_vectors, compat_tables)
from relations2d import rel_mask, rel_canon

NEDGE = 4
# base edge and slot of every base point index: point i on edge e at slot s
EDGE_OF = {}
for e, d in enumerate(DIRS):
    for s, t in enumerate(TANG):
        EDGE_OF[PT_IDX[(M * d[0] - t * d[1], M * d[1] + t * d[0])]] = (e, s)


def derive_equation(ax, o1, o2):
    """The (g, h, sigma) equation equivalent to Compat(ax, o1, o2).

    Compat(ax,o1,o2)  <=>  for all world tangentials t:
        dec[PERMINV[o1][idx(+face pt t)]] + dec[PERMINV[o2][idx(-face pt t)]] == 0
    Both sides trace out an edge each (g for o1, h for o2) and a slot map
    s_h = phi(s_g); phi must be +-identity on slots (sigma).
    """
    g = h = None
    slot_map = {}
    for t in TANG:
        if ax == 0:
            p_plus, p_minus = PT_IDX[(M, t)], PT_IDX[(-M, t)]
        else:
            p_plus, p_minus = PT_IDX[(t, M)], PT_IDX[(t, -M)]
        i1 = PERMINV[o1][p_plus]
        i2 = PERMINV[o2][p_minus]
        e1, s1 = EDGE_OF[i1]
        e2, s2 = EDGE_OF[i2]
        g = e1 if g is None else g
        h = e2 if h is None else h
        assert e1 == g and e2 == h, "face points scattered across edges"
        slot_map[s1] = s2
    ident = all(slot_map[s] == s for s in range(K))
    mirror = all(slot_map[s] == K - 1 - s for s in range(K))
    assert ident or mirror, f"slot map not +-identity: {slot_map}"
    sigma = 0 if ident else 1
    return (g, h, sigma)


TRIPLES = [(ax, o1, o2) for ax in range(2)
           for o1 in range(NORI) for o2 in range(NORI)]
EQ_OF = {tr: derive_equation(*tr) for tr in TRIPLES}


def eq_norm(e):
    """E(g,h,sigma) and E(h,g,sigma) are the same equation (mirror is an
    involution and negation is symmetric)."""
    g, h, s = e
    return (min(g, h), max(g, h), s)


EQS = sorted({eq_norm(e) for e in EQ_OF.values()})
EQ_IDX = {e: i for i, e in enumerate(EQS)}


def compat_via_equations(dec):
    """Reconstruct the compat table from the equations (validation)."""
    F = [[dec[i] for i, (e2, s) in sorted(
        ((i, EDGE_OF[i]) for i in range(NPTS) if EDGE_OF[i][0] == e),
        key=lambda kv: kv[1][1])] for e in range(NEDGE)]
    # F[e][s] = dec value at edge e slot s
    def holds(eq):
        g, h, s = eq
        if s == 0:
            return all(F[g][t] == -F[h][t] for t in range(K))
        return all(F[g][t] == -F[h][K - 1 - t] for t in range(K))
    hv = {e: holds(e) for e in EQS}
    compat = np.zeros((2, NORI, NORI), dtype=bool)
    for tr in TRIPLES:
        compat[tr] = hv[eq_norm(EQ_OF[tr])]
    return compat


def validate_reconstruction(n=500, seed=7):
    rng = random.Random(seed)
    for _ in range(n):
        dec = tuple(rng.choice((1, -1)) for _ in range(NPTS))
        ok = (compat_via_equations(dec) ==
              compat_tables(placed_vectors(dec))).all()
        assert ok, f"reconstruction mismatch: {dec}"
    print(f"reconstruction OK on {n} random decorations (K={K}, "
          f"{len(EQS)} distinct equations: {EQS})", flush=True)


# ---- abstract achievability via gain-graph closure ----------------------
# Gain group G = Z2(mirror) x Z2(sign): elements (m, s), composition adds.
# Held equation E(g,h,sigma): F_g = -(F_h o sigma) is an edge g--h with gain
# (sigma, 1) [sign 1 = negated]. Classes carry a self-gain subgroup H:
#   (0,1) in H: UNSAT at every K (F = -F)
#   (1,1) in H: F = -F o mirror  -- needs K even (odd K has fixed slot t=0)
#   (1,0) in H: F = F o mirror   -- fine at any K (symmetric functions)
# An assignment (held set) is ACHIEVABLE iff:
#   - the closure has no (0,1) self-gain, and
#   - no NON-held equation is implied: E(g,h,s) is implied iff g,h are in
#     the same class and (s,1) lies in the coset gain(g->h) . H.
# Sufficiency of non-implication (existence of witness functions making
# held hold exactly): generic choice of class representatives; at K=4 a
# union bound over the <=10 possible accidental equations vs 2^4 choices
# per representative closes it (formal proof deferred to the Lean pass;
# here the prediction is CHECKED against the brute-forced relation sets).


def gain_mul(a, b):
    return ((a[0] + b[0]) % 2, (a[1] + b[1]) % 2)


class GainClasses:
    """Tiny gain-graph closure over Z2 x Z2 on NEDGE nodes."""

    def __init__(self, n):
        self.parent = list(range(n))
        self.gain = [(0, 0)] * n          # gain node -> parent
        self.H = [set() for _ in range(n)]  # root -> self-gain subgroup\{e}

    def find(self, x):
        if self.parent[x] == x:
            return x, (0, 0)
        r, gp = self.find(self.parent[x])
        g = gain_mul(self.gain[x], gp)
        self.parent[x], self.gain[x] = r, g
        return r, g

    def add_self(self, r, h):
        if h == (0, 0):
            return True
        S = self.H[r]
        S.add(h)
        changed = True
        while changed:
            changed = False
            for a in list(S):
                for b in list(S):
                    c = gain_mul(a, b)
                    if c != (0, 0) and c not in S:
                        S.add(c)
                        changed = True
        return (0, 1) not in S

    def union(self, a, b, g):
        """Impose F_a = g . F_b. False on K-independent contradiction."""
        ra, ga = self.find(a)
        rb, gb = self.find(b)
        if ra == rb:
            return self.add_self(ra, gain_mul(ga, gain_mul(g, gb)))
        self.parent[ra] = rb
        self.gain[ra] = gain_mul(ga, gain_mul(g, gb))
        S = self.H[ra]
        self.H[ra] = set()
        return all(self.add_self(rb, h) for h in S)

    def implied(self, a, b, g):
        """Is F_a = g . F_b forced by the closure?"""
        ra, ga = self.find(a)
        rb, gb = self.find(b)
        if ra != rb:
            return False
        h = gain_mul(ga, gain_mul(g, gb))
        return h == (0, 0) or h in self.H[ra]

    def parity(self):
        roots = {self.find(x)[0] for x in range(len(self.parent))}
        return ("even-only"
                if any((1, 1) in self.H[r] for r in roots) else "any")


def assignment_status(held):
    """'unsat' | 'even-only' | 'any' -- with the non-held implication
    filter applied (an assignment whose closure forces a non-held equation
    is not achievable as an EXACT relation)."""
    uf = GainClasses(NEDGE)
    for ei in held:
        g, h, s = EQS[ei]
        if not uf.union(g, h, (s, 1)):
            return "unsat"
    for ei in range(len(EQS)):
        if ei in held:
            continue
        g, h, s = EQS[ei]
        if uf.implied(g, h, (s, 1)):
            return "unsat"
    return uf.parity()


def predicted_relations():
    """All achievable relations per the characterization, as canonical
    masks: (achievable at odd and even K, achievable at even K only)."""
    def mask_of_held(held):
        m = 0
        for tr in TRIPLES:
            if EQ_IDX[eq_norm(EQ_OF[tr])] in held:
                ax, o1, o2 = tr
                m |= 1 << (ax * 16 + o1 * 4 + o2)
        return m

    sat_any, sat_even = set(), set()
    for bits in range(1 << len(EQS)):
        held = frozenset(i for i in range(len(EQS)) if (bits >> i) & 1)
        st = assignment_status(held)
        if st == "unsat":
            continue
        (sat_even if st == "even-only" else sat_any).add(held)
    print(f"achievable assignments: {len(sat_any)} any-K, "
          f"{len(sat_even)} even-only (of {1 << len(EQS)})", flush=True)
    return ({rel_canon(mask_of_held(h)) for h in sat_any},
            {rel_canon(mask_of_held(h)) for h in sat_even})


if __name__ == "__main__":
    validate_reconstruction()
    pred_any, pred_even = predicted_relations()
    pred = pred_any | pred_even
    R = {k: {int(x) for x in
             json.load(open(f"relations2d_K{k}.json"))["relations"]}
         for k in (1, 2, 3, 4, 5)}
    collected = set().union(*R.values())
    odd_collected = R[1] | R[3] | R[5]
    print(f"predicted achievable: {len(pred)} "
          f"({len(pred_any)} any-K + {len(pred_even - pred_any)} even-only)",
          flush=True)
    print(f"collected union (K=1..5): {len(collected)}", flush=True)
    print(f"PREDICTED == COLLECTED: {pred == collected}", flush=True)
    print(f"PREDICTED-any == ODD-collected (R1|R3|R5): "
          f"{pred_any == odd_collected}", flush=True)
    if pred != collected:
        print(f"  predicted - collected: {sorted(pred - collected)[:5]}")
        print(f"  collected - predicted: {sorted(collected - pred)[:5]}")
