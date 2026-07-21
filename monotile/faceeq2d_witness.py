"""Witness search for predicted-but-uncollected relations (anyk-08 2D).

For each achievable-per-characterization assignment whose canonical mask is
NOT in the K<=5 collected union, search for a witness decoration at the
current K by sampling class representatives consistent with the closure's
forced symmetries, then verifying the induced relation is EXACTLY the
assignment's mask.

Run:  ARENA2D_K=6 ./runpy.sh faceeq2d_witness.py
"""
import json
import random

from arena2d import K, NPTS, placed_vectors, compat_tables
from relations2d import rel_mask, rel_canon
from faceeq2d import (EQS, EQ_IDX, EQ_OF, TRIPLES, NEDGE, EDGE_OF, eq_norm,
                      GainClasses, assignment_status)


def mask_of_held(held):
    m = 0
    for tr in TRIPLES:
        if EQ_IDX[eq_norm(EQ_OF[tr])] in held:
            ax, o1, o2 = tr
            m |= 1 << (ax * 16 + o1 * 4 + o2)
    return m


def apply_gain(g, F):
    """(m, s) . F : mirror then negate."""
    m, s = g
    G = F[::-1] if m else list(F)
    return [-x for x in G] if s else G


def dec_from_reps(uf, reps):
    """Build a decoration from root representatives via the gains."""
    F = [None] * NEDGE
    for e in range(NEDGE):
        r, g = uf.find(e)
        F[e] = apply_gain(g, reps[r])
    dec = [0] * NPTS
    for i in range(NPTS):
        e, s = EDGE_OF[i]
        dec[i] = F[e][s]
    return tuple(dec)


def sample_rep(H, rng):
    """Random function [K] -> {+-1} satisfying every self-gain in H."""
    F = [rng.choice((1, -1)) for _ in range(K)]
    if (1, 0) in H:                      # F = F o mirror
        for t in range(K):
            F[K - 1 - t] = F[t] if t <= K - 1 - t else F[K - 1 - t]
        for t in range(K // 2):
            F[K - 1 - t] = F[t]
    if (1, 1) in H:                      # F = -F o mirror (K even)
        assert K % 2 == 0
        for t in range(K // 2):
            F[K - 1 - t] = -F[t]
    if (1, 0) in H and (1, 1) in H:
        return None                      # forces F = -F
    return F


def find_witness(held, tries=20000, seed=11):
    uf = GainClasses(NEDGE)
    for ei in held:
        g, h, s = EQS[ei]
        assert uf.union(g, h, (s, 1))
    roots = sorted({uf.find(e)[0] for e in range(NEDGE)})
    target = mask_of_held(held)
    rng = random.Random(seed)
    for _ in range(tries):
        reps = {}
        ok = True
        for r in roots:
            F = sample_rep(uf.H[r], rng)
            if F is None:
                ok = False
                break
            reps[r] = F
        if not ok:
            return None
        dec = dec_from_reps(uf, reps)
        if rel_mask(compat_tables(placed_vectors(dec))) == target:
            return dec
    return None


def main():
    collected = set()
    for k in (1, 2, 3, 4, 5):
        collected |= {int(x) for x in
                      json.load(open(f"relations2d_K{k}.json"))["relations"]}
    # regenerate the predicted assignments, keep extras only
    extras = {}                      # canonical mask -> one held set
    for bits in range(1 << len(EQS)):
        held = frozenset(i for i in range(len(EQS)) if (bits >> i) & 1)
        st = assignment_status(held)
        if st == "unsat":
            continue
        if st == "even-only" and K % 2 == 1:
            continue
        cm = rel_canon(mask_of_held(held))
        if cm not in collected:
            extras.setdefault(cm, held)
    print(f"K={K}: {len(extras)} predicted-but-uncollected canonical "
          f"relations to witness", flush=True)
    found, missing = 0, []
    for cm, held in sorted(extras.items()):
        w = find_witness(held)
        if w is not None:
            found += 1
            print(f"  {cm}: WITNESS at K={K}: {list(w)}", flush=True)
        else:
            missing.append(cm)
            print(f"  {cm}: no witness in sample budget "
                  f"(held={sorted(held)})", flush=True)
    print(f"witnessed {found}/{len(extras)}; missing: {len(missing)}",
          flush=True)


if __name__ == "__main__":
    main()
