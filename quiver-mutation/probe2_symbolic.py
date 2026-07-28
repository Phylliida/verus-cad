#!/usr/bin/env python3
"""Probe 2: symbolic-in-c ratchet search (gadget CEGIS, stage 1: exhaustive sweep).

Entries are polynomials in a symbolic counter c; signs are taken for c >> 0
(sign of leading coefficient), so mutation is exact piecewise-polynomial and
every conclusion is uniform "for all sufficiently large c".

RATCHET DETECTOR (self-similarity scan): after BFS-enumerating the island of a
template T(c) (with degree/coefficient/state caps), look for ANY pair of island
states S1, S2 with S2 = g * pi(S1 with c -> c+delta) for a vertex permutation pi
and global sign g (both commute with mutation). Such a pair yields a mutation
word implementing a uniform counter climb at S1 — much stronger than checking
only T(c) -> T(c+delta).

Sweep: all rank-4 templates with counter at b_02, b_13 = 0 (Pfaffian-forced),
control entries (b01,b03,b12,b32) in {-2..2}, canonicalized under the symmetry
group fixing the counter. Then rank-5 extensions of three motivated bases
(Pfaffian vanishes identically at odd rank -> that obstruction disappears).

Any hit is verified by concrete integer mutation at c ~ 1e8 (large enough that
leading coefficients dominate under the coefficient cap).
"""
import sys, time, json
from collections import deque
from itertools import product, permutations
from math import comb

DEGCAP, COEFCAP = 4, 10**7

# ---------------- polynomial helpers (coeffs low->high) ----------------
def pn(t):
    t = list(t)
    while t and t[-1] == 0: t.pop()
    return tuple(t)

def padd(a, b):
    if len(a) < len(b): a, b = b, a
    return pn(tuple((x + (b[i] if i < len(b) else 0)) for i, x in enumerate(a)))

def pneg(a): return tuple(-x for x in a)

def pmul(a, b):
    if not a or not b: return ()
    r = [0]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i+j] += x*y
    return pn(r)

def psign(a): return 0 if not a else (1 if a[-1] > 0 else -1)

def pshift(a, d):
    """c -> c+d"""
    r = [0]*len(a)
    for i, ai in enumerate(a):
        if ai:
            for j in range(i+1):
                r[j] += ai * comb(i, j) * d**(i-j)
    return pn(r)

def peval(a, cval):
    v = 0
    for x in reversed(a): v = v*cval + x
    return v

def pabs_canon(a):
    """representative of {a, -a}, for perm/sign-invariant hashing"""
    na = pneg(a)
    return a if a >= na else na

# ---------------- mutation ----------------
def mutate_sym(B, k):
    n = len(B)
    Bp = [row[:] for row in B]
    for i in range(n):
        Bp[i][k] = pneg(B[i][k]); Bp[k][i] = pneg(B[k][i])
    others = [i for i in range(n) if i != k]
    for ai in range(len(others)):
        for aj in range(ai+1, len(others)):
            i, j = others[ai], others[aj]
            x, y = B[i][k], B[k][j]
            sx, sy = psign(x), psign(y)
            if sx != 0 and sx == sy:
                corr = pmul(x, y)
                if sx < 0: corr = pneg(corr)
                nb = padd(B[i][j], corr)
                Bp[i][j] = nb; Bp[j][i] = pneg(nb)
    return Bp

def mutate_int(B, k):
    n = len(B)
    Bp = [[0]*n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if i == k or j == k: Bp[i][j] = -B[i][j]
            else: Bp[i][j] = B[i][j] + (abs(B[i][k])*B[k][j] + B[i][k]*abs(B[k][j]))//2
    return Bp

def key(B):
    n = len(B)
    return tuple(B[i][j] for i in range(n) for j in range(i+1, n))

def transform(B, pi, g):
    n = len(B)
    return [[(pneg(B[pi[i]][pi[j]]) if g < 0 else B[pi[i]][pi[j]]) for j in range(n)] for i in range(n)]

def inv_hash(B):
    """invariant under vertex permutation and global sign"""
    n = len(B)
    return tuple(sorted(pabs_canon(B[i][j]) for i in range(n) for j in range(i+1, n)))

def ok_caps(B):
    for row in B:
        for e in row:
            if len(e)-1 > DEGCAP: return False
            for x in e:
                if abs(x) > COEFCAP: return False
    return True

# ---------------- BFS island enumeration ----------------
def island(start, statecap=20000, depthcap=16):
    n = len(start)
    k0 = key(start)
    parents = {k0: None}
    mats = {k0: start}
    q = deque([(start, -1, 0)])
    pruned = capped = 0
    while q:
        B, lastk, d = q.popleft()
        if d >= depthcap: continue
        for k in range(n):
            if k == lastk: continue
            B1 = mutate_sym(B, k)
            if not ok_caps(B1): pruned += 1; continue
            k1 = key(B1)
            if k1 in parents: continue
            if len(parents) >= statecap: capped += 1; continue
            parents[k1] = (key(B), k)
            mats[k1] = B1
            q.append((B1, k, d+1))
    return mats, parents, pruned, capped

def word_to(parents, kk):
    w = []
    while parents[kk] is not None:
        pk, k = parents[kk]
        w.append(k); kk = pk
    return list(reversed(w))

# ---------------- self-similarity (ratchet) scan ----------------
def ratchet_scan(mats, parents, n, perms, deltas=(1, 2, 3, 4)):
    buckets = {}
    for kk, M in mats.items():
        buckets.setdefault(inv_hash(M), []).append(kk)
    hits = []
    for kk, M in mats.items():
        if all(len(e) <= 1 for row in M for e in row): continue  # c-independent
        for d in deltas:
            S = [[pshift(M[i][j], d) for j in range(n)] for i in range(n)]
            cands = buckets.get(inv_hash(S))
            if not cands: continue
            for pi in perms:
                for g in (1, -1):
                    tk = key(transform(S, pi, g))
                    if tk in parents:
                        hits.append((kk, tk, d, pi, g))
                        break
                else: continue
                break
            if len(hits) >= 3: return hits
    return hits

def verify_hit(mats, parents, hit, n):
    """concrete check: ratchet word maps M(c) -> g*pi(M(c+d)) for several large c"""
    kk, tk, d, pi, g = hit
    w = word_to(parents, kk)
    w2 = word_to(parents, tk)
    ratchet_word = list(reversed(w)) + w2   # M -> root -> transformed shift
    M = mats[kk]
    for cval in (10**8, 10**8 + 1, 3*10**8):
        Bc = [[peval(M[i][j], cval) for j in range(n)] for i in range(n)]
        Sh = [[peval(pshift(M[i][j], d), cval) for j in range(n)] for i in range(n)]
        target = [[(-Sh[pi[i]][pi[j]] if g < 0 else Sh[pi[i]][pi[j]]) for j in range(n)] for i in range(n)]
        X = Bc
        for k in ratchet_word: X = mutate_int(X, k)
        if X != target: return False, ratchet_word
    return True, ratchet_word

# ---------------- rank-4 template sweep ----------------
def tmpl4(controls, cpoly=(0, 1)):
    a, b, u, v = controls  # (b01, b03, b12, b32); counter at b02; b13 = 0
    P = lambda x: (x,) if x else ()
    n = 4
    B = [[()]*n for _ in range(n)]
    def setpair(i, j, p): B[i][j] = p; B[j][i] = pneg(p)
    setpair(0, 1, P(a)); setpair(0, 3, P(b)); setpair(1, 2, P(u)); setpair(3, 2, P(v))
    setpair(0, 2, pn(cpoly))
    return B

def canon4(controls):
    # symmetry group fixing counter b02: swap 1<->3; swap 0<->2 + global negation
    a, b, u, v = controls
    variants = [(a, b, u, v), (b, a, v, u), (u, v, a, b), (v, u, b, a)]
    return min(variants)

def sweep_rank4(statecap=20000):
    perms = list(permutations(range(4)))
    seen_canon, todo = set(), []
    for controls in product(range(-2, 3), repeat=4):
        if controls == (0, 0, 0, 0): continue
        cn = canon4(controls)
        if cn not in seen_canon:
            seen_canon.add(cn); todo.append(cn)
    print(f"rank-4 sweep: {len(todo)} canonical templates (counter b02, b13=0, controls in -2..2)")
    found, stats = [], []
    t0 = time.time()
    for idx, controls in enumerate(todo):
        mats, parents, pruned, capped = island(tmpl4(controls), statecap=statecap)
        hits = ratchet_scan(mats, parents, 4, perms)
        ver = [(verify_hit(mats, parents, h, 4), h[2], h[4]) for h in hits]
        stats.append((controls, len(mats), pruned, capped, len(hits)))
        if hits:
            found.append((controls, [(okw[0], d, g, okw[1]) for okw, d, g in ver]))
            print(f"  !! HIT template {controls}: verified={ver[0][0][0]} d={ver[0][1]} g={ver[0][2]} word={ver[0][0][1]}")
        if (idx+1) % 30 == 0:
            print(f"  ... {idx+1}/{len(todo)} templates, {time.time()-t0:.0f}s", flush=True)
    return found, stats

# ---------------- rank-5 extensions ----------------
def tmpl5(base_controls, ext, cpoly=(0, 1)):
    a, b, u, v = base_controls
    e04, e14, e24, e34 = ext
    P = lambda x: (x,) if x else ()
    n = 5
    B = [[()]*n for _ in range(n)]
    def setpair(i, j, p): B[i][j] = p; B[j][i] = pneg(p)
    setpair(0, 1, P(a)); setpair(0, 3, P(b)); setpair(1, 2, P(u)); setpair(3, 2, P(v))
    setpair(0, 2, pn(cpoly))
    setpair(0, 4, P(e04)); setpair(1, 4, P(e14)); setpair(2, 4, P(e24)); setpair(3, 4, P(e34))
    return B

def sweep_rank5(bases, statecap=12000):
    perms = []
    for swap02 in (False, True):
        for rest in permutations((1, 3, 4)):
            pi = [0]*5
            pi[0], pi[2] = (2, 0) if swap02 else (0, 2)
            for pos, val in zip((1, 3, 4), rest): pi[pos] = val
            perms.append(tuple(pi))
    exts = [e for e in product((-1, 0, 1), repeat=4) if e != (0, 0, 0, 0)]
    print(f"rank-5 sweep: {len(bases)} bases x {len(exts)} extensions")
    found = []
    t0 = time.time()
    for bi, base in enumerate(bases):
        nstates = []
        for ext in exts:
            mats, parents, pruned, capped = island(tmpl5(base, ext), statecap=statecap)
            nstates.append(len(mats))
            hits = ratchet_scan(mats, parents, 5, perms)
            if hits:
                ver = [(verify_hit(mats, parents, h, 5), h[2], h[4]) for h in hits]
                found.append((base, ext, [(okw[0], d, g, okw[1]) for okw, d, g in ver]))
                print(f"  !! HIT base {base} ext {ext}: verified={ver[0][0][0]} d={ver[0][1]} g={ver[0][2]} word={ver[0][0][1]}")
        print(f"  base {bi+1}/{len(bases)} done ({time.time()-t0:.0f}s), "
              f"island sizes max {max(nstates)} median {sorted(nstates)[len(nstates)//2]}", flush=True)
    return found

if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "rank4"
    if mode == "rank4":
        found, stats = sweep_rank4()
        sizes = sorted(s[1] for s in stats)
        ncapped = sum(1 for s in stats if s[3])
        print(f"\nrank-4 SUMMARY: {len(found)} templates with ratchet hits / {len(stats)}")
        print(f"island sizes: min {sizes[0]}, median {sizes[len(sizes)//2]}, max {sizes[-1]}; "
              f"{ncapped} hit the state cap")
        with open("probe2_rank4_results.json", "w") as f:
            json.dump({"found": [(list(c), [(bool(o), d, g, list(w)) for (o, d, g, w) in v]) for c, v in found],
                       "stats": [(list(c), m, p, cap, h) for c, m, p, cap, h in stats]}, f)
    else:
        bases = [(1, 1, 1, 1), (1, 2, 1, 1), (1, 1, 1, -1)]
        found = sweep_rank5(bases)
        print(f"\nrank-5 SUMMARY: {len(found)} (base, ext) with ratchet hits")
        with open("probe2_rank5_results.json", "w") as f:
            json.dump({"found": [(list(b), list(e), [[bool(o), d, g, list(w)] for (o, d, g, w) in v])
                                  for b, e, v in found]}, f)
