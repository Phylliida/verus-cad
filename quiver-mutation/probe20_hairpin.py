#!/usr/bin/env python3
"""Probe 20: automated HAIRPIN HUNT on Q9/Q13/Q15/Q19 (+ Q14 sanity).

A "hairpin" is a short mutation word w such that the iterates w^m(Q) grow
unboundedly while staying NON-ABUNDANT (some |b_ij|<2 survives) -- hence non-fork
-- proving the forkless part of [Q] is infinite. Preference: LINEAR growth (max
entry increases by a constant per step) => clean closed form for a rigorous proof.
Non-forkness cross-checked with the database forkWithPOR. Python big-ints: no
overflow.
"""
import sys, itertools
sys.path.insert(0,'.'); sys.path.insert(0,'quiver-mutation-database')
import probe17_forkless as P
from quiver import Quiver
N=5; PAIRS=[(i,j) for i in range(N) for j in range(i+1,N)]
def toM(t): return P.toM(t,PAIRS,N)
def mut(t,k): return P.mutate(t,k,PAIRS,N)
def mx(t): return max(abs(x) for x in t)
def abundant(t): return all(abs(x)>=2 for x in t)
def is_fork(t): return P.is_fork(toM(t),N)
def db_fork(t):
    Q=Quiver(toM(t)); return any(Q.forkWithPOR(r) for r in range(N))
def multiset(t): return tuple(sorted(abs(x) for x in t))

QUIVERS = {
 "Q14": (-2,-2,2,-2,-2,-2,1,2,1,2),   # sanity: mu3 mu0 known hairpin
 "Q9":  (0,-1,0,2,-1,3,-3,2,2,3),
 "Q13": (2,-2,-1,2,-1,0,-2,2,0,-2),
 "Q15": (2,-2,2,-2,2,1,-1,2,2,-2),
 "Q19": (-2,0,0,-2,-2,-1,2,2,1,-2),
}

def words(maxlen):
    for L in range(1,maxlen+1):
        for w in itertools.product(range(N), repeat=L):
            if any(w[i]==w[i+1] for i in range(L-1)): continue   # no immediate repeat
            if L>1 and w[0]==w[-1]: continue                     # w^m has no repeat at seam
            yield w

def apply_word(t,w):
    for k in w: t=mut(t,k)
    return t

def analyze(seed, w, M=24):
    """return (ok, growth_type, deltas) if w is a hairpin on seed."""
    orbit=[seed]; t=seed
    for _ in range(M):
        t=apply_word(t,w)
        if mx(t)>10**9: break
        orbit.append(t)
    if len(orbit)<8: return None
    # non-abundant (=> non-fork) for all iterates, strictly growing, distinct
    if any(abundant(o) for o in orbit): return None
    mxs=[mx(o) for o in orbit]
    if not all(mxs[i]<mxs[i+1] for i in range(len(mxs)-1)): return None
    if len({multiset(o) for o in orbit})!=len(orbit): return None
    # growth type: linear if per-step entry-diffs are eventually constant
    diffs=[tuple(orbit[i+1][p]-orbit[i][p] for p in range(10)) for i in range(len(orbit)-1)]
    linear = all(d==diffs[-1] for d in diffs[2:])   # affine (constant increment) after warmup
    return ("linear" if linear else "superlinear", diffs[-1], mxs)

if __name__=="__main__":
    for name,seed in QUIVERS.items():
        found=None
        for w in words(4):
            r=analyze(seed,w)
            if r:
                gtype,delta,mxs=r
                # prefer linear; take first linear, else remember first found
                if gtype=="linear":
                    found=(w,gtype,delta,mxs); break
                if found is None: found=(w,gtype,delta,mxs)
        if found:
            w,gtype,delta,mxs=found
            # verify non-fork (both detectors) to m=200
            t=seed; okf=True
            for m in range(201):
                if is_fork(t) or db_fork(t): okf=False; break
                t=apply_word(t,w)
            nz=[(PAIRS[p],delta[p]) for p in range(10) if delta[p]!=0]
            print(f"[{name}] HAIRPIN w={w} ({gtype}), per-step nonzero entry-deltas={nz}")
            print(f"        max-entry seq (first 8): {mxs[:8]}  | non-fork(mine+db) m=0..200: {okf}")
        else:
            print(f"[{name}] no hairpin found in words up to length 4")
