#!/usr/bin/env python3
"""Probe 8b: rank-6 tick search = enumerate words, SMT-solve the wiring per word.

For a FIXED word w over {1,3,4,5} (no k-branching), the mutation is a
deterministic sequence of maps; the 14 non-counter entries evolve as (piecewise-
polynomial) z3 expressions in the initial aux wiring. We ask z3: is there a
wiring in [-2,2]^14 (hub arms fixed) that makes w RESTORE all 14 entries and
accumulate net +delta into the counter (0,2)? First SAT = a rank-6 tick; full
enumeration with no SAT = a bounded freezing-style result.

Run: /home/bepis/.venv/bin/python3 probe8b_wordsearch.py [L] [delta]
"""
import sys, time, itertools
from z3 import *

N=6
PAIRS=[(i,j) for i in range(N) for j in range(i+1,N)]
STATE=[p for p in PAIRS if p!=(0,2)]
PI={p:idx for idx,p in enumerate(STATE)}
def pair(i,j): return (i,j) if i<j else (j,i)

L     = int(sys.argv[1]) if len(sys.argv)>1 else 8
DELTA = int(sys.argv[2]) if len(sys.argv)>2 else 1
M     = 2
KSET  = [1,3,4,5]

def words(L):
    # start with hub fire (1), no immediate repeat
    def rec(prefix):
        if len(prefix)==L: yield tuple(prefix); return
        for k in KSET:
            if prefix and k==prefix[-1]: continue
            yield from rec(prefix+[k])
    yield from rec([1])

def zhalf(s,e,tag):
    h=BitVec(f"h_{tag}",12); s.add(2*h==e); return h

def check_word(w):
    s=Solver(); s.set("timeout",3000)
    B0={p: BitVec(f"b_{i}{j}",12) for p in STATE for (i,j) in [p]}
    # hub arms fixed, aux in [-2,2]
    s.add(B0[(0,1)]==1, B0[(1,2)]==1)
    for p in STATE:
        if p in [(0,1),(1,2)]: continue
        s.add(B0[p]>=-2, B0[p]<=2)
    cur=dict(B0); acc=BitVecVal(0,12); tag=0
    def get(cur,i,j):
        if i==j: return BitVecVal(0,12)
        p=pair(i,j)
        if p==(0,2): return BitVecVal(0,12)
        return cur[p] if i<j else -cur[p]
    def ABS(x): return If(x>=0, x, -x)   # z3 BitVec >= is signed in z3py
    for step,k in enumerate(w):
        nxt={}
        for p in STATE:
            i,j=p
            if k==i or k==j:
                nxt[p]=-cur[p]
            else:
                x=get(cur,i,k); y=get(cur,k,j)
                nxt[p]=cur[p]+zhalf(s,ABS(x)*y+x*ABS(y),tag); tag+=1
        # accumulator into (0,2)
        x=get(cur,0,k); y=get(cur,k,2)
        acc=acc+zhalf(s,ABS(x)*y+x*ABS(y),tag); tag+=1
        # keep entries bounded
        for p in STATE: s.add(nxt[p]>=-M, nxt[p]<=M)
        cur=nxt
    for p in STATE: s.add(cur[p]==B0[p])
    s.add(acc==DELTA)
    r=s.check()
    if r==sat:
        m=s.model()
        return {f"b{i}{j}":m[B0[(i,j)]].as_signed_long() for (i,j) in STATE}
    return None

if __name__=="__main__":
    print(f"probe8b: rank-6 tick, |w|={L}, delta={DELTA}, M={M}, K in {KSET}", flush=True)
    t0=time.time(); n=0
    allw=list(words(L))
    print(f"  {len(allw)} words to check", flush=True)
    for w in allw:
        n+=1
        res=check_word(w)
        if res is not None:
            print(f"\n*** TICK FOUND *** word={w}\n  wiring={res}")
            break
        if n%50==0:
            print(f"  ...{n}/{len(allw)} words, {time.time()-t0:.0f}s", flush=True)
    else:
        print(f"\nUNSAT over all {len(allw)} words at L={L}: no rank-6 tick "
              f"(bounded freezing-style result). {time.time()-t0:.0f}s")
