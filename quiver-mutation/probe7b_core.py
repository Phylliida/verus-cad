#!/usr/bin/env python3
"""Probe 7b: is the leaky family DECIDABLE by descent, or a machine host?

Probe 7 showed T(5) not~ T(6) (disjoint entry-capped islands). Now the crux:
the GLOBAL minimal-Sum-b^2 stratum ("descent core") of each class --
  - FINITE and stable across caps  => compare cores decides equivalence =>
    the family is descent-TAME (decidable) and CANNOT host an undecidable
    reduction, even though it separates counter values;
  - GROWS with the cap => no finite core => the machine-host signal survives.

For each counter value we fully enumerate the |entry|<=cap orbit component, take
the class-minimum of Sum b^2, and canonicalize the minimal stratum (under
S_5 x global sign). We watch the core size as cap grows.
"""
from collections import deque
from itertools import permutations

N=5
IDX={}; PAIRS=[]
for i in range(N):
    for j in range(i+1,N): IDX[(i,j)]=len(PAIRS); PAIRS.append((i,j))
def mutate(B,k):
    Bp=[[0]*N for _ in range(N)]
    for i in range(N):
        for j in range(N):
            if i==k or j==k: Bp[i][j]=-B[i][j]
            else: Bp[i][j]=B[i][j]+(abs(B[i][k])*B[k][j]+B[i][k]*abs(B[k][j]))//2
    return Bp
def skew(ent):
    B=[[0]*N for _ in range(N)]
    for (i,j),v in ent.items(): B[i][j]=v; B[j][i]=-v
    return B
def up(B): return tuple(B[i][j] for (i,j) in PAIRS)
def from_up(t):
    B=[[0]*N for _ in range(N)]
    for (i,j),v in zip(PAIRS,t): B[i][j]=v; B[j][i]=-v
    return B
def sq(t): return sum(x*x for x in t)
def maxabs(t): return max(abs(x) for x in t)
PERMS=list(permutations(range(N)))
def canon_up(t):
    B=from_up(t); best=None
    for pi in PERMS:
        r=tuple(B[pi[i]][pi[j]] if pi[i]<pi[j] else -B[pi[j]][pi[i]] for (i,j) in PAIRS)
        if best is None or r<best: best=r
        rn=tuple(-x for x in r)
        if rn<best: best=rn
    return best

def island(seed, cap, statecap=250000):
    start=up(skew(seed)); seen={start}; q=deque([start]); cut=False
    while q:
        t=q.popleft(); B=from_up(t)
        for k in range(N):
            C=up(mutate(B,k))
            if maxabs(C)>cap or C in seen: continue
            if len(seen)>=statecap: cut=True; continue
            seen.add(C); q.append(C)
    return seen, cut

FAM=lambda c: {(0,1):1,(1,2):1,(0,2):c,(0,3):1,(1,3):2,(1,4):2,(2,4):-1}

def core(seed, cap):
    isl,cut=island(seed,cap)
    m=min(sq(t) for t in isl)
    strat=[t for t in isl if sq(t)==m]
    ccore={canon_up(t) for t in strat}
    # also band [m, m+8] to see if near-minimal stratum is larger
    band={canon_up(t) for t in isl if sq(t)<=m+8}
    return m, len(strat), ccore, len(band), len(isl), cut

if __name__=="__main__":
    for c in (5,6):
        print(f"=== T({c}) ===")
        prev=None
        for cap in (15,25,40,60):
            m,ns,cc,nb,ni,cut=core(FAM(c),cap)
            grew = "" if prev is None else ("  (core GREW)" if cc!=prev else "  (core stable)")
            print(f"  cap={cap:3d}: |island|={ni:7d} minSumb2={m:4d} "
                  f"|min-stratum|={ns} |canon-core|={len(cc)} |canon band<=min+8|={nb}"
                  f"{'  [statecap hit]' if cut else ''}{grew}")
            prev=cc
        print(f"  -> canonical core (min-Sum-b^2 stratum, up to symmetry):")
        for t in sorted(cc)[:6]: print("      ", t)
    # separation check between the two cores at the largest cap
    _,_,cc5,_,_,_=core(FAM(5),60)
    _,_,cc6,_,_,_=core(FAM(6),60)
    print(f"\ncores disjoint (T5 vs T6): {cc5.isdisjoint(cc6)}  "
          f"(|core5|={len(cc5)} |core6|={len(cc6)})")
    print("verdict: FINITE stable core => descent-decidable (not a machine host); "
          "GROWING core => machine signal survives.")
