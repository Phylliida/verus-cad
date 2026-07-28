#!/usr/bin/env python3
"""Probe 15 (Danielle option 1): the clusters->B FIBER structure + a decidability
check on Fomin's long-cycle family.

MUT lives in the B-graph = quotient of the cluster exchange graph (many clusters
-> one B). Part A: for a family, build the capped cluster exchange graph and, for
each distinct B (up to relabeling), count how many distinct clusters project to
it (fiber size). Trivial fibers (all size 1) => MUT ~ cluster equivalence (tame);
rich/growing fibers => the projection is where B-graph complexity hides.

Part B (Fomin substrate): does a Fomin long-cycle quiver's B-mutation class have a
FINITE descent core (=> decidable despite long non-pavable cycles) or a growing
one (=> machine candidate)? Uses the reliable min-Sum-b^2 core diagnostic.
"""
import sys
from collections import deque, Counter
from itertools import permutations
import probe12_gvec as P
import probe14_fomin as F

# ---------- Part A: fiber structure ----------
def bcanon(Brows,n):
    PERMS=P._perms(n); best=None
    for pi in PERMS:
        t=tuple(Brows[pi[i]][pi[j]] for i in range(n) for j in range(i+1,n))
        if best is None or t<best: best=t
    return best
def fibers(B0,n,cap):
    V,order,cut=P.build(B0,n,cap)
    byB=Counter()
    seenBcluster=set()
    for M in order:
        b=bcanon(M[:n],n)
        seenBcluster.add((b, P.key(M)))
    fib=Counter()
    for b,ck in seenBcluster: fib[b]+=1
    dist=Counter(fib.values())
    print(f"  |clusters|={len(order)} |distinct B|={len(fib)} "
          f"fiber-size dist(size:#B)={dict(sorted(dist.items()))} maxfiber={max(fib.values())}"
          f"{'  [cut]' if cut else ''}")
    return dist

# ---------- Part B: descent core of a B-mutation class ----------
def mutate(t,k,n,PAIRS):
    B=[[0]*n for _ in range(n)]
    for (i,j),v in zip(PAIRS,t): B[i][j]=v; B[j][i]=-v
    Bp=[[0]*n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if i==k or j==k: Bp[i][j]=-B[i][j]
            else: Bp[i][j]=B[i][j]+(abs(B[i][k])*B[k][j]+B[i][k]*abs(B[k][j]))//2
    return tuple(Bp[i][j] for (i,j) in PAIRS)
def core_of(B0,n,caps):
    PAIRS=[(i,j) for i in range(n) for j in range(i+1,n)]
    s0=tuple(B0[i][j] for (i,j) in PAIRS)
    def sq(t): return sum(x*x for x in t)
    def mx(t): return max(abs(x) for x in t)
    PERMS=P._perms(n)
    def cn(t):
        Bm=[[0]*n for _ in range(n)]
        for (i,j),v in zip(PAIRS,t): Bm[i][j]=v; Bm[j][i]=-v
        best=None
        for pi in PERMS:
            r=tuple(Bm[pi[i]][pi[j]] for (i,j) in PAIRS)
            if best is None or r<best: best=r
            rn=tuple(-x for x in r)
            if rn<best: best=rn
        return best
    prevcore=None
    for cap in caps:
        seen={s0}; q=deque([s0]); cut=False
        while q:
            t=q.popleft()
            for k in range(n):
                u=mutate(t,k,n,PAIRS)
                if mx(u)>cap or u in seen: continue
                if len(seen)>=300000: cut=True; break
                seen.add(u); q.append(u)
            if cut: break
        gmin=min(sq(t) for t in seen)
        core={cn(t) for t in seen if sq(t)==gmin}
        grew = "" if prevcore is None else ("  GREW" if core!=prevcore else "  stable")
        print(f"  cap={cap}: |class-comp|={len(seen)} minSumb2={gmin} |canon-core|={len(core)}"
              f"{grew}{'  [cut]' if cut else ''}", flush=True)
        prevcore=core

if __name__=="__main__":
    print("=== Part A: fiber structure (clusters per B) ===")
    e={(0,1):1,(1,2):1,(0,2):5,(0,3):1,(1,3):2,(1,4):2,(2,4):-1}
    leaky=[[0]*5 for _ in range(5)]
    for (i,j),v in e.items(): leaky[i][j]=v; leaky[j][i]=-v
    print("[leaky T(5)]");
    for cap in (8,10): fibers(leaky,5,cap)
    print("[A2] (sanity: pentagon, 5 clusters, all B same up to relabel)")
    fibers([[0,1],[-1,0]],2,50)

    print("\n=== Part B: descent core of Fomin long-cycle quivers ===")
    q10={(i,j):2 for i in range(1,6) for j in range(i+1,6)}
    for k in (1,2):
        B=F.fomin_B(5,k,q10)
        print(f"[Fomin n=5 k={k}] (long cycle len {5+4*k}, entries up to {max(abs(x) for r in B for x in r)})")
        core_of(B,5,(20,40,80))
