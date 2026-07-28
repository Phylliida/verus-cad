#!/usr/bin/env python3
"""Probe 17 (positive campaign): measure the FORKLESS PART directly (Warkentin),
the right object for decidability. MUT decidable for a class <=> finite computable
forkless part. Validate the fork detector, confirm forks = large-entry outer trees
& forkless part = small-entry core, then measure forkless-part size + stability
across caps on proven-finite families (Markov-type, Fomin) and sweep parametrized
families for a growing (candidate-infinite) forkless part.

Fork (Warkentin Def 2.1, via Burcroff 2605.12865): an ABUNDANT (|b_ij|>=2 for all
pairs), NON-ACYCLIC quiver with a unique point of return r s.t. for Q+(r)={i:b_ri>0},
Q-(r)={j:b_jr>0}: subquivers on Q+(r),Q-(r) are acyclic, and for all i in Q+(r),
j in Q-(r): b_ij > b_ri and b_ij > b_jr.
"""
import sys, itertools, random
from collections import deque, Counter

def toM(t,PAIRS,n):
    M=[[0]*n for _ in range(n)]
    for (i,j),v in zip(PAIRS,t): M[i][j]=v; M[j][i]=-v
    return M
def up(M,PAIRS): return tuple(M[i][j] for (i,j) in PAIRS)
def mutate(t,k,PAIRS,n):
    M=toM(t,PAIRS,n); Mp=[[0]*n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if i==k or j==k: Mp[i][j]=-M[i][j]
            else: Mp[i][j]=M[i][j]+(abs(M[i][k])*M[k][j]+M[i][k]*abs(M[k][j]))//2
    return up(Mp,PAIRS)
def sq(t): return sum(x*x for x in t)
def mx(t): return max((abs(x) for x in t),default=0)

def is_acyclic_sub(M,verts):
    # directed graph on verts, edge a->b if M[a][b]>0 ; check acyclic via DFS
    verts=set(verts); color={}
    def dfs(u):
        color[u]=1
        for w in verts:
            if w!=u and M[u][w]>0:
                if color.get(w)==1: return False
                if color.get(w) is None and not dfs(w): return False
        color[u]=2; return True
    return all(color.get(v) is not None or dfs(v) for v in verts)
def is_abundant(M,n): return all(abs(M[i][j])>=2 for i in range(n) for j in range(i+1,n))
def is_fork(M,n):
    if not is_abundant(M,n): return False
    if is_acyclic_sub(M,range(n)): return False        # must be non-acyclic
    for r in range(n):
        Qp=[i for i in range(n) if i!=r and M[r][i]>0]
        Qm=[j for j in range(n) if j!=r and M[j][r]>0]
        if len(Qp)+len(Qm)!=n-1: continue
        if not (is_acyclic_sub(M,Qp) and is_acyclic_sub(M,Qm)): continue
        ok=True
        for i in Qp:
            for j in Qm:
                if not (M[i][j]>M[r][i] and M[i][j]>M[j][r]): ok=False; break
            if not ok: break
        if ok: return True
    return False

def canon_factory(n,PAIRS):
    PERMS=list(itertools.permutations(range(n)))
    def canon(t):
        M=toM(t,PAIRS,n); best=None
        for pi in PERMS:
            r=tuple(M[pi[i]][pi[j]] for (i,j) in PAIRS)
            if best is None or r<best: best=r
            rn=tuple(-x for x in r)
            if rn<best: best=rn
        return best
    return canon

def forkless_profile(B0,n,caps=(6,10,16,24),statecap=150000):
    PAIRS=[(i,j) for i in range(n) for j in range(i+1,n)]
    canon=canon_factory(n,PAIRS)
    t0=up(B0,PAIRS)
    prev=None; out=[]
    for cap in caps:
        seen={t0}; q=deque([t0]); cut=False
        while q:
            t=q.popleft()
            for k in range(n):
                u=mutate(t,k,PAIRS,n)
                if mx(u)>cap or u in seen: continue
                if len(seen)>=statecap: cut=True; break
                seen.add(u); q.append(u)
            if cut: break
        forkless=[t for t in seen if not is_fork(toM(t,PAIRS,n),n)]
        fl=frozenset(canon(t) for t in forkless)
        # sanity: mean Sum b^2 of forks vs forkless
        fk=[sq(t) for t in seen if is_fork(toM(t,PAIRS,n),n)]
        nf=[sq(t) for t in forkless]
        grew=None if prev is None else (fl!=prev)
        out.append((cap,len(seen),len(fl),grew,cut,
                    (min(fk) if fk else None),(max(nf) if nf else None)))
        prev=fl
    return out

def show(name,B,n):
    prof=forkless_profile(B,n)
    comp=[p[1] for p in prof]; fls=[p[2] for p in prof]
    grew=any(p[3] for p in prof if p[3] is not None)
    cut=any(p[4] for p in prof)
    minfork=prof[-1][5]; maxforkless=prof[-1][6]
    print(f"[{name}] comp={comp} |forkless|={fls} -> "
          f"{'GROWING' if grew else 'stable'}"
          f"  (min Sumb2 over forks={minfork}, max over forkless={maxforkless})"
          f"{'  [cut]' if cut else ''}", flush=True)
    return grew

def markov(n,w):  # cyclic n-quiver all weights w (rank-3 Markov = n=3)
    B=[[0]*n for _ in range(n)]
    for i in range(n):
        j=(i+1)%n; B[i][j]=w; B[j][i]=-w
    return B

if __name__=="__main__":
    print("=== fork-detector validation (forks should have LARGER Sumb2 than forkless) ===")
    # Markov(2,2,2): its whole class is Markov up to relabel -> forkless part size 1, no forks
    show("Markov(2,2,2)", markov(3,2), 3)
    show("cyclic3 w=3", markov(3,3), 3)   # grows -> should have forks (large) + small forkless core
    show("cyclic3 w=4", markov(3,4), 3)
    print("\n=== proven/expected finite forkless (Fomin long-cycle quivers) ===")
    import probe14_fomin as F
    q10={(i,j):2 for i in range(1,6) for j in range(i+1,6)}
    for k in (1,2):
        show(f"Fomin n5 k{k}", F.fomin_B(5,k,q10), 5)
    print("\n=== sweep: parametrized rank-4/5 cyclic families, hunt growing forkless part ===")
    growing=[]
    for n,w in [(4,2),(4,3),(5,2),(5,3)]:
        g=show(f"cyclic{n} w={w}", markov(n,w), n)
        if g: growing.append((n,w))
    print(f"\nGROWING forkless-part families found: {growing if growing else 'NONE (all finite/stable)'}")
