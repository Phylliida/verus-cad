#!/usr/bin/env python3
"""Probe 12 (Debt 1, done right): squares+pentagons span the CLUSTER exchange
graph's cycle space?  Track principal coefficients (c-vectors): the extended
matrix M = [B; C] (2n x n, C starts = I_n) mutates as a whole, and exchange-graph
vertices are full seeds (B,C) -- so the FZ pentagon (|b|=1, A_2) genuinely closes
as a 5-cycle (C distinguishes the 5 seeds the bare quiver collapses).

Rectangular mutation at column k (0<=k<n): negate column k everywhere and
principal row k; quadratic update elsewhere (uses principal row k). This tracks B
and sign-coherent c-vectors simultaneously.

Validate on finite type (A_2 -> pentagon; A_5 -> associahedron, must SPAN), then
the leaky family (entry-capped on M; boundary caveat).
"""
import sys
from collections import deque

from itertools import permutations
_PERM_CACHE={}
def _perms(n):
    if n not in _PERM_CACHE: _PERM_CACHE[n]=list(permutations(range(n)))
    return _PERM_CACHE[n]

def mutate_ext(M,k,n):
    R=len(M); Mp=[[0]*n for _ in range(R)]
    for i in range(R):
        Mik=M[i][k]
        for j in range(n):
            if j==k: Mp[i][j]=-M[i][j]
            elif i==k: Mp[i][j]=-M[i][j]
            else:
                Mkj=M[k][j]
                Mp[i][j]=M[i][j]+(abs(Mik)*Mkj+Mik*abs(Mkj))//2
    return Mp

def key(M):
    """canonical seed up to relabeling pi: B[i][j]->B[pi i][pi j], C cols->C[:,pi j].
    (A cluster returns up to relabeling after a pentagon, so the exchange-graph
    vertex is the seed modulo relabeling.)"""
    n=len(M[0]); R=len(M); best=None
    for pi in _perms(n):
        rows=[]
        for i in range(n):        # B block: permute rows and cols
            rows.append(tuple(M[pi[i]][pi[j]] for j in range(n)))
        for i in range(n,R):      # C block: permute columns only
            rows.append(tuple(M[i][pi[j]] for j in range(n)))
        t=tuple(rows)
        if best is None or t<best: best=t
    return best
def maxabs(M): return max(abs(x) for r in M for x in r)
def initM(B,n):
    M=[list(r) for r in B]
    for i in range(n): M.append([1 if j==i else 0 for j in range(n)])
    return M

def build(B0,n,cap,statecap=400000):
    M0=initM(B0,n); V={key(M0):0}; order=[M0]; q=deque([M0])
    while q:
        M=q.popleft()
        for k in range(n):
            Mm=mutate_ext(M,k,n)
            if maxabs(Mm)>cap: continue
            kk=key(Mm)
            if kk not in V:
                V[kk]=len(order); order.append(Mm); q.append(Mm)
            if len(V)>=statecap: return V,order,True
    return V,order,False

def edges_of(V,order,n,cap):
    E={}
    def eid(a,b):
        t=(a,b) if a<b else (b,a)
        if t not in E: E[t]=len(E)
        return E[t]
    for M in order:
        a=V[key(M)]
        for k in range(n):
            Mm=mutate_ext(M,k,n)
            if maxabs(Mm)>cap: continue
            b=V.get(key(Mm))
            if b is not None and a!=b: eid(a,b)
    return E

def cycles(V,order,E,n,cap):
    def eidx(a,b):
        return E.get((a,b) if a<b else (b,a))
    def loop(verts):
        ids=[]
        for a,b in zip(verts,verts[1:]+verts[:1]):
            e=eidx(a,b)
            if e is None: return None
            ids.append(e)
        return ids
    sqs=[]; pens=[]
    for M in order:
        v0=V[key(M)]; B=M[:n]
        for a in range(n):
            for b in range(a+1,n):
                w=B[a][b]
                if w==0:
                    M1=mutate_ext(M,a,n); M2=mutate_ext(M1,b,n); M3=mutate_ext(M,b,n)
                    if max(maxabs(x) for x in (M1,M2,M3))>cap: continue
                    vs=[v0,V.get(key(M1)),V.get(key(M2)),V.get(key(M3))]
                    if None in vs or len(set(vs))!=4: continue
                    pe=loop(vs)
                    if pe: sqs.append(frozenset(pe))
                elif abs(w)==1:
                    seq=[M]; x=M
                    for s in range(5):
                        x=mutate_ext(x, a if s%2==0 else b, n); seq.append(x)
                    if max(maxabs(y) for y in seq)>cap: continue
                    if key(seq[5])!=key(M): continue           # must close in 5
                    vs=[V.get(key(seq[i])) for i in range(5)]
                    if None in vs or len(set(vs))!=5: continue
                    pe=loop(vs)
                    if pe: pens.append(frozenset(pe))
    return sqs,pens

def gf2_rank(vectors):
    basis=[]
    for s in vectors:
        v=0
        for e in s: v|=(1<<e)
        for b in basis:
            if v^b < v: v^=b
        if v:
            basis.append(v); basis.sort(reverse=True)
    return len(basis)

def analyze(name,B0,n,cap):
    V,order,cut=build(B0,n,cap)
    E=edges_of(V,order,n,cap); nv=len(order); ne=len(E); cyc=ne-nv+1
    sqs,pens=cycles(V,order,E,n,cap)
    r=gf2_rank(sqs+pens)
    verdict=('SPANS' if r==cyc and cyc>=0 else f'GAP {cyc-r}')
    print(f"{name}: |V|={nv} |E|={ne} cycle-dim={cyc} squares={len(sqs)} pentagons={len(pens)} "
          f"span-rank={r} -> {verdict}{'  [statecap cut]' if cut else ''}", flush=True)
    return cyc,r

if __name__=="__main__":
    print("=== validation (finite type: must reproduce pentagon / span) ===")
    analyze("A2 (0->1)", [[0,1],[-1,0]], 2, 50)
    analyze("A2xA1? A3 path", [[0,1,0],[-1,0,1],[0,-1,0]], 3, 50)
    a5=[[0,0,0,0,0] for _ in range(5)]
    for i in range(4): a5[i][i+1]=1; a5[i+1][i]=-1
    analyze("A5 path", a5, 5, 50)
    print("\n=== leaky rank-5 cluster exchange graph (M entry-capped; caveat) ===")
    e={(0,1):1,(1,2):1,(0,2):5,(0,3):1,(1,3):2,(1,4):2,(2,4):-1}
    B=[[0]*5 for _ in range(5)]
    for (i,j),v in e.items(): B[i][j]=v; B[j][i]=-v
    for cap in (6,8,10):
        analyze(f"leaky T(5) cap={cap}", B, 5, cap)
