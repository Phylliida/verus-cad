#!/usr/bin/env python3
"""Probe 10 (Debt 1): do squares + pentagons SPAN the cycle space? (done right)

Work in the UNLABELED exchange graph (vertices = quivers up to S_n relabeling),
where a square (b_jk=0: commuting mutations) is a 4-cycle and a pentagon
(|b_jk|=1: the A_2 relation) is a 5-cycle. Build the graph, take the cycle-space
dimension E-V+1, and compute the GF(2) rank of the span of all squares and
pentagons. rank == E-V+1  <=>  the component is square/pentagon-generated
(cluster-like, Fomin-Zelevinsky); rank < E-V+1  =>  independent long cycles
(instruction material).

Validated on finite-type quivers (A_1xA_1 -> square; A_2 -> pentagon; A_5 ->
associahedron) where FZ guarantees full span, before the leaky component (which
is entry-capped, so boundary cycles are excluded -- reported as a caveat).
"""
import sys
from collections import deque
from itertools import permutations

def make(n):
    IDX={}; PAIRS=[]
    for i in range(n):
        for j in range(i+1,n): IDX[(i,j)]=len(PAIRS); PAIRS.append((i,j))
    return IDX,PAIRS

def mutate(t,k,n,PAIRS):
    B=[[0]*n for _ in range(n)]
    for (i,j),v in zip(PAIRS,t): B[i][j]=v; B[j][i]=-v
    Bp=[[0]*n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if i==k or j==k: Bp[i][j]=-B[i][j]
            else: Bp[i][j]=B[i][j]+(abs(B[i][k])*B[k][j]+B[i][k]*abs(B[k][j]))//2
    return tuple(Bp[i][j] for (i,j) in PAIRS)
def maxabs(t): return max((abs(x) for x in t),default=0)
def ent(t,i,j,PAIRS,IDX):
    if i==j: return 0
    return t[IDX[(i,j)]] if i<j else -t[IDX[(j,i)]]

def canon_factory(n,PAIRS):
    PERMS=list(permutations(range(n)))
    def canon(t):
        B=[[0]*n for _ in range(n)]
        for (i,j),v in zip(PAIRS,t): B[i][j]=v; B[j][i]=-v
        best=None
        for pi in PERMS:
            r=tuple(B[pi[i]][pi[j]] for (i,j) in PAIRS)
            if best is None or r<best: best=r
        return best
    return canon

def build(seed,n,cap):
    IDX,PAIRS=make(n); canon=canon_factory(n,PAIRS)
    s=canon(seed); V={s:0}; rep={s:seed}; order=[s]; q=deque([seed])
    seenlab={seed}
    while q:
        t=q.popleft()
        for k in range(n):
            u=mutate(t,k,n,PAIRS)
            if maxabs(u)>cap: continue
            cu=canon(u)
            if cu not in V:
                V[cu]=len(order); order.append(cu); rep[cu]=u
            if u not in seenlab:
                seenlab.add(u); q.append(u)
    # edges (undirected) between canonical vertices
    E={}
    def eid(a,b):
        key=(a,b) if a<b else (b,a)
        if key not in E: E[key]=len(E)
        return E[key]
    for cu in order:
        t=rep[cu]
        for k in range(n):
            u=mutate(t,k,n,PAIRS)
            if maxabs(u)>cap: continue
            cv=canon(u)
            if V[cu]!=V[cv]: eid(V[cu],V[cv])
    return V,order,rep,E,IDX,PAIRS,canon

def cycles(V,order,rep,E,IDX,PAIRS,canon,n,cap):
    """generate square (b=0) and pentagon (|b|=1) cycles as edge-id sets."""
    def eidx(a,b):
        key=(a,b) if a<b else (b,a); return E.get(key)
    def path_edges(verts):
        ids=[]
        for a,b in zip(verts,verts[1:]+verts[:1]):
            e=eidx(a,b)
            if e is None: return None
            ids.append(e)
        return ids
    sqs=[]; pens=[]
    for cu in order:
        B=rep[cu]
        for a in range(n):
            for b in range(a+1,n):
                w=ent(B,a,b,PAIRS,IDX)
                if w==0:
                    B1=mutate(B,a,n,PAIRS); B2=mutate(B1,b,n,PAIRS); B3=mutate(B,b,n,PAIRS)
                    if max(maxabs(x) for x in (B1,B2,B3))>cap: continue
                    vs=[V[cu],V[canon(B1)],V[canon(B2)],V[canon(B3)]]
                    if len(set(vs))==4:
                        pe=path_edges(vs)
                        if pe: sqs.append(frozenset(pe))
                elif abs(w)==1:
                    # alternating j=a,k=b: mu_a,mu_b,mu_a,mu_b,mu_a should close in S_n quotient
                    seq=[B]; x=B
                    for step in range(5):
                        x=mutate(x, a if step%2==0 else b, n, PAIRS); seq.append(x)
                    if max(maxabs(x) for x in seq)>cap: continue
                    if canon(seq[5])==cu:
                        vs=[V[canon(seq[i])] for i in range(5)]
                        if len(set(vs))==5:
                            pe=path_edges(vs)
                            if pe: pens.append(frozenset(pe))
    return sqs,pens

def gf2_rank(vectors,nedges):
    basis=[]  # list of ints (bitmasks)
    for s in vectors:
        v=0
        for e in s: v|=(1<<e)
        for b in basis:
            v=min(v, v^b)
        # proper reduction:
        v=0
        for e in s: v|=(1<<e)
        for b in basis:
            if (v ^ b) < v: v^=b
        if v: basis.append(v); basis.sort(reverse=True)
    return len(basis)

def analyze(name,seed,n,cap):
    V,order,rep,E,IDX,PAIRS,canon=build(seed,n,cap)
    nv=len(order); ne=len(E)
    cyc=ne-nv+1
    sqs,pens=cycles(V,order,rep,E,IDX,PAIRS,canon,n,cap)
    r=gf2_rank(sqs+pens,ne)
    print(f"{name}: |V|={nv} |E|={ne} cycle-dim={cyc}  squares={len(sqs)} pentagons={len(pens)}  "
          f"span-rank={r}  -> {'SPANS (square/pentagon-generated)' if r==cyc and cyc>0 else ('trivial' if cyc==0 else f'GAP {cyc-r} (long cycles)')}")
    return cyc,r

if __name__=="__main__":
    print("=== validation on finite type ===")
    analyze("A1xA1 (b01=0)", (0,), 2, 3)              # 1 pair, b01=0 -> square
    analyze("A2 (b01=1)",    (1,), 2, 3)              # b01=1 -> pentagon
    # A3 path 0->1->2 : pairs (01,02,12)=(1,0,1)
    analyze("A3 path",       (1,0,1), 3, 3)
    # A5 path 0->1->2->3->4: pairs order (01,02,03,04,12,13,14,23,24,34)
    a5={(0,1):1,(1,2):1,(2,3):1,(3,4):1}
    IDX5,P5=make(5); a5t=tuple(a5.get(p,0) for p in P5)
    analyze("A5 path",       a5t, 5, 3)

    print("\n=== leaky rank-5 component (entry-capped; boundary caveat) ===")
    e={(0,1):1,(1,2):1,(0,2):5,(0,3):1,(1,3):2,(1,4):2,(2,4):-1}
    IDX5,P5=make(5); leaky=tuple(e.get(p,0) for p in P5)
    for cap in (8,10,12):
        analyze(f"leaky T(5) cap={cap}", leaky, 5, cap)
