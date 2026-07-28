#!/usr/bin/env python3
"""Probe 5: does a rank-5 SPLIT re-arm gadget achieve a uniform counter tick?

Rank-4 freezes because one auxiliary vertex cannot re-arm both hub arms while
holding the accumulator (inconsistent sign system, see plan 5.5). Rank 5 splits
the re-arm: vertex 3 (wired {0,1}) re-arms b_01, vertex 4 (wired {1,2}) re-arms
b_12. We search the symbolic-in-c island of such gadgets for a self-similarity
ratchet  S2 = +/- pi( S1|_{c->c+delta} )  -- a uniform counter climb anywhere in
the island -- over a focused grid of small integer weights.

Entries are polynomials in c; signs taken for c >> 0. Any hit is verified by
concrete integer mutation at several large c.
"""
import sys, time
from collections import deque
from itertools import product, permutations
from math import comb

DEGCAP = 4          # a genuine tick returns to a degree-1-in-c relabeling; keep low
COEFCAP = 10**6

# ---- polys in c (low->high) ----
def pn(t):
    t=list(t)
    while t and t[-1]==0: t.pop()
    return tuple(t)
def padd(a,b):
    if len(a)<len(b): a,b=b,a
    return pn(tuple(x+(b[i] if i<len(b) else 0) for i,x in enumerate(a)))
def pneg(a): return tuple(-x for x in a)
def pmul(a,b):
    if not a or not b: return ()
    r=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b): r[i+j]+=x*y
    return pn(r)
def psign(a): return 0 if not a else (1 if a[-1]>0 else -1)
def pshift(a,d):
    r=[0]*len(a)
    for i,ai in enumerate(a):
        if ai:
            for j in range(i+1): r[j]+=ai*comb(i,j)*d**(i-j)
    return pn(r)
def peval(a,c):
    v=0
    for x in reversed(a): v=v*c+x
    return v
def pabs_canon(a):
    na=pneg(a); return a if a>=na else na

N=5
IDX={}; PAIRS=[]
for i in range(N):
    for j in range(i+1,N): IDX[(i,j)]=len(PAIRS); PAIRS.append((i,j))
def fget(M,i,j):
    if i==j: return ()
    if i<j: return M[IDX[(i,j)]]
    return pneg(M[IDX[(j,i)]])
def mutate(M,k):
    out=[None]*len(PAIRS)
    for (i,j) in PAIRS:
        idx=IDX[(i,j)]
        if i==k or j==k: out[idx]=pneg(M[idx]); continue
        x=fget(M,i,k); y=fget(M,k,j); sx,sy=psign(x),psign(y)
        if sx!=0 and sx==sy:
            corr=pmul(x,y)
            if sx<0: corr=pneg(corr)
            out[idx]=padd(M[idx],corr)
        else: out[idx]=M[idx]
    return tuple(out)
def key(M): return M
def deg(M): return max((len(e)-1 for e in M),default=0)
def okcap(M):
    for e in M:
        if len(e)-1>DEGCAP: return False
        for x in e:
            if abs(x)>COEFCAP: return False
    return True
def inv_hash(M):
    return tuple(sorted(pabs_canon(e) for e in M))
def transform(M,pi,g):
    # relabel vertices by pi, optional global sign g
    out=[None]*len(PAIRS)
    for (i,j) in PAIRS:
        e=fget(M,pi[i],pi[j])
        out[IDX[(i,j)]]= pneg(e) if g<0 else e
    return tuple(out)

def island(start, statecap=15000):
    seen={start}; q=deque([start]); mats={start:start}; parents={start:None}
    while q:
        M=q.popleft()
        for k in range(N):
            C=mutate(M,k)
            if not okcap(C): continue
            if C in seen: continue
            if len(seen)>=statecap: continue
            seen.add(C); parents[C]=(M,k); mats[C]=C; q.append(C)
    return mats, parents

PERMS=[p for p in permutations(range(N))]
def ratchet_scan(mats, parents, deltas=(1,2)):
    buckets={}
    for M in mats: buckets.setdefault(inv_hash(M),[]).append(M)
    for M in mats:
        if all(len(e)<=1 for e in M): continue
        for d in deltas:
            S=tuple(pshift(e,d) for e in M)
            if inv_hash(S) not in buckets: continue
            for pi in PERMS:
                for g in (1,-1):
                    if transform(S,pi,g) in parents:
                        return (M, transform(S,pi,g), d, pi, g)
    return None

def word_to(parents,M):
    w=[]
    while parents[M] is not None:
        p,k=parents[M]; w.append(k); M=p
    return list(reversed(w))

def mutate_int(B,k):
    n=len(B); Bp=[[0]*n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if i==k or j==k: Bp[i][j]=-B[i][j]
            else: Bp[i][j]=B[i][j]+(abs(B[i][k])*B[k][j]+B[i][k]*abs(B[k][j]))//2
    return Bp
def to_int(M,c):
    B=[[0]*N for _ in range(N)]
    for (i,j),idx in IDX.items():
        v=peval(M[idx],c); B[i][j]=v; B[j][i]=-v
    return B
def verify(mats,parents,hit):
    M,T,d,pi,g=hit
    w=list(reversed(word_to(parents,M)))+word_to(parents,T)
    for c in (10**7,10**7+1,3*10**7):
        B=to_int(M,c); X=B
        for k in w: X=mutate_int(X,k)
        Sh=to_int(tuple(pshift(e,d) for e in M),c)
        tgt=[[(-Sh[pi[i]][pi[j]] if g<0 else Sh[pi[i]][pi[j]]) for j in range(N)] for i in range(N)]
        if X!=tgt: return False,w
    return True,w

def seed(arm3, w34, w13, w14, w24):
    """hub 1 armed (b01=1,b12=1), accumulator b02=c, split re-arm with the
    auxiliaries COUPLED (b34=w34) so vertices 3 and 4 can re-arm each other:
       vertex 3 on {0,1,4}: b03=arm3, b13=w13, b34=w34 ;
       vertex 4 on {1,2,3}: b14=w14, b24=w24, b34=w34."""
    ent={(0,1):(1,),(1,2):(1,),(0,2):(0,1),
         (0,3):(arm3,),(1,3):(w13,),(2,3):(),
         (0,4):(),(1,4):(w14,),(2,4):(w24,),(3,4):(w34,)}
    return tuple(ent[p] for p in PAIRS)

if __name__=="__main__":
    t0=time.time()
    tried=0; found=[]
    # focused grid: magnitudes 1..2 with signs suggested by the re-arm derivation
    # DECOUPLED family: b13,b14 negative (opposite hub arm) so mu_1 does not
    # perturb the re-arm lines -- fire step is clean (b02 += 1 exactly).
    grid=[]
    for arm3 in (1,):
        for w34 in (-2,-1,1,2):
            for w13 in (-1,1):
                for w14 in (-1,1):
                    for w24 in (-1,1):
                        grid.append((arm3,w34,w13,w14,w24))
    print(f"probe5 (coupled aux, b34): {len(grid)} seeds, DEGCAP={DEGCAP}", flush=True)
    for (arm3,w34,w13,w14,w24) in grid:
        s=seed(arm3,w34,w13,w14,w24)
        mats,parents=island(s)
        tried+=1
        hit=ratchet_scan(mats,parents)
        if hit:
            ok,w=verify(mats,parents,hit)
            found.append((arm3,w34,w13,w14,w24,ok,hit[2],hit[4],len(w)))
            print(f"  !! seed(b34={w34},w13={w13},w14={w14},w24={w24}) RATCHET verified={ok} "
                  f"delta={hit[2]} g={hit[4]} |island|={len(mats)} word_len={len(w)}", flush=True)
        if tried%16==0:
            print(f"  ...{tried}/{len(grid)} seeds, {time.time()-t0:.0f}s, island sizes vary", flush=True)
    print(f"\nprobe5 done: {len(found)} verified ratchets / {len(grid)} seeds ({time.time()-t0:.0f}s)")
    if not found:
        print("no uniform tick in this focused family at DEGCAP=3 -- widen DEGCAP or weights,")
        print("or the split re-arm still doesn't compose (cycle fails to close).")
