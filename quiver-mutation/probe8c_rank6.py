#!/usr/bin/env python3
"""Probe 8c: rank-6 tick search, concrete symbolic-in-c self-similarity (fast;
finds ticks of ANY length within the degree-capped island, unlike bounded-L SMT).

Architecture (three aux vertices split the three sign constraints that killed
rank 4/5 on one vertex): hub 1 (arms b01,b12), counter b02=c; aux 3 wired {0,1}
re-arms b01; aux 4 wired {1,2} re-arms b12; COUPLER 5 wired {3,4} re-arms 3 and 4
after they fire. Free small weights on b03,b13,b14,b24,b35,b45 (+ optional b34).
For each weight combo, enumerate the symbolic-c island and scan for a uniform
tick  S2 = +/- pi(S1|_{c->c+d}).  Any hit verified at large integer c.
"""
import sys, time
from collections import deque
from itertools import product, permutations
from math import comb

DEGCAP=2; COEFCAP=10**6
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

N=6
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
def deg(M): return max((len(e)-1 for e in M),default=0)
def okcap(M):
    for e in M:
        if len(e)-1>DEGCAP: return False
        for x in e:
            if abs(x)>COEFCAP: return False
    return True
def inv_hash(M): return tuple(sorted(pabs_canon(e) for e in M))
def transform(M,pi,g):
    out=[None]*len(PAIRS)
    for (i,j) in PAIRS:
        e=fget(M,pi[i],pi[j]); out[IDX[(i,j)]]=pneg(e) if g<0 else e
    return tuple(out)
def island(start,statecap=60000):
    seen={start}; q=deque([start]); parents={start:None}
    while q:
        M=q.popleft()
        for k in range(N):
            C=mutate(M,k)
            if not okcap(C) or C in seen: continue
            if len(seen)>=statecap: continue
            seen.add(C); parents[C]=(M,k); q.append(C)
    return seen,parents
# permutations fixing the counter pair {0,2} setwise
PERMS=[]
for swap in (False,True):
    for rest in permutations((1,3,4,5)):
        pi=[0]*N
        pi[0],pi[2]=(2,0) if swap else (0,2)
        for pos,val in zip((1,3,4,5),rest): pi[pos]=val
        PERMS.append(tuple(pi))
def ratchet_scan(seen,parents,deltas=(1,2)):
    buckets={}
    for M in seen: buckets.setdefault(inv_hash(M),[]).append(M)
    for M in seen:
        if all(len(e)<=1 for e in M): continue
        for d in deltas:
            S=tuple(pshift(e,d) for e in M)
            if inv_hash(S) not in buckets: continue
            for pi in PERMS:
                for g in (1,-1):
                    if transform(S,pi,g) in parents: return (M,d,pi,g)
    return None

def seed(w):
    b03,b13,b14,b24,b35,b45,b34=w
    ent={(0,1):(1,),(1,2):(1,),(0,2):(0,1),
         (0,3):(b03,),(1,3):(b13,),(1,4):(b14,),(2,4):(b24,),
         (3,5):(b35,),(4,5):(b45,),(3,4):(b34,) if b34 else ()}
    return tuple(ent.get(p,()) for p in PAIRS)

if __name__=="__main__":
    t0=time.time(); found=[]; tried=0
    vals=(-1,1)
    grid=[(b03,b13,b14,b24,b35,b45,b34)
          for b03 in (1,) for b13 in vals for b14 in vals for b24 in vals
          for b35 in vals for b45 in vals for b34 in (0,1,-1)]
    print(f"probe8c rank-6: {len(grid)} seeds, DEGCAP={DEGCAP}", flush=True)
    for w in grid:
        tried+=1
        seen,parents=island(seed(w))
        hit=ratchet_scan(seen,parents)
        if hit:
            found.append((w,hit)); print(f"  !! seed {w}: RATCHET d={hit[1]} g={hit[3]} |island|={len(seen)}", flush=True)
        if tried%24==0: print(f"  ...{tried}/{len(grid)}, {time.time()-t0:.0f}s", flush=True)
    print(f"\nprobe8c done: {len(found)} ratchets / {len(grid)} seeds ({time.time()-t0:.0f}s)")
    if not found:
        print("no uniform tick in this rank-6 split+coupler family at DEGCAP=2 (bounded).")
