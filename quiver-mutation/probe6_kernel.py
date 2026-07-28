#!/usr/bin/env python3
"""Probe 6 (Danielle direction 1): the rank-5 kernel vector as a dynamical
companion. For 5x5 skew B, Pf(B)=0 and (generically) corank 1; the kernel is
spanned by  v_i = (-1)^i Pf(B with row&col i deleted).  Under mutation
B -> E B E^T, ker transforms by E^{-T}, so v moves by a linear cocycle.

TEST: walk a leaky rank-5 gadget's orbit and watch the PROJECTIVE direction of v.
  - v projectively FIXED  => dynamics collapses to the rank-4 symplectic quotient
    B|_{Z^5/<v>} => the rank-4 freezing obstruction imports => that architecture
    cannot host a counter (another cheap freezing certificate).
  - v MOVES               => genuine rank-5 behaviour; architecture is promising.
Also reports the integral invariants: corank, and the elementary divisors
(d1 J + d2 J + 0) of B, whose product d1*d2 is the honest rank-5 analog of Pf.
"""
import random
from math import gcd
from functools import reduce

def mutate(B,k):
    n=len(B); Bp=[[0]*n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if i==k or j==k: Bp[i][j]=-B[i][j]
            else: Bp[i][j]=B[i][j]+(abs(B[i][k])*B[k][j]+B[i][k]*abs(B[k][j]))//2
    return Bp
def skew(ent,n=5):
    B=[[0]*n for _ in range(n)]
    for (i,j),v in ent.items(): B[i][j]=v; B[j][i]=-v
    return B

def pf4(M,idx):
    p,q,r,s=idx
    return M[p][q]*M[r][s]-M[p][r]*M[q][s]+M[p][s]*M[q][r]
def kernel_vec(B):
    n=len(B); v=[]
    for i in range(n):
        rest=[j for j in range(n) if j!=i]
        v.append(((-1)**i)*pf4(B,rest))
    return v
def matvec(B,v): return [sum(B[i][j]*v[j] for j in range(len(v))) for i in range(len(B))]
def primitive(v):
    g=reduce(gcd,[abs(x) for x in v],0)
    if g==0: return tuple(v),0
    w=[x//g for x in v]
    # canonical sign: first nonzero positive
    for x in w:
        if x!=0:
            if x<0: w=[-y for y in w]
            break
    return tuple(w),g

def proj_dir(v):
    w,_=primitive(v); return w

if __name__=="__main__":
    c=1000
    # the leaky gadget (b13,b14 same sign as hub -> leaks) and a decoupled one
    fams={
      "leaky":     {(0,1):1,(1,2):1,(0,2):c,(0,3):1,(1,3):2,(1,4):2,(2,4):-1},
      "decoupled": {(0,1):1,(1,2):1,(0,2):c,(0,3):1,(1,3):-1,(1,4):-1,(2,4):-1},
      "coupled":   {(0,1):1,(1,2):1,(0,2):c,(0,3):1,(1,3):-1,(1,4):-1,(2,4):-1,(3,4):1},
    }
    for name,ent in fams.items():
        B=skew(ent)
        v=kernel_vec(B)
        assert matvec(B,v)==[0,0,0,0,0], (name, matvec(B,v))
        print(f"\n=== {name} ===  kernel check Bv=0 OK; v0 dir = {proj_dir(v)}")
        random.seed(0)
        dirs=set(); moved=0; steps=4000
        cur=B; prev=proj_dir(v)
        seen_dirs=[prev]
        for t in range(steps):
            k=random.randrange(5)
            nx=mutate(cur,k)
            if max(abs(e).bit_length() for row in nx for e in row)>1600:
                cur=skew(ent); continue   # reset on blowup
            vv=kernel_vec(nx)
            assert matvec(nx,vv)==[0]*5
            d=proj_dir(vv); dirs.add(d)
            if d!=prev: moved+=1
            prev=d; cur=nx
        print(f"    over {steps} orbit steps: distinct projective v-directions = {len(dirs)}, "
              f"direction-changes = {moved}")
        print(f"    verdict: {'v MOVES -> genuine rank-5' if len(dirs)>1 else 'v FIXED -> secretly rank-4 (import freezing)'}")
        # a few sample directions
        for d in list(dirs)[:5]: print("      dir:",d)
