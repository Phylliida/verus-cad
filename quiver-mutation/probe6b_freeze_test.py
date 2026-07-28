#!/usr/bin/env python3
"""Probe 6b: is a given rank-5 gadget family FROZEN or a COUNTER CANDIDATE?

Sample mutation pairs (B, mu_k B) from walks along the family's orbit for many
counter values c, then find the space of signed-monomial invariants (kernel of
the constraint matrix mod p). If some invariant takes different values on T(5)
and T(6), the two counter values lie in DIFFERENT orbits (frozen-like, no counter
tick between them). If ALL invariants up to degree d agree on T(5),T(6), the
family is a counter CANDIDATE at that degree (worth deeper search).

This is the reversibility-consistent form of the "Lyapunov" idea: mutation is an
involution, so a one-sided Delta f >= 0 on every move forces Delta f = 0 (a true
invariant). Hence the honest per-family certificate is the invariant search here,
not a strict-on-fire monotone (which is infeasible for a reversible system).
"""
import numpy as np, random, sys

P=2147483647
N=5
IDX={}; PAIRS=[]
for i in range(N):
    for j in range(i+1,N): IDX[(i,j)]=len(PAIRS); PAIRS.append((i,j))
NV=len(PAIRS)  # 10

def mutate(B,k):
    n=N; Bp=[[0]*n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if i==k or j==k: Bp[i][j]=-B[i][j]
            else: Bp[i][j]=B[i][j]+(abs(B[i][k])*B[k][j]+B[i][k]*abs(B[k][j]))//2
    return Bp
def skew(ent):
    B=[[0]*N for _ in range(N)]
    for (i,j),v in ent.items(): B[i][j]=v; B[j][i]=-v
    return B
def upper(B): return tuple(B[i][j] for (i,j) in PAIRS)

def exp_tuples(nv,d):
    out=[]
    def rec(pos,rem,cur):
        if pos==nv: out.append(tuple(cur)); return
        for e in range(rem+1): cur.append(e); rec(pos+1,rem-e,cur); cur.pop()
    rec(0,d,[]); return out
def signed_features(nv,d):
    feats=[]
    for t in exp_tuples(nv,d):
        sup=[i for i in range(nv) if t[i]>=1]
        for bits in range(1<<len(sup)):
            s=[0]*nv
            for b,i in enumerate(sup): s[i]=(bits>>b)&1
            feats.append((t,tuple(s)))
    return feats
def feat_matrix(points,feats,p):
    M=len(points); absA=np.array([[abs(x)%p for x in pt] for pt in points],dtype=np.int64)
    sgnA=np.array([[(0 if x==0 else(1 if x>0 else -1)) for x in pt] for pt in points],dtype=np.int64)
    maxe=max(max(t) for t,s in feats)
    pw=np.ones((M,NV,maxe+1),dtype=np.int64)
    for e in range(1,maxe+1): pw[:,:,e]=(pw[:,:,e-1]*absA)%p
    R=np.empty((M,len(feats)),dtype=np.int64)
    for j,(t,s) in enumerate(feats):
        col=np.ones(M,dtype=np.int64); sg=np.ones(M,dtype=np.int64)
        for v in range(NV):
            if t[v]: col=(col*pw[:,v,t[v]])%p
            if s[v]: sg=sg*sgnA[:,v]
        R[:,j]=(col*sg)%p
    return R
def rref(A,p):
    A=A.copy()%p; rows,cols=A.shape; piv=[]; r=0
    for c in range(cols):
        nz=np.nonzero(A[r:,c])[0]
        if nz.size==0: continue
        i=r+int(nz[0])
        if i!=r: A[[r,i]]=A[[i,r]]
        A[r]=(A[r]*pow(int(A[r,c]),p-2,p))%p
        col=A[:,c].copy(); col[r]=0; nzr=np.nonzero(col)[0]
        if nzr.size: A[nzr]=(A[nzr]-col[nzr,None]*A[r][None,:])%p
        piv.append(c); r+=1
        if r==rows: break
    return A,piv,r
def kernel_basis(A,piv,cols,p):
    ps=set(piv); free=[c for c in range(cols) if c not in ps]
    K=np.zeros((len(free),cols),dtype=np.int64)
    for idx,f in enumerate(free):
        K[idx,f]=1
        for i,pc in enumerate(piv): K[idx,pc]=(-int(A[i,f]))%p
    return K
def matmod(A,B,p):
    Bh,Bl=B>>16,B&0xFFFF
    return ((A@Bl)%p+(((A@Bh)%p)<<16))%p

def kernel(pairs,feats,p):
    xs=[x for x,y in pairs]; ys=[y for x,y in pairs]; nc=len(feats)
    n1=min(len(pairs),int(2.5*nc)+50)
    C=(feat_matrix(ys[:n1],feats,p)-feat_matrix(xs[:n1],feats,p))%p
    A,piv,_=rref(C,p); K=kernel_basis(A,piv,nc,p)
    i=n1
    while i<len(pairs) and K.shape[0]>0:
        j=min(len(pairs),i+4000)
        C=(feat_matrix(ys[i:j],feats,p)-feat_matrix(xs[i:j],feats,p))%p
        Rr=matmod(C,K.T%p,p)
        if np.any(Rr):
            A2,p2,_=rref(Rr,p); K=matmod(kernel_basis(A2,p2,K.shape[0],p),K%p,p)
        i=j
    return K
def separates(K,feats,B1,B2,p):
    F=feat_matrix([upper(B1),upper(B2)],feats,p); s=(F[1]-F[0])%p
    return bool(np.any(matmod(K%p,s[:,None],p)))

def sample_pairs(ent_fn, cs, walks=40, steps=60, bit=1400):
    pairs=[]; seen=set()
    random.seed(1)
    for c in cs:
        for _ in range(walks):
            B=skew(ent_fn(c))
            for _ in range(steps):
                k=random.randrange(N); B1=mutate(B,k)
                if max(abs(e).bit_length() for row in B1 for e in row)>bit: break
                key=(upper(B),upper(B1)) if upper(B)<=upper(B1) else (upper(B1),upper(B))
                if key not in seen: seen.add(key); pairs.append((upper(B),upper(B1)))
                B=B1
    return pairs

FAMS={
 "twin_hub_rank5pad": lambda c: {(0,1):1,(1,2):1,(0,2):c,(0,3):1,(3,2):1},  # rank-4 frozen, padded
 "leaky":     lambda c: {(0,1):1,(1,2):1,(0,2):c,(0,3):1,(1,3):2,(1,4):2,(2,4):-1},
 "decoupled": lambda c: {(0,1):1,(1,2):1,(0,2):c,(0,3):1,(1,3):-1,(1,4):-1,(2,4):-1},
 "coupled":   lambda c: {(0,1):1,(1,2):1,(0,2):c,(0,3):1,(1,3):-1,(1,4):-1,(2,4):-1,(3,4):1},
}

if __name__=="__main__":
    for name,fn in FAMS.items():
        pairs=sample_pairs(fn,list(range(3,13)))
        print(f"\n=== {name} ===  {len(pairs)} sampled orbit pairs")
        for d in (2,3):
            feats=signed_features(NV,d)
            K=kernel(pairs,feats,P)
            sep=separates(K,feats,skew(fn(5)),skew(fn(6)),P)
            print(f"  signed deg<={d}: {len(feats)} feats, invariant-space dim {K.shape[0]}, "
                  f"separates T(5)/T(6): {sep}  -> {'FROZEN-like' if sep else 'counter-candidate@deg%d'%d}")
            if sep: break
