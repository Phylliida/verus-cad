#!/usr/bin/env python3
"""Probe 14: build Fomin's long-mutation-cycle quivers (arXiv 2304.11505,
Thm 'Summary') and verify the cycle closes -- our explicit FZ-FAILURE substrate.

Construction: n>=4, k>=1, parameters q_{ij}>=2 (1<=i<j<=n).
  p_0=1, p_1=q_12, p_{j+1}=q_12 p_j - p_{j-1}.
  B(Q)_{ij} (i<j):
    i=1, 3<=j<=n-1 : -p_{2k-2} q_{1j} - p_{2k-1} q_{2j}
    i=2, 3<=j<=n-1 :  p_{2k-1} q_{1j} + p_{2k} q_{2j}
    else           :  q_{ij}
  Mutation cycle (length n+4k), 1-indexed vertices:
    n, [1,2]*k, n-1,n-2,...,2,1, [2,1]*k
  Claim: applying it returns Q; all n+4k quivers distinct; not paved by cycles <=4k.
"""
import sys

def mutate(B,k):
    n=len(B); Bp=[[0]*n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if i==k or j==k: Bp[i][j]=-B[i][j]
            else: Bp[i][j]=B[i][j]+(abs(B[i][k])*B[k][j]+B[i][k]*abs(B[k][j]))//2
    return Bp

def fomin_B(n,k,q):
    """q: dict {(i,j):val} 1-indexed i<j. Returns 0-indexed B."""
    # recurrence p (needs up to p_{2k})
    p=[1, q[(1,2)]]
    while len(p)<=2*k: p.append(q[(1,2)]*p[-1]-p[-2])
    B=[[0]*n for _ in range(n)]
    for i in range(1,n+1):
        for j in range(i+1,n+1):
            if i==1 and 3<=j<=n-1:
                v=-p[2*k-2]*q[(1,j)]-p[2*k-1]*q[(2,j)]
            elif i==2 and 3<=j<=n-1:
                v= p[2*k-1]*q[(1,j)]+p[2*k]*q[(2,j)]
            else:
                v=q[(i,j)]
            B[i-1][j-1]=v; B[j-1][i-1]=-v
    return B

def cycle_seq(n,k):
    seq=[n]
    seq+= [1,2]*k
    seq+= list(range(n-1,0,-1))     # n-1,...,1
    seq+= [2,1]*k
    return [x-1 for x in seq]        # 0-indexed

def apply_seq(B,seq):
    states=[[row[:] for row in B]]
    cur=B
    for k in seq:
        cur=mutate(cur,k); states.append([row[:] for row in cur])
    return states

def eq(A,B): return all(A[i][j]==B[i][j] for i in range(len(A)) for j in range(len(A)))

def test(n,k,q,verbose=False):
    B=fomin_B(n,k,q)
    seq=cycle_seq(n,k)
    # no-immediate-repeat check
    reps=any(seq[i]==seq[i+1] for i in range(len(seq)-1)) or seq[0]==seq[-1]
    states=apply_seq(B,seq)
    closes= eq(states[-1],B)
    # distinctness of the n+4k quivers on the cycle (states[0..N-1], states[N]==states[0])
    up=lambda M: tuple(M[i][j] for i in range(n) for j in range(i+1,n))
    distinct=len({up(s) for s in states[:-1]})==len(states)-1
    maxent=max(abs(states[t][i][j]) for t in range(len(states)) for i in range(n) for j in range(n))
    print(f"n={n} k={k}: cycle len={len(seq)} (=n+4k={n+4*k}) closes={closes} "
          f"all-distinct={distinct} no-immediate-repeat={not reps} max|entry|={maxent}")
    if verbose:
        print(f"  seq(0-idx)={seq}")
        print(f"  B(Q) row0={B[0]}")
    return closes and distinct

if __name__=="__main__":
    print("=== Fomin construction: closure + distinctness ===")
    # n=4,k=1 simplest, all q=2
    ok=True
    q6={(i,j):2 for i in range(1,5) for j in range(i+1,5)}
    ok&=test(4,1,q6,verbose=True)
    # n=4,k=2,3
    ok&=test(4,2,q6)
    ok&=test(4,3,q6)
    # n=5, k=1..4, all q=2
    q10={(i,j):2 for i in range(1,6) for j in range(i+1,6)}
    for k in (1,2,3,5,10):
        ok&=test(5,k,q10)
    # n=5, k=2 with varied q>=2
    qv={(1,2):3,(1,3):2,(1,4):4,(1,5):2,(2,3):2,(2,4):3,(2,5):2,(3,4):2,(3,5):5,(4,5):2}
    ok&=test(5,2,qv,verbose=True)
    # n=6, k=1
    q15={(i,j):2 for i in range(1,7) for j in range(i+1,7)}
    ok&=test(6,1,q15)
    print(f"\nALL PASS: {ok}")
