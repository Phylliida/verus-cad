#!/usr/bin/env python3
"""Probe 7 (Danielle direction 2): is the rank-5 counter DEAD? Try to CONNECT
T(5) and T(6). A collision => the two counter values are in the same mutation
class (up to the gadget's relabeling/sign symmetry) => the family cannot encode a
counter. Persistent non-collision under bidirectional search = best evidence of
separation.

(a) Greedy Sum b^2 descent from both seeds (+ random restarts): compare the
    canonicalized floor sets.
(b) Bidirectional entry-capped island enumeration: fully enumerate the |entry|<=CAP
    component of each orbit, canonicalize under S_5 x {global sign}, check overlap.
    Collision at any CAP is decisive; no collision is bounded evidence.
"""
import sys, random
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
def sq(B): return sum(B[i][j]*B[i][j] for (i,j) in PAIRS)
def maxabs(B): return max(abs(B[i][j]) for (i,j) in PAIRS)

PERMS=list(permutations(range(N)))
def canon(B):
    """min upper-tuple over vertex relabelings and global sign."""
    best=None
    for pi in PERMS:
        t=tuple(B[pi[i]][pi[j]] if pi[i]<pi[j] else -B[pi[j]][pi[i]] for (i,j) in PAIRS)
        if best is None or t<best: best=t
        tn=tuple(-x for x in t)
        if tn<best: best=tn
    return best
def from_up(t):
    B=[[0]*N for _ in range(N)]
    for (i,j),v in zip(PAIRS,t): B[i][j]=v; B[j][i]=-v
    return B

FAM=lambda c: {(0,1):1,(1,2):1,(0,2):c,(0,3):1,(1,3):2,(1,4):2,(2,4):-1}  # leaky

# ---------- (a) greedy descent ----------
def descend(B):
    cur=B; curs=sq(B)
    while True:
        best=None; bests=curs
        for k in range(N):
            nb=mutate(cur,k); s=sq(nb)
            if s<bests: bests=s; best=nb
        if best is None: return cur
        cur=best; curs=bests
def descent_floors(seed, restarts=400, walk=8, seed_rng=0):
    random.seed(seed_rng)
    floors={}
    for _ in range(restarts):
        B=skew(seed)
        for _ in range(random.randrange(walk+1)):
            B=mutate(B,random.randrange(N))
            if maxabs(B)>10**6: B=skew(seed); break
        f=descend(B); floors[canon(f)]=sq(f)
    return floors

# ---------- (b) bidirectional island ----------
def island_canon(seed, cap, statecap=200000):
    start=up(skew(seed)); seen={start}; q=deque([start]); canons={canon(skew(seed))}
    while q:
        B=from_up(q.popleft())
        for k in range(N):
            C=mutate(B,k)
            if maxabs(C)>cap: continue
            t=up(C)
            if t in seen: continue
            if len(seen)>=statecap: return canons, seen, True
            seen.add(t); canons.add(canon(C)); q.append(t)
    return canons, seen, False

if __name__=="__main__":
    print("=== (a) greedy Sum-b^2 descent floors ===")
    f5=descent_floors(FAM(5)); f6=descent_floors(FAM(6))
    print(f"  T(5): {len(f5)} distinct canonical floors, min Sum b^2 = {min(f5.values())}")
    print(f"  T(6): {len(f6)} distinct canonical floors, min Sum b^2 = {min(f6.values())}")
    shared=set(f5)&set(f6)
    print(f"  shared floors (up to relabel/sign): {len(shared)}  -> "
          f"{'CONNECTED (counter dead)' if shared else 'no shared floor (descent inconclusive)'}")

    print("\n=== (b) bidirectional entry-capped island collision ===")
    for cap in (12, 20, 30, 45):
        c5,s5,cut5=island_canon(FAM(5),cap)
        c6,s6,cut6=island_canon(FAM(6),cap)
        rawcut = cut5 or cut6
        # raw (exact-matrix) overlap = strict T5~T6; canonical overlap = up to symmetry
        rawshare=len(s5 & s6)
        canshare=len(c5 & c6)
        print(f"  cap={cap:3d}: |isl5|={len(s5)} |isl6|={len(s6)}  "
              f"raw-overlap={rawshare}  canon-overlap={canshare}"
              f"{'  [statecap hit]' if rawcut else ''}")
        if canshare:
            print(f"           *** COLLISION: T(5) ~ T(6) up to symmetry -> counter DEAD ***")
            break
    else:
        print("  no collision up to cap 45 -> bounded evidence T(5) NOT~ T(6) (separation)")
