#!/usr/bin/env python3
"""Probe 16 (Danielle #1): mine the past-the-invariant-ceiling region and run the
descent-core diagnostic on it. Layer-3 (undecidability) needs BOTH invariant
failure AND a non-recognizable core; the invariants give us the first condition
for free.

By Neville (mutation-acyclic => totally proper), `proper is False` CERTIFIES
mutation-cyclic. We generate rank-5 quivers, keep the certified-mutation-cyclic
ones (proper=False, acyclic=False, alexander=False = fully past the ceiling), and
for each run the min-Sum-b^2 descent-core diagnostic across growing caps. If every
core stabilizes => strong evidence for the decidable lean (the arsenal's blind
spot is descent-visible). A core that keeps GROWING with the cap = the target.
Run: /run/current-system/sw/bin/python3 probe16_unknown.py
"""
import sys, random, itertools
from collections import deque, Counter
sys.path.insert(0,'quiver-mutation-database')
from quiver import Quiver

N=5
PAIRS=[(i,j) for i in range(N) for j in range(i+1,N)]
def toM(t):
    M=[[0]*N for _ in range(N)]
    for (i,j),v in zip(PAIRS,t): M[i][j]=v; M[j][i]=-v
    return M
def up(M): return tuple(M[i][j] for (i,j) in PAIRS)
def mutate(t,k):
    M=toM(t); Mp=[[0]*N for _ in range(N)]
    for i in range(N):
        for j in range(N):
            if i==k or j==k: Mp[i][j]=-M[i][j]
            else: Mp[i][j]=M[i][j]+(abs(M[i][k])*M[k][j]+M[i][k]*abs(M[k][j]))//2
    return up(Mp)
def sq(t): return sum(x*x for x in t)
def mx(t): return max((abs(x) for x in t),default=0)
def connected(t):
    M=toM(t); seen={0}; st=[0]
    while st:
        x=st.pop()
        for y in range(N):
            if M[x][y]!=0 and y not in seen: seen.add(y); st.append(y)
    return len(seen)==N
PERMS=list(itertools.permutations(range(N)))
def canon(t):
    M=toM(t); best=None
    for pi in PERMS:
        r=tuple(M[pi[i]][pi[j]] for (i,j) in PAIRS)
        if best is None or r<best: best=r
        rn=tuple(-x for x in r)
        if rn<best: best=rn
    return best

def core_profile(t0, caps=(15,25,40,60)):
    prev=None; profile=[]
    for cap in caps:
        seen={t0}; q=deque([t0]); cut=False
        while q:
            t=q.popleft()
            for k in range(N):
                u=mutate(t,k)
                if mx(u)>cap or u in seen: continue
                if len(seen)>=120000: cut=True; break
                seen.add(u); q.append(u)
            if cut: break
        gmin=min(sq(t) for t in seen)
        core=frozenset(canon(t) for t in seen if sq(t)==gmin)
        grew = None if prev is None else (core!=prev)
        profile.append((cap,len(seen),gmin,len(core),grew,cut))
        prev=core
    return profile

def is_past_ceiling(t):
    Q=Quiver(toM(t))
    try:
        if Q.acyclic(): return False
        if Q.proper() is not False: return False   # totally proper => mutation-acyclic possible; skip
        if Q.alexanderPolynomial() is not False: return False
    except Exception:
        return False
    return True

if __name__=="__main__":
    random.seed(20260705)
    print("generating rank-5 quivers, filtering to certified-mutation-cyclic (past ceiling)...", flush=True)
    cyclic=[]
    tries=0
    # bias toward abundant/cyclic: entries in wider range
    while len(cyclic)<40 and tries<20000:
        tries+=1
        rng=random.choice([2,3])
        t=tuple(random.randint(-rng,rng) for _ in PAIRS)
        if not connected(t): continue
        if is_past_ceiling(t): cyclic.append(t)
    print(f"found {len(cyclic)} certified-mutation-cyclic rank-5 quivers in {tries} tries\n", flush=True)

    growing=[]; stable=0; coresizes=Counter()
    for idx,t in enumerate(cyclic):
        prof=core_profile(t)
        finalcore=prof[-1][3]
        grew_ever=any(g for (_,_,_,_,g,_) in prof if g is not None)
        coresizes[finalcore]+=1
        tag = "GROWING-CORE" if grew_ever else "stable"
        if grew_ever: growing.append((t,prof))
        else: stable+=1
        comp=[p[1] for p in prof]; cores=[p[3] for p in prof]; gmin=prof[0][2]
        print(f"[{idx:2d}] gmin={gmin:4d} comp={comp} core-sizes={cores} -> {tag}"
              f"{'  [cut]' if any(p[5] for p in prof) else ''}", flush=True)

    print(f"\n===== SUMMARY: {len(cyclic)} certified-mutation-cyclic quivers =====")
    print(f"  stable core: {stable}   growing core: {len(growing)}")
    print(f"  final core-size distribution: {dict(sorted(coresizes.items()))}")
    if growing:
        print("  *** GROWING-CORE candidates (layer-3 leads): ***")
        for t,prof in growing[:5]:
            print(f"    {t}: {[(p[0],p[3]) for p in prof]}")
    else:
        print("  ALL cores stabilized -> decidable lean corroborated past the invariant ceiling.")
