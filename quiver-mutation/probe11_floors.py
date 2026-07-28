#!/usr/bin/env python3
"""Probe 11 (Debt 2): rigorize "leaky family is decidable" via the floor structure.

Greedy Sum-b^2 descent was non-confluent (8 local minima). To make the finite
7-state core a genuine computable normal form we check:
  (i)   closed-from-below: no mutation of a global-min state lowers Sum b^2
        (=> the min-stratum is a true floor, not passed through);
  (ii)  false floors: local minima with Sum b^2 > global min (greedy traps);
  (iii) perturbation escape (Danielle's fix): from each false floor, does a
        bounded perturbation (BFS radius r) + greedy re-descent reach the global
        min? If yes for small r, descent-with-perturbation is confluent to the
        unique canonical core => decidable.
Plus: every component state descends (with perturbation) to the SAME canonical
min-stratum => the core is the normal form.
"""
from collections import deque
from itertools import permutations

N=5
IDX={}; PAIRS=[]
for i in range(N):
    for j in range(i+1,N): IDX[(i,j)]=len(PAIRS); PAIRS.append((i,j))
def mutate(t,k):
    B=[[0]*N for _ in range(N)]
    for (i,j),v in zip(PAIRS,t): B[i][j]=v; B[j][i]=-v
    Bp=[[0]*N for _ in range(N)]
    for i in range(N):
        for j in range(N):
            if i==k or j==k: Bp[i][j]=-B[i][j]
            else: Bp[i][j]=B[i][j]+(abs(B[i][k])*B[k][j]+B[i][k]*abs(B[k][j]))//2
    return tuple(Bp[i][j] for (i,j) in PAIRS)
def seed(c):
    e={(0,1):1,(1,2):1,(0,2):c,(0,3):1,(1,3):2,(1,4):2,(2,4):-1}
    return tuple(e.get(p,0) for p in PAIRS)
def sq(t): return sum(x*x for x in t)
def maxabs(t): return max(abs(x) for x in t)
PERMS=list(permutations(range(N)))
def canon(t):
    B=[[0]*N for _ in range(N)]
    for (i,j),v in zip(PAIRS,t): B[i][j]=v; B[j][i]=-v
    best=None
    for pi in PERMS:
        r=tuple(B[pi[i]][pi[j]] for (i,j) in PAIRS)
        if best is None or r<best: best=r
        rn=tuple(-x for x in r)
        if rn<best: best=rn
    return best

def component(c,cap,statecap=200000):
    s=seed(c); seen={s}; q=deque([s])
    while q:
        t=q.popleft()
        for k in range(N):
            u=mutate(t,k)
            if maxabs(u)>cap or u in seen: continue
            if len(seen)>=statecap: return seen,True
            seen.add(u); q.append(u)
    return seen,False

def neighbors(t,cap):
    out=[]
    for k in range(N):
        u=mutate(t,k)
        if maxabs(u)<=cap: out.append(u)
    return out

def greedy_descend(t,cap):
    cur=t; curs=sq(t)
    while True:
        best=None; bests=curs
        for u in neighbors(cur,cap):
            if sq(u)<bests: bests=sq(u); best=u
        if best is None: return cur
        cur=best; curs=bests

def escape(floor,cap,gmin,r=3):
    # BFS radius r from floor, greedy-descend each, min Sum b^2 reached
    seen={floor}; q=deque([(floor,0)]); best=sq(greedy_descend(floor,cap))
    while q:
        t,d=q.popleft()
        if d>=r: continue
        for u in neighbors(t,cap):
            if u in seen: continue
            seen.add(u)
            best=min(best,sq(greedy_descend(u,cap)))
            if best==gmin: return gmin,d+1
            q.append((u,d+1))
    return best,r

if __name__=="__main__":
    c=5; cap=30
    comp,cut=component(c,cap)
    print(f"T({c}) entry-<= {cap} component: {len(comp)} states{'  [cut]' if cut else ''}")
    gmin=min(sq(t) for t in comp)
    minstrat=[t for t in comp if sq(t)==gmin]
    core={canon(t) for t in minstrat}
    print(f"global min Sum b^2 = {gmin}; |min-stratum|={len(minstrat)}; |canonical core|={len(core)}")

    # (i) closed-from-below
    below=0
    for t in minstrat:
        for u in neighbors(t,cap):
            if sq(u)<gmin: below+=1
    print(f"(i) closed-from-below: {below} mutations of min-stratum go below gmin "
          f"-> {'PASS (true floor)' if below==0 else 'FAIL'}")

    # (ii) all local minima and their Sum b^2
    locmin={}
    for t in comp:
        if all(sq(u)>=sq(t) for u in neighbors(t,cap)):
            locmin.setdefault(sq(t),0); locmin[sq(t)]+=1
    print(f"(ii) local minima by Sum b^2: {dict(sorted(locmin.items()))}")
    false_floors=[t for t in comp
                  if sq(t)>gmin and all(sq(u)>=sq(t) for u in neighbors(t,cap))]
    print(f"     false floors (local min > gmin): {len(false_floors)} states, "
          f"canonically {len({canon(t) for t in false_floors})}")

    # (iii) perturbation escape from each false-floor canonical class
    if false_floors:
        reps={}
        for t in false_floors: reps.setdefault(canon(t),t)
        worst_r=0; allok=True
        for cn,t in reps.items():
            reached,rr=escape(t,cap,gmin,r=3)
            worst_r=max(worst_r,rr)
            if reached!=gmin: allok=False
            print(f"     false-floor {cn[:4]}...: perturbation radius {rr} -> reaches gmin? {reached==gmin}")
        print(f"(iii) perturbation escape: {'ALL false floors escape to gmin' if allok else 'SOME trapped'} "
              f"(max radius {worst_r})")
    else:
        print("(iii) no false floors -> greedy descent already confluent to the floor")

    # (iv) does every state descend (with radius-1 perturbation) to the SAME canonical core?
    import random; random.seed(0)
    sample=random.sample(list(comp), min(3000,len(comp)))
    landed=set()
    for t in sample:
        f=greedy_descend(t,cap)
        if sq(f)>gmin:  # trapped: perturb once + descend
            cand=[greedy_descend(u,cap) for u in neighbors(f,cap)]
            cand=[x for x in cand if sq(x)==gmin]
            if cand: f=cand[0]
        landed.add(canon(f))
    print(f"(iv) 3000 sampled states -> {len(landed)} distinct canonical floors reached; "
          f"subset of core: {landed<=core}")
    print(f"\nverdict: floor is {'a genuine computable normal form (decidable)' if below==0 and (not false_floors or allok) else 'not yet closed'}")
