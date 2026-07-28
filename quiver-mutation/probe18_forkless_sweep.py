#!/usr/bin/env python3
"""Probe 18 (the positive-campaign experiment): forkless-part fraction sweep over
CERTIFIED-mutation-cyclic quivers, hunting an infinite forkless part.

By Neville (mutation-acyclic => totally proper), `proper is False` CERTIFIES
mutation-cyclic (past the invariant ceiling). For each such quiver we measure the
forkless part (Warkentin) across growing caps and track the fraction
forkless/component:
  fraction -> 0        => FINITE forkless part  => fork-descent decidable
  fraction stays >~c   => candidate INFINITE forkless part => non-recognizable
                          substrate (the only place undecidability can live).
Reports the fraction trend per quiver; flags any non-declining one for follow-up.
"""
import sys, random, itertools
sys.path.insert(0,'.'); sys.path.insert(0,'quiver-mutation-database')
import probe17_forkless as P
from quiver import Quiver

N=5
PAIRS=[(i,j) for i in range(N) for j in range(i+1,N)]
def toM(t):
    M=[[0]*N for _ in range(N)]
    for (i,j),v in zip(PAIRS,t): M[i][j]=v; M[j][i]=-v
    return M
def connected(t):
    M=toM(t); seen={0}; st=[0]
    while st:
        x=st.pop()
        for y in range(N):
            if M[x][y]!=0 and y not in seen: seen.add(y); st.append(y)
    return len(seen)==N
def certified_mut_cyclic(t):
    Q=Quiver(toM(t))
    try:
        return (not Q.acyclic()) and (Q.proper() is False)
    except Exception:
        return False

def trend(fracs):
    """classify the fraction sequence."""
    # declining if last is a good bit below the max; flat/rising = candidate
    mx=max(fracs); last=fracs[-1]; first=fracs[0]
    if last <= 0.5*mx and last < 0.06: return "declining->0 (finite)"
    if last >= 0.85*first and last > 0.05: return "*** NON-DECLINING (candidate infinite) ***"
    return "declining (finite, slow)"

if __name__=="__main__":
    random.seed(20260705)
    print("generating certified-mutation-cyclic (proper=False) rank-5 quivers...", flush=True)
    fam=[]; tries=0
    while len(fam)<25 and tries<40000:
        tries+=1
        rng=random.choice([2,2,3])
        t=tuple(random.randint(-rng,rng) for _ in PAIRS)
        if not connected(t): continue
        if certified_mut_cyclic(t): fam.append(t)
    print(f"found {len(fam)} in {tries} tries\n", flush=True)

    caps=(8,16,26,38,52)
    candidates=[]
    for idx,t in enumerate(fam):
        prof=P.forkless_profile(toM(t),N,caps=caps,statecap=200000)
        comp=[p[1] for p in prof]; fl=[p[2] for p in prof]
        fr=[f/c for f,c in zip(fl,comp)]
        cut=any(p[4] for p in prof)
        tg=trend(fr)
        if "NON-DECLINING" in tg: candidates.append((t,prof,fr))
        print(f"[{idx:2d}] comp={comp} forkless={fl} frac={[f'{x:.3f}' for x in fr]} "
              f"-> {tg}{'  [cut]' if cut else ''}", flush=True)

    print(f"\n===== SUMMARY: {len(fam)} certified-mutation-cyclic quivers =====")
    if candidates:
        print(f"  *** {len(candidates)} NON-DECLINING (candidate infinite forkless) — the leads: ***")
        for t,prof,fr in candidates:
            print(f"    {t}: fractions={[f'{x:.3f}' for x in fr]}")
    else:
        print("  ALL forkless fractions decline -> finite forkless part everywhere")
        print("  => fork-descent decidability holds across the certified-mutation-cyclic sample.")
        print("  => decidable lean corroborated on the RIGHT object (forkless part).")
