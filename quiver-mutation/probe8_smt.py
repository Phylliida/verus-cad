#!/usr/bin/env python3
"""Probe 8 (Danielle direction 3): SMT search for a rank-6 uniform tick.

Key simplification: the word never mutates the counter endpoints {0,2}, so the
counter entry b_02 never feeds any correction -- it is a pure ACCUMULATOR. Drop
it from the state and track only the net correction to (0,2). Then every state
variable is small-bounded (bit-blastable), and the tick is:

  find aux wiring on {3,4,5} + a word w (|w|<=L over {1,3,4,5}) that RESTORES all
  14 non-counter entries AND accumulates net correction +delta into (0,2).

That single tick = the Minsky increment. UNSAT at generous bounds = a bounded
freezing-style result. rank 6 gives three aux vertices to split the three sign
constraints that killed rank 4/5 when concentrated on one vertex.

Run: /home/bepis/.venv/bin/python3 probe8_smt.py [L] [delta]
"""
import sys, time
from z3 import *

N=6
PAIRS=[(i,j) for i in range(N) for j in range(i+1,N)]
STATE=[p for p in PAIRS if p!=(0,2)]        # 14 tracked entries
PI={p:idx for idx,p in enumerate(STATE)}
def pair(i,j): return (i,j) if i<j else (j,i)

L     = int(sys.argv[1]) if len(sys.argv)>1 else 12
DELTA = int(sys.argv[2]) if len(sys.argv)>2 else 1
M     = 3
KSET  = [1,3,4,5]

s=Solver(); s.set("timeout", 1000*60*25)
B=[[Int(f"b_{t}_{i}{j}") for (i,j) in STATE] for t in range(L+1)]
A=[Int(f"a_{t}") for t in range(L+1)]        # accumulator into (0,2)
def get(t,i,j):
    if i==j: return IntVal(0)
    p=pair(i,j)
    if p==(0,2): return IntVal(0)            # never accessed (k never in {0,2})
    v=B[t][PI[p]]
    return v if i<j else -v

# initial: hub armed, aux free in [-2,2]
def setB0(i,j,val): s.add(B[0][PI[pair(i,j)]]==val)
setB0(0,1,1); setB0(1,2,1)
for p in STATE:
    if p in [(0,1),(1,2)]: continue
    s.add(B[0][PI[p]]>=-2, B[0][PI[p]]<=2)
s.add(A[0]==0)

# word
K=[Int(f"k_{t}") for t in range(L)]
for t in range(L):
    s.add(Or([K[t]==kk for kk in KSET]))
    if t>0: s.add(K[t]!=K[t-1])
s.add(K[0]==1)                                # fire hub first (symmetry break)

def half(e):
    h=Int(f"h_{half.n}"); half.n+=1; s.add(2*h==e); return h
half.n=0

for t in range(L):
    # 14 state updates
    for p in STATE:
        i,j=p; idx=PI[p]; expr=None
        for kk in reversed(KSET):
            if kk==i or kk==j:
                upd=-B[t][idx]
            else:
                x=get(t,i,kk); y=get(t,kk,j)
                upd=B[t][idx]+half(Abs(x)*y + x*Abs(y))
            expr = upd if expr is None else If(K[t]==kk, upd, expr)
        s.add(B[t+1][idx]==expr)
        s.add(B[t+1][idx]>=-M, B[t+1][idx]<=M)
    # accumulator: correction into (0,2) from mutation at kk (kk never 0/2)
    aexpr=None
    for kk in reversed(KSET):
        x=get(t,0,kk); y=get(t,kk,2)
        c=half(Abs(x)*y + x*Abs(y))
        aexpr = c if aexpr is None else If(K[t]==kk, c, aexpr)
    s.add(A[t+1]==A[t]+aexpr)

# goal: restore all 14 entries, accumulate +DELTA
for p in STATE: s.add(B[L][PI[p]]==B[0][PI[p]])
s.add(A[L]==DELTA)

print(f"probe8 SMT: rank 6, L={L}, delta={DELTA}, M={M}, K in {KSET}", flush=True)
t0=time.time(); r=s.check()
print(f"result: {r}  ({time.time()-t0:.0f}s)", flush=True)
if r==sat:
    m=s.model()
    print("*** TICK FOUND ***")
    print(" aux wiring:", {f"b{i}{j}": m[B[0][PI[(i,j)]]].as_long() for (i,j) in STATE})
    print(" word:", [m[K[t]].as_long() for t in range(L)])
    print(" accumulator:", [m[A[t]].as_long() for t in range(L+1)])
elif r==unsat:
    print(f"UNSAT: no rank-6 tick at L={L}, M={M}, K={KSET} (bounded freezing result).")
else:
    print("UNKNOWN (timeout).")
