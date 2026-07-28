#!/usr/bin/env python3
"""Probe 13: hunt for FZ-FAILURE (long cycles) = the machine substrate.

Uses the validated g-vector cluster-exchange-graph tool (probe12). For each
family, span-rank < cycle-dim (a GAP) means squares+pentagons do NOT generate the
cycle space => independent long cycles => candidate instruction material. Any GAP
is re-checked at a higher cap: a real FZ-failure GROWS with the cap; a boundary
artifact stays fixed. Baseline: leaky family SPANS (gap 0) despite capping.
"""
import sys, random
import probe12_gvec as P

def B_from(edges,n):
    B=[[0]*n for _ in range(n)]
    for (i,j),v in edges.items(): B[i][j]=v; B[j][i]=-v
    return B
def cyc(n,w=1):   # 0->1->...->(n-1)->0
    e={}
    for i in range(n): e[(min(i,(i+1)%n),max(i,(i+1)%n))]= w if i<(i+1)%n else -w
    return B_from(e,n)

FAMILIES=[]
def add(name,B,n): FAMILIES.append((name,B,n))

# --- rank 3 (sanity: Markov, cyclic) ---
add("R3 Markov(2,2,2)", B_from({(0,1):2,(1,2):2,(0,2):-2},3),3)
add("R3 cyclic(1,1,1)", B_from({(0,1):1,(1,2):1,(0,2):-1},3),3)
add("R3 (3,3,3)", B_from({(0,1):3,(1,2):3,(0,2):-3},3),3)
# --- rank 4 ---
add("R4 4-cycle w1", cyc(4,1),4)
add("R4 4-cycle w2", cyc(4,2),4)
add("R4 Markov+tail", B_from({(0,1):2,(1,2):2,(0,2):-2,(2,3):1},4),4)
add("R4 double-tri", B_from({(0,1):2,(1,2):2,(0,2):-2,(1,3):1,(2,3):1},4),4)
# --- rank 5 ---
add("R5 5-cycle w1", cyc(5,1),5)
add("R5 5-cycle w2", cyc(5,2),5)
add("R5 Markov+chain", B_from({(0,1):2,(1,2):2,(0,2):-2,(2,3):1,(3,4):1},5),5)
add("R5 two-tri share", B_from({(0,1):2,(1,2):2,(0,2):-2,(2,3):2,(3,4):2,(2,4):-2},5),5)
add("R5 wheel", B_from({(0,1):1,(1,2):1,(2,3):1,(3,4):1,(0,4):-1,(0,2):1,(0,3):1},5),5)
add("R5 dbl-cycle", cyc(5,2),5)
# --- rank 6 ---
add("R6 6-cycle w1", cyc(6,1),6)
add("R6 6-cycle w2", cyc(6,2),6)
add("R6 two Markov coupled", B_from({(0,1):2,(1,2):2,(0,2):-2,(3,4):2,(4,5):2,(3,5):-2,(2,3):1},6),6)
add("R6 two Markov strong", B_from({(0,1):2,(1,2):2,(0,2):-2,(3,4):2,(4,5):2,(3,5):-2,(2,3):2,(0,5):1},6),6)

# --- random rank-5 sample (connected) ---
random.seed(7)
def connected(B,n):
    seen={0}; st=[0]
    while st:
        x=st.pop()
        for y in range(n):
            if B[x][y]!=0 and y not in seen: seen.add(y); st.append(y)
    return len(seen)==n
cnt=0
while cnt<10:
    n=5; e={}
    for i in range(n):
        for j in range(i+1,n): e[(i,j)]=random.randint(-2,2)
    B=B_from(e,n)
    if connected(B,n): add(f"R5 rand#{cnt}",B,n); cnt+=1

def gap_at(B,n,cap):
    cyc,r=P.analyze(f"    cap={cap}",B,n,cap)
    return cyc-r

if __name__=="__main__":
    caps={3:12,4:8,5:6,6:4}
    hits=[]
    for name,B,n in FAMILIES:
        cap=caps[n]
        print(f"\n[{name}] (rank {n})", flush=True)
        try:
            g=gap_at(B,n,cap)
        except Exception as ex:
            print(f"    ERROR {ex}"); continue
        if g>0:
            print(f"    *** GAP {g} at cap {cap} -- re-check higher cap ***", flush=True)
            g2=gap_at(B,n,cap+2)
            grew = g2>g
            hits.append((name,n,g,g2,grew))
            print(f"    GAP {g}->{g2} ({'GROWS = real FZ-failure' if grew else 'fixed = likely boundary'})", flush=True)
    print("\n===== FZ-FAILURE HITS =====")
    if not hits: print("none: all families square/pentagon-generated at these caps (FZ holds).")
    for name,n,g,g2,grew in hits:
        print(f"  {name} (r{n}): gap {g}->{g2} {'GROWS' if grew else 'fixed'}")
