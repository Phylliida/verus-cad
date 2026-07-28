#!/usr/bin/env python3
"""Probe 4 (diagnostic): the sign-chamber graph of the twin-hub mutation closure.

Signs of the six entries (b01,b02,b03,b12,b13,b23) live in {-1,0,+1}^6 (<=729
patterns). Mutation induces a finite graph on patterns. We compute the reachable
subgraph from the twin-hub seed by SOUND abstract sign-mutation:

  entry in row/col k:   sign flips (determined)
  other entry (i,j):    new = old + corr, where
      corr = s   if sign(b_ik)==sign(b_kj)==s != 0     (magnitude nonzero)
      corr = 0   otherwise
    then new sign:
      corr==0            -> old sign (determined)
      old==0             -> corr sign (determined)
      corr==old (!=0)    -> that sign (determined; same-sign sum)
      corr==-old (!=0)   -> AMBIGUOUS: {-1,0,+1} all possible (branch; sound
                            over-approximation of what magnitudes can realize)

Over-approximation is SOUND for a later invariance proof: if f's identity holds
on every edge of this graph it holds on the true (smaller) closure. We report
the graph size, #ambiguous branch events, and how many edges are "clean"
(no sum-cancellation, so no absolute-value-of-a-sum appears downstream).
"""
import sys
from collections import deque
from itertools import product

# entry index <-> (i,j)
IDX = {}
PAIRS = []
for i in range(4):
    for j in range(i+1, 4):
        IDX[(i,j)] = len(PAIRS); PAIRS.append((i,j))
def gij(sig, i, j):
    if i == j: return 0
    if i < j: return sig[IDX[(i,j)]]
    return -sig[IDX[(j,i)]]

def sign_mutate(sig, k):
    """Return list of (child_sig, ambiguous_count) reachable by mutating at k."""
    base = list(sig)
    # row/col k entries flip
    flips = {}
    for i in range(4):
        if i == k: continue
        # entry (min,max) among (i,k)
        if (min(i,k),max(i,k)) in IDX:
            pass
    # compute new signs for all 6 entries
    # determined part + ambiguous positions
    determined = [None]*6
    ambiguous = []
    for (i,j) in PAIRS:
        idx = IDX[(i,j)]
        if i == k or j == k:
            determined[idx] = -sig[idx]
            continue
        old = sig[idx]
        sik = gij(sig, i, k); skj = gij(sig, k, j)
        corr = sik if (sik != 0 and sik == skj) else 0
        if corr == 0:
            determined[idx] = old
        elif old == 0:
            determined[idx] = corr
        elif corr == old:
            determined[idx] = old
        else:  # corr == -old : cancellation, sign of sum is ambiguous
            ambiguous.append(idx)
    children = []
    if not ambiguous:
        children.append((tuple(determined), 0))
    else:
        for combo in product((-1,0,1), repeat=len(ambiguous)):
            c = determined[:]
            for pos, val in zip(ambiguous, combo):
                c[pos] = val
            children.append((tuple(c), len(ambiguous)))
    return children, len(ambiguous)

def closure(seed):
    seen = {seed}
    q = deque([seed])
    edges = []            # (sig, k, child, ambiguous_count)
    max_amb = 0
    while q:
        sig = q.popleft()
        for k in range(4):
            children, amb = sign_mutate(sig, k)
            max_amb = max(max_amb, amb)
            for child, a in children:
                edges.append((sig, k, child, a))
                if child not in seen:
                    seen.add(child); q.append(child)
    return seen, edges, max_amb

if __name__ == "__main__":
    # twin-hub seed, large c: (b01,b02,b03,b12,b13,b23) = (+,+,+,+,0,-)
    seed = (1, 1, 1, 1, 0, -1)
    print("seed (twin-hub, large c):", seed)
    nodes, edges, max_amb = closure(seed)
    clean_edges = [e for e in edges if e[3] == 0]
    amb_edges = [e for e in edges if e[3] > 0]
    print(f"reachable sign-patterns: {len(nodes)}")
    print(f"total edges: {len(edges)}  (clean: {len(clean_edges)}, cancellation: {len(amb_edges)})")
    print(f"max simultaneous ambiguous entries in one mutation: {max_amb}")
    # distinct (parent-sign, k, child-sign) identity obligations
    obligations = set((s, k, c) for s, k, c, a in edges)
    print(f"distinct (sigma, k, sigma') identity obligations: {len(obligations)}")
    # how many patterns have a zero entry
    withzero = sum(1 for n in nodes if 0 in n)
    print(f"patterns containing a zero entry: {withzero}/{len(nodes)}")
    # how many child patterns arise ONLY through a cancellation branch (may need
    # care with |sum| in the outer f)
    clean_children = set(c for s,k,c,a in clean_edges)
    only_amb = set(c for s,k,c,a in amb_edges) - clean_children - {seed}
    print(f"patterns reachable ONLY via a cancellation branch: {len(only_amb)}")
    import json
    json.dump({"nodes": [list(n) for n in sorted(nodes)],
               "obligations": [[list(s), k, list(c)] for (s,k,c) in sorted(obligations)]},
              open("probe4_chambers.json","w"))
    print("wrote probe4_chambers.json")
