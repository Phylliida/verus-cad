"""Lazy-absorption probe: after teaching the solver the saved pattern
library one bump at a time (as the real run does), how hard is the
first FRESH proposal? Configs: balance off / seqcounter / totalizer.

Reports per config: cache-absorption time, then the first fresh
proposal's time or STALL at the per-proposal cap.
"""
import json
import time

from pysat.card import EncType
from arena2 import Synth, PATTERN_FILE, PERM

CAP = 150.0           # per-proposal wall cap, seconds

with open(PATTERN_FILE) as f:
    data = json.load(f)
plists = data.get("patterns", [])

library = []
libseen = set()
for plist in plists:
    S = frozenset((min(a, b), max(a, b)) for a, b in plist)
    for g in range(24):
        pg = PERM[g]
        Sg = frozenset((min(pg[a], pg[b]), max(pg[a], pg[b]))
                       for a, b in S)
        if Sg not in libseen:
            libseen.add(Sg)
            library.append(Sg)
print(f"{len(plists)} saved patterns, {len(library)} conjugates")

CONFIGS = [("balance OFF        ", dict(balance=False)),
           ("balance seqcounter ", dict(balance=True,
                                        balance_enc=EncType.seqcounter)),
           ("balance totalizer  ", dict(balance=True,
                                        balance_enc=EncType.totalizer))]

for name, kw in CONFIGS:
    syn = Synth(**kw)
    seen = set()
    cached = 0
    t_absorb0 = time.time()
    result = None
    while True:
        t0 = time.time()
        dec = syn.propose(deadline=t0 + CAP)
        dt = time.time() - t0
        if dec == "STALL":
            result = f"STALL after {cached} cached (proposal >{CAP:.0f}s)"
            break
        if dec is None:
            result = f"UNSAT after {cached} cached ({dt:.1f}s)"
            break
        hit = next((S for S in library
                    if all(dec[a] != dec[b] for a, b in S)), None)
        if hit is not None:
            syn.block_pattern(hit, seen)
            cached += 1
            continue
        result = (f"FRESH proposal after {cached} cached, "
                  f"fresh solve {dt:.1f}s")
        break
    print(f"{name}: {result}  [total {time.time()-t_absorb0:.0f}s]")
    syn.solver.delete()
