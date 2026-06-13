"""Forensics on the arena-4 d4 suspicious pile.

ARCHIVED from the parallel claude.ai session (arena 4 is CLOSED).
NOTE (local): needs arena3.py + theory_forensics.py +
arena4_d4_progress.jsonl from that session's outputs."""
import json
import time
from collections import Counter
import numpy as np

from arena4 import setup, compat_sector
from arena3 import box_sat, lattice_torus, bad_tables, sheet_scan, D4_CANON
from arena2 import held_vectors
from theory_forensics import deep_implied
from skew import lattice_classes

if __name__ == "__main__":
    letters, coset_id, cross = setup("d4")
    NL = len(letters)
    recs = [json.loads(l) for l in open("arena4_d4_progress.jsonl")]
    sus = [tuple(r["dec"]) for r in recs
           if r["verdict"] == "suspicious" and "dec" in r]
    print(f"{len(sus)} suspicious candidates")

    sig = Counter()
    for d in sus:
        c = compat_sector(d, letters)
        sig[tuple(int(c[ax].sum()) for ax in range(3))] += 1
    print("compat-density families:", sig.most_common(8))

    t0 = time.time()
    verdicts = Counter()
    for i, d in enumerate(sus[:14]):
        if time.time() - t0 > 150:
            print(f"(time cap after {i} samples)")
            break
        compat = compat_sector(d, letters)
        bad, selfbad = bad_tables(compat, NL)
        target = None
        for v in D4_CANON:
            s, _ = box_sat((5, 5, 5), bad, NL, identify=v, budget=60_000)
            if s is not False:
                target = v
                break
        if target is None:
            verdicts["no-vector@5"] += 1
            continue
        s6, g6 = box_sat((6, 6, 6), bad, NL, identify=target,
                         budget=500_000)
        if s6 is False:
            verdicts["refuted@6"] += 1
            print(f"  {i}: v={target} refuted at 6^3 (window artifact)")
            continue
        if s6 is None:
            verdicts["timeout@6"] += 1
            continue
        held = held_vectors(g6, 4, 12)
        done = False
        for B in deep_implied(held):
            ts, _ = lattice_torus(B, bad, selfbad, NL)
            if ts:
                idx = B[0][0] * B[1][1] * B[2][2]
                verdicts[f"periodic(idx {idx})"] += 1
                print(f"  {i}: periodic via v={target}, index {idx}")
                done = True
                break
        if done:
            continue
        hitB = None
        for B in lattice_classes(32):
            ts, _ = lattice_torus(B, bad, selfbad, NL)
            if ts:
                hitB = B
                break
        if hitB:
            idx = hitB[0][0] * hitB[1][1] * hitB[2][2]
            verdicts[f"periodic(idx {idx})"] += 1
            print(f"  {i}: periodic (brute), index {idx}")
            continue
        rank = int(np.linalg.matrix_rank(np.array(held))) if held else 0
        hs = sorted(held, key=lambda w: max(map(abs, w)))[:6]
        print(f"  {i}: OPEN v={target} held-rank={rank} held~{hs}")
        verdicts["OPEN"] += 1
    print(f"\nverdicts: {dict(verdicts)}  [{time.time()-t0:.0f}s]")
