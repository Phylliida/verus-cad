"""FULL pre-check of the R3 coverage claim: for every one of the
9,341,248 raw achievable color profiles, the lex-min canonical (via the
Lean permMask direction, i.e. preimage under EQPERM[g]) is in the
414,079-entry verdict table."""
import json
import time

EQPERM = json.load(open("anyk3d_canonical.json"))["eqperm"]
canon = json.load(open("color3d_canonical.json"))["canonical"]
cmasks = set(sum(1 << e for e in p) for p in canon)
profs = json.load(open("color3d_profiles.json"))
print("raw profiles:", len(profs), flush=True)


def canonof(m):
    return min(tuple(sorted(i for i in range(84)
                            if m >> EQPERM[g][i] & 1))
               for g in range(24))


def pmask(p):
    return sum(1 << e for e in p)


t0 = time.time()
miss = 0
for k, p in enumerate(profs):
    if pmask(list(canonof(pmask(p)))) not in cmasks:
        miss += 1
        if miss <= 5:
            print("MISS:", p[:10], flush=True)
    if k % 1000000 == 0:
        print(f"{k} checked, {miss} misses, {time.time()-t0:.0f}s",
              flush=True)
print(f"TOTAL: {len(profs)} profiles, {miss} misses, "
      f"{time.time()-t0:.0f}s", flush=True)
