"""Parallel pattern saturation: classes are independent, so enumerate
them in a worker pool, level-synchronous in ascending-index batches
(novel patterns found in batch k are pre-blocked in batch k+1, so
later classes only surface genuinely new minimal patterns).

Same soundness as saturate.py (it imports the fixed enumerate_class):
every emitted pattern certifies a periodic tiling; per-class UNSAT
under effective blocks = class complete. Cross-class concurrent
over-emission (two classes finding overlapping patterns in the same
batch) is deduped at merge -- sound either way.

Merge into arena2_patterns.json is atomic (tmp + os.replace).

Usage: python3 saturate2.py [max_index=24] [workers=8]
                            [max_pat=1000] [class_cap_s=900]
                            [min_index=0]
min_index skips classes with index <= min_index (already certified
complete in a previous campaign; their patterns are pre-blocked from
the file regardless).
"""
import json
import os
import sys
import time
from multiprocessing import Pool

from arena2 import PATTERN_FILE
from saturate import enumerate_class, conjugates, stamp
from skew import lattice_classes

WLOG = None


def winit():
    global WLOG
    WLOG = open("saturation_results.jsonl", "a")


def wjob(args):
    B, blocked_list, max_pat, cap = args
    blocked = set(blocked_list)
    t0 = time.time()
    novel, complete, nsol = enumerate_class(B, blocked, WLOG,
                                            max_pat, cap)
    return B, novel, complete, round(time.time() - t0, 1)


def main():
    max_index = int(sys.argv[1]) if len(sys.argv) > 1 else 24
    workers = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    max_pat = int(sys.argv[3]) if len(sys.argv) > 3 else 1000
    cap = float(sys.argv[4]) if len(sys.argv) > 4 else 900.0
    min_index = int(sys.argv[5]) if len(sys.argv) > 5 else 0

    with open(PATTERN_FILE) as fh:
        data = json.load(fh)
    existing = [frozenset((min(p, q), max(p, q)) for p, q in plist)
                for plist in data.get("patterns", [])]
    blocked = set()
    for S in existing:
        blocked.update(conjugates(S))
    classes = sorted((B for B in lattice_classes(max_index)
                      if B[0][0] * B[1][1] * B[2][2] > min_index),
                     key=lambda B: B[0][0] * B[1][1] * B[2][2])
    print(f"[{stamp()}] parallel saturation to {max_index} "
          f"(skipping <= {min_index}): {len(classes)} classes, "
          f"{workers} workers, {len(existing)} patterns pre-blocked",
          flush=True)

    all_novel = []
    incomplete = []
    ndone = 0
    t00 = time.time()
    with Pool(workers, initializer=winit) as pool:
        bs = 2 * workers
        for i in range(0, len(classes), bs):
            batch = classes[i:i + bs]
            blocked_list = list(blocked)
            tasks = [(B, blocked_list, max_pat, cap) for B in batch]
            for B, novel, complete, secs in pool.imap_unordered(
                    wjob, tasks):
                ndone += 1
                ix = B[0][0] * B[1][1] * B[2][2]
                for S in novel:
                    if not any(Sg in blocked for Sg in conjugates(S)):
                        all_novel.append(S)
                    blocked.update(conjugates(S))
                if not complete:
                    incomplete.append(B)
                print(f"[{stamp()}] class {ndone}/{len(classes)} {B} "
                      f"idx {ix}: {len(novel)} novel, "
                      f"{'COMPLETE' if complete else 'CAPPED'} "
                      f"[{secs:.0f}s] (total novel {len(all_novel)})",
                      flush=True)

    # atomic merge
    with open(PATTERN_FILE) as fh:
        data = json.load(fh)
    have = set()
    for plist in data.get("patterns", []):
        S = frozenset((min(p, q), max(p, q)) for p, q in plist)
        have.update(conjugates(S))
    added = 0
    for S in all_novel:
        if not any(Sg in have for Sg in conjugates(S)):
            have.update(conjugates(S))
            data["patterns"].append(sorted(map(list, S)))
            added += 1
    tmp = PATTERN_FILE + ".tmp"
    with open(tmp, "w") as fh:
        json.dump(data, fh)
    os.replace(tmp, PATTERN_FILE)
    print(f"[{stamp()}] PARALLEL SATURATION DONE in "
          f"{(time.time()-t00)/60:.0f}m: {len(all_novel)} novel "
          f"({added} merged, file now {len(data['patterns'])}); "
          f"{len(incomplete)} CAPPED of {len(classes)}", flush=True)
    if not incomplete:
        print(f"[{stamp()}] all classes COMPLETE: library contains "
              f"EVERY balanced-realizable periodic pattern of "
              f"index <= {max_index}", flush=True)
    else:
        print(f"[{stamp()}] capped classes (completeness holds only "
              f"below their indices): {incomplete[:6]}...", flush=True)


if __name__ == "__main__":
    main()
