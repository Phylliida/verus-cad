"""COLOR mop-up: resolve the 201 STALLs and 194 empty4s.

STALLs: torus sweep to index 64 (200k conflicts), then boxes 4^3/5^3/6^3
(20M). empty4s: box 5^3 (10M), then 6^3 (20M). Parallel, checkpointed
(appends resolved verdicts to classify_color.jsonl; safe to relaunch).

Run:  ./runpy.sh color_mopup.py [workers=48]
"""
import json
import multiprocessing as mp
import os
import sys
import time

WORKERS = int(sys.argv[1]) if len(sys.argv) > 1 else 48
CKPT = "classify_color.jsonl"

_G = {}


def init_worker():
    import arena2
    from skew import lattice_classes
    census = json.load(open("faceeq3d_census.json"))
    T2E = {}
    for key, ei in census["triple_to_eq"].items():
        ax, o1, o2 = map(int, key.split(","))
        T2E[(ax, o1, o2)] = ei
    _G["T2E"] = T2E
    _G["LAT64"] = list(lattice_classes(64))
    _G["arena2"] = arena2


def bad_of(prof):
    T2E = _G["T2E"]
    held = set(prof)
    bad = [[], [], []]
    selfbad = [[], [], []]
    for ax in range(3):
        for o1 in range(24):
            for o2 in range(24):
                if T2E[(ax, o1, o2)] not in held:
                    bad[ax].append((o1, o2))
                    if o1 == o2:
                        selfbad[ax].append(o1)
    return bad, selfbad


def do_stall(ci, prof):
    arena2 = _G["arena2"]
    bad, selfbad = bad_of(prof)
    for B in _G["LAT64"]:
        ts, _ = arena2.solve_lattice_torus(B, bad, selfbad,
                                           conf_budget=200_000)
        if ts:
            return (ci, "periodic", B[0][0] * B[1][1] * B[2][2])
    for dims in ((4, 4, 4), (5, 5, 5), (6, 6, 6)):
        sb, _ = arena2.box_sat(dims, bad, conf_budget=20_000_000)
        if sb is False:
            return (ci, f"empty{dims[0]}", None)
    return (ci, "DEEP-SURVIVOR", None)


def do_empty4(ci, prof):
    arena2 = _G["arena2"]
    bad, selfbad = bad_of(prof)
    sb, _ = arena2.box_sat((5, 5, 5), bad, conf_budget=10_000_000)
    if sb is False:
        return (ci, "empty5", None)
    sb, _ = arena2.box_sat((6, 6, 6), bad, conf_budget=20_000_000)
    if sb is False:
        return (ci, "empty6", None)
    return (ci, "DEEP-SURVIVOR", None)


def do_one(arg):
    ci, prof, kind = arg
    if kind == "stall":
        return do_stall(ci, prof)
    return do_empty4(ci, prof)


def main():
    canonical = json.load(open("color3d_canonical.json"))["canonical"]
    stalls, e4 = [], []
    done = set()
    if os.path.exists(CKPT):
        for line in open(CKPT):
            r = json.loads(line)
            if r["verdict"] == "STALL":
                stalls.append(r["i"])
            elif r["verdict"] == "empty4":
                e4.append(r["i"])
            else:
                done.add((r["i"], r["verdict"]))
    jobs = [(ci, "stall") for ci in sorted(set(stalls))] + \
           [(ci, "e4") for ci in sorted(set(e4))]
    print(f"jobs: {len(jobs)} ({len(stalls)} stalls, {len(e4)} empty4)",
          flush=True)
    t0 = time.time()
    survivors = []
    with open(CKPT, "a") as out, \
            mp.Pool(WORKERS, initializer=init_worker) as pool:
        for k, ((ci, kind), (ci2, verdict, idx)) in enumerate(
                zip(jobs, pool.imap_unordered(
                    do_one,
                    [(ci, canonical[ci], kind)
                     for ci, kind in jobs], chunksize=1))):
            rec = {"i": ci2, "verdict": verdict}
            if idx is not None:
                rec["index"] = idx
            out.write(json.dumps(rec) + "\n")
            if verdict == "DEEP-SURVIVOR":
                out.flush()
                survivors.append(ci2)
                print(f"  *** DEEP-SURVIVOR {ci2} ({kind}) ***", flush=True)
            if (k + 1) % 20 == 0:
                out.flush()
                print(f"  {k + 1}/{len(jobs)} [{time.time() - t0:.0f}s]",
                      flush=True)
    print(f"MOPUP DONE [{time.time() - t0:.0f}s] "
          f"survivors: {survivors}", flush=True)


if __name__ == "__main__":
    main()
