"""anyk-08/12: THE CAMPAIGN — classify all 66,134 canonical 3D profiles.

Parallel (Pool), checkpointed (append jsonl, skip done on restart — the
saturate2 discipline; safe to relaunch after any death). Tiers per profile:
torus sweep idx<=8 -> box 3^3 -> box 4^3 (2M conflicts) -> torus <=32 ->
STALL (deep probes handled separately by stallprobe3d.py).

Run:  ./runpy.sh classify3d_all.py [workers=20]
"""
import json
import multiprocessing as mp
import os
import sys
import time

WORKERS = int(sys.argv[1]) if len(sys.argv) > 1 else 20
CKPT = "classify3d_all.jsonl"

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
    _G["LAT8"] = list(lattice_classes(8))
    _G["LAT32"] = list(lattice_classes(32))
    _G["arena2"] = arena2


def classify_one(args):
    ci, prof = args
    arena2 = _G["arena2"]
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
    for B in _G["LAT8"]:
        ts, _ = arena2.solve_lattice_torus(B, bad, selfbad,
                                           conf_budget=20_000)
        if ts:
            return (ci, "periodic", B[0][0] * B[1][1] * B[2][2])
    sb, _ = arena2.box_sat((3, 3, 3), bad, conf_budget=200_000)
    if sb is False:
        return (ci, "empty3", None)
    sb, _ = arena2.box_sat((4, 4, 4), bad, conf_budget=2_000_000)
    if sb is False:
        return (ci, "empty4", None)
    for B in _G["LAT32"]:
        ts, _ = arena2.solve_lattice_torus(B, bad, selfbad,
                                           conf_budget=20_000)
        if ts:
            return (ci, "periodic", B[0][0] * B[1][1] * B[2][2])
    return (ci, "STALL", None)


def main():
    canonical = json.load(open("anyk3d_canonical.json"))["canonical"]
    done = set()
    if os.path.exists(CKPT):
        with open(CKPT) as f:
            for line in f:
                try:
                    done.add(json.loads(line)["i"])
                except Exception:
                    pass
    todo = [(i, p) for i, p in enumerate(canonical) if i not in done]
    print(f"canonical {len(canonical)}, done {len(done)}, todo {len(todo)}",
          flush=True)
    counts = {}
    t0 = time.time()
    with open(CKPT, "a") as out, \
            mp.Pool(WORKERS, initializer=init_worker) as pool:
        for k, (ci, verdict, idx) in enumerate(
                pool.imap_unordered(classify_one, todo, chunksize=16)):
            counts[verdict] = counts.get(verdict, 0) + 1
            rec = {"i": ci, "verdict": verdict}
            if idx is not None:
                rec["index"] = idx
            out.write(json.dumps(rec) + "\n")
            if verdict == "STALL":
                out.flush()
                print(f"  *** STALL canonical {ci} ***", flush=True)
            if (k + 1) % 1000 == 0:
                out.flush()
                rate = (k + 1) / (time.time() - t0)
                print(f"  {k + 1}/{len(todo)} {counts} "
                      f"[{rate:.1f}/s, eta {(len(todo) - k - 1) / rate / 60:.0f}m]",
                      flush=True)
    print(f"CAMPAIGN DONE {counts} [{time.time() - t0:.0f}s]", flush=True)


if __name__ == "__main__":
    main()
