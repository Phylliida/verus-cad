"""COLOR finalists: deep autopsy of the 5 DEEP-SURVIVORs.

Per survivor (from classify_color.jsonl DEEP-SURVIVOR records):
  1. torus sweep index <= 64 at 10x budget (2M conflicts/class — the
     budget the binary finalists needed),
  2. index <= 128 sweep at 1M,
  3. boxes (7,7,7) and (8,8,8) at 50M conflicts.

Run:  ./runpy.sh color_finalists.py [workers=5]
"""
import json
import multiprocessing as mp
import sys
import time

WORKERS = int(sys.argv[1]) if len(sys.argv) > 1 else 5

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
    _G["arena2"] = arena2
    _G["LAT64"] = list(lattice_classes(64))
    _G["LAT128"] = [B for B in lattice_classes(128)
                    if B[0][0] * B[1][1] * B[2][2] > 64]


def autopsy(ci, prof):
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
    log = []
    t0 = time.time()
    for B in _G["LAT64"]:
        ts, _ = arena2.solve_lattice_torus(B, bad, selfbad,
                                           conf_budget=2_000_000)
        if ts:
            return (ci, "periodic",
                    B[0][0] * B[1][1] * B[2][2], log, time.time() - t0)
    log.append(f"no torus <=64 @2M [{time.time() - t0:.0f}s]")
    for B in _G["LAT128"]:
        ts, _ = arena2.solve_lattice_torus(B, bad, selfbad,
                                           conf_budget=1_000_000)
        if ts:
            return (ci, "periodic",
                    B[0][0] * B[1][1] * B[2][2], log, time.time() - t0)
    log.append(f"no torus 65..128 @1M [{time.time() - t0:.0f}s]")
    for dims in ((7, 7, 7), (8, 8, 8)):
        t1 = time.time()
        sb, _ = arena2.box_sat(dims, bad, conf_budget=50_000_000)
        log.append(f"box {dims}: "
                   f"{ {False: 'UNSAT', True: 'SAT', None: 'budget-out'}[sb] } "
                   f"[{time.time() - t1:.0f}s]")
        if sb is False:
            return (ci, f"empty{dims[0]}", None, log, time.time() - t0)
        if sb is None:
            break
    return (ci, "FINALIST", None, log, time.time() - t0)


def do_one(arg):
    return autopsy(*arg)


def main():
    canonical = json.load(open("color3d_canonical.json"))["canonical"]
    surv = []
    FINAL = {"periodic", "empty3", "empty4", "empty5", "empty6", "empty7"}
    resolved = set()
    for line in open("classify_color.jsonl"):
        r = json.loads(line)
        if r["verdict"] in FINAL:
            resolved.add(r["i"])
    for line in open("classify_color.jsonl"):
        r = json.loads(line)
        if r["verdict"] == "DEEP-SURVIVOR" and r["i"] not in resolved:
            surv.append(r["i"])
    surv = sorted(set(surv))
    print(f"finalists: {surv}", flush=True)
    with mp.Pool(WORKERS, initializer=init_worker) as pool:
        for ci, verdict, idx, log, dt in pool.imap_unordered(
                do_one,
                [(ci, canonical[ci]) for ci in surv], chunksize=1):
            print(f"\n=== canon {ci} ===", flush=True)
            for line in log:
                print(f"  {line}", flush=True)
            rec = {"i": ci, "verdict": verdict}
            if idx is not None:
                rec["index"] = idx
            with open("classify_color.jsonl", "a") as out:
                out.write(json.dumps(rec) + "\n")
            print(f"  verdict: {verdict} "
                  f"(index {idx}) [{dt:.0f}s]", flush=True)


if __name__ == "__main__":
    main()
