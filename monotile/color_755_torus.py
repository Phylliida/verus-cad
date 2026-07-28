"""canon 755: torus sweep index 129..256 (parallel to the C&C box).

Run:  ./runpy.sh color_755_torus.py [workers=20]
"""
import json
import multiprocessing as mp
import sys
import time

WORKERS = int(sys.argv[1]) if len(sys.argv) > 1 else 20

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
    _G["LAT"] = [B for B in lattice_classes(256)
                 if 128 < B[0][0] * B[1][1] * B[2][2] <= 256]


def try_lattice(B):
    arena2 = _G["arena2"]
    T2E = _G["T2E"]
    ts, _ = arena2.solve_lattice_torus(
        B, _G["bad"], _G["selfbad"], conf_budget=200_000)
    if ts:
        return B
    return None


def main():
    canonical = json.load(open("color3d_canonical.json"))["canonical"]
    prof = canonical[755]
    T2E = {}
    census = json.load(open("faceeq3d_census.json"))
    for key, ei in census["triple_to_eq"].items():
        ax, o1, o2 = map(int, key.split(","))
        T2E[(ax, o1, o2)] = ei
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
    _G["bad"] = bad
    _G["selfbad"] = selfbad
    t0 = time.time()
    from skew import lattice_classes
    LAT = [B for B in lattice_classes(256)
           if 128 < B[0][0] * B[1][1] * B[2][2] <= 256]
    print(f"sweep 129..256: {len(LAT)} lattices (200k/class) [{t0:.0f}]",
          flush=True)
    with mp.Pool(WORKERS, initializer=init_worker) as pool:
        for k, hit in enumerate(pool.imap_unordered(
                try_lattice, LAT, chunksize=4)):
            if hit is not None:
                print(f"*** PERIODIC: lattice {hit} index "
                      f"{hit[0][0] * hit[1][1] * hit[2][2]} "
                      f"[{time.time() - t0:.0f}s] ***", flush=True)
                with open("classify_color.jsonl", "a") as out:
                    out.write(json.dumps(
                        {"i": 755, "verdict": "periodic",
                         "index": hit[0][0] * hit[1][1] * hit[2][2]})
                        + "\n")
                pool.terminate()
                return
            if (k + 1) % 2000 == 0:
                print(f"  {k + 1}/{len(LAT)} "
                      f"[{time.time() - t0:.0f}s]", flush=True)
    print(f"no torus 129..256 [{time.time() - t0:.0f}s]", flush=True)


if __name__ == "__main__":
    main()
