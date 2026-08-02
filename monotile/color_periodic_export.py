"""Export periodic torus witnesses for all periodic color profiles.

For each of the 41,824 canonical color profiles verdicted periodic
(last-wins over classify_color.jsonl), re-solve the lattice torus
(same machinery as classify_color.py) STORING the orientation grid,
then rectangularize: the witness lattice B (upper-triangular HNF) has
diagonal periods d_i (smallest d_i > 0 with d_i*e_i in B), and the
B-periodic grid expands to a plain (d1,d2,d3) rectangular torus config
— which is all the Lean checker needs (no lattice machinery kernel-side).

Self-check before export mirrors the Lean `torusOK` check exactly:
every cell/axis compat holds under the symmetrization-free relation
(allowed = NOT in `bad`).

Outputs:
  color_periodic_witnesses.json — [{i, d: [d1,d2,d3], grid: [...]}]
  ../lean-flocq/LeanFlocq/AnyK3DColorPeriodicData{j}.lean — packed
      chunks for AnyK3DColorPeriodic (torusOK + torusOK_sound).

Run:  ./runpy.sh color_periodic_export.py [workers=48]
"""
import json
import multiprocessing as mp
import os
import sys

os.environ.setdefault("ARENA_K", "4")

WORKERS = int(sys.argv[1]) if len(sys.argv) > 1 else 48
N_CHUNKS = 8
CHUNK_NUMBERS = 400_000   # soft cap on grid numbers per chunk

_G = {}


def _init(cap):
    import arena2
    from skew import lattice_classes
    census = json.load(open("faceeq3d_census.json"))
    T2E = {}
    for key, ei in census["triple_to_eq"].items():
        ax, o1, o2 = map(int, key.split(","))
        T2E[(ax, o1, o2)] = ei
    _G["T2E"] = T2E
    _G["LAT"] = list(lattice_classes(cap))
    _G["arena2"] = arena2


def init_worker():
    _init(64)


def init_worker_big():
    _init(96)


def diag_periods(B):
    """Smallest diagonal periods (d1,d2,d3) with d_i*e_i in the lattice."""
    (a, b, c), (_, d, e), (_, _, f) = B
    idx = a * d * f
    d3 = f
    g = f
    beta = 1
    while (e * beta) % g:
        beta += 1
    d2 = d * beta
    d1 = None
    for d1c in range(a, idx + 1, a):
        al = d1c // a
        if (b * al) % d:
            continue
        beta1 = -(b * al) // d
        if (c * al + e * beta1) % f == 0:
            d1 = d1c
            break
    assert d1 is not None
    return (d1, d2, d3)


def do_one(args):
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
    for B in _G["LAT"]:
        ts, grid = arena2.solve_lattice_torus(B, bad, selfbad,
                                              conf_budget=50_000)
        if ts:
            break
    else:
        return (ci, None)
    d1, d2, d3 = diag_periods(B)
    rv = arena2.reduce_vec
    rect = {}
    for x in range(d1):
        for y in range(d2):
            for z in range(d3):
                rect[(x, y, z)] = grid[rv((x, y, z), B)]
    # self-check: mirrors Lean torusOK exactly
    for (x, y, z), o1 in rect.items():
        for ax in range(3):
            nc = [x, y, z]
            nc[ax] = (nc[ax] + 1) % (d1, d2, d3)[ax]
            o2 = rect[tuple(nc)]
            if (o1, o2) in bad[ax]:
                return (ci, ("SELFCHECK-FAIL", B, (d1, d2, d3)))
    flat = [rect[(x, y, z)]
            for x in range(d1) for y in range(d2) for z in range(d3)]
    return (ci, (d1, d2, d3, flat))


def pack_profile(prof):
    n = 0
    for i in prof:
        n |= 1 << i
    return n


def main():
    canonical = json.load(open("color3d_canonical.json"))["canonical"]
    verdicts = {}
    for line in open("classify_color.jsonl"):
        r = json.loads(line)
        verdicts[r["i"]] = r["verdict"]
    periodic = sorted(ci for ci, v in verdicts.items() if v == "periodic")
    print(f"periodic profiles: {len(periodic)}")

    jobs = [(ci, canonical[ci]) for ci in periodic]
    witnesses = []
    failures = []
    with mp.Pool(WORKERS, initializer=init_worker) as pool:
        for k, (ci, w) in enumerate(
                pool.imap_unordered(do_one, jobs, chunksize=16)):
            if w is None:
                failures.append(ci)
            elif isinstance(w, tuple) and w and w[0] == "SELFCHECK-FAIL":
                failures.append((ci, "SELFCHECK-FAIL"))
            else:
                d1, d2, d3, flat = w
                witnesses.append({"i": ci, "d": [d1, d2, d3], "grid": flat})
            if (k + 1) % 2000 == 0:
                print(f"  {k + 1}/{len(jobs)} solved, "
                      f"{len(failures)} failures", flush=True)
    print(f"main sweep: {len(witnesses)} witnesses, "
          f"{len(failures)} failures")
    if failures:
        # retry at larger lattice caps (e.g. the index-72 profile 22387)
        retry = [(f, canonical[f]) for f in failures
                 if isinstance(f, int)]
        failures = [f for f in failures if not isinstance(f, int)]
        print(f"retrying {len(retry)} at cap 96")
        with mp.Pool(min(8, WORKERS), initializer=init_worker_big) as pool:
            for ci, w in pool.imap_unordered(do_one, retry, chunksize=1):
                if w is None or (isinstance(w, tuple) and w
                                 and w[0] == "SELFCHECK-FAIL"):
                    failures.append(ci)
                else:
                    d1, d2, d3, flat = w
                    witnesses.append({"i": ci, "d": [d1, d2, d3],
                                      "grid": flat})
    print(f"witnesses: {len(witnesses)}, failures: {len(failures)}")
    if failures:
        print("FAILURES:", failures[:20])
    assert not failures, "unresolved periodic profiles — investigate"

    witnesses.sort(key=lambda w: w["i"])
    with open("color_periodic_witnesses.json", "w") as f:
        json.dump(witnesses, f)

    total = sum(len(w["grid"]) for w in witnesses)
    print(f"total grid cells: {total}")

    # Lean export: chunks bounded by grid-number count
    chunks = []
    cur = []
    curn = 0
    for w in witnesses:
        cur.append(w)
        curn += len(w["grid"]) + 6
        if curn >= CHUNK_NUMBERS:
            chunks.append(cur)
            cur, curn = [], 0
    if cur:
        chunks.append(cur)
    print(f"{len(chunks)} lean chunks")

    for j, chunk in enumerate(chunks):
        rows = []
        for w in chunk:
            prof = pack_profile(canonical[w["i"]])
            d1, d2, d3 = w["d"]
            grid = ", ".join(map(str, w["grid"]))
            rows.append(f"  ({w['i']}, {prof}, {d1}, {d2}, {d3}, #[{grid}])")
        body = ",\n".join(rows)
        out = f"""/- AUTO-GENERATED by monotile/color_periodic_export.py.
Periodic torus witnesses for color profiles, chunk {j}
of {len(chunks)} (canonical indices of
monotile/color3d_canonical.json). Each entry:
(canon index, 84-bit profile, d1, d2, d3, rectangular torus grid).
Do not edit by hand. -/
import LeanFlocq.AnyK3DColorPeriodic

set_option maxRecDepth 1000000

namespace AnyK3D

def periodicData{j} : Array (Nat × Nat × Nat × Nat × Nat × Array Nat) := #[
{body}
]

theorem periodicData{j}_verified :
    periodicData{j}.all (fun x =>
      torusOK (heldOfNat x.2.1) x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2)
      = true := by
  native_decide

set_option maxHeartbeats 800000 in
theorem periodicData{j}_periodic : ∀ x ∈ periodicData{j},
    PeriodicRelTiles (relOfHeld (heldOfNat x.2.1)) := by
  intro x hx
  have hv := Array.all_eq_true_iff_forall_mem.mp periodicData{j}_verified x hx
  -- sizes are positive by construction (exported grids are nonempty)
  have hsize := torusOK_size_pos hv
  exact torusOK_sound _ hsize.1 hsize.2.1 hsize.2.2 hv

end AnyK3D
"""
        path = f"../lean-flocq/LeanFlocq/AnyK3DColorPeriodicData{j}.lean"
        with open(path, "w") as f:
            f.write(out)
    print("wrote lean chunk files")


if __name__ == "__main__":
    main()
