"""M4-C3 cert campaign: cadical --lrat for the 3,405 empty frontier masks.

- The 3,371 cheap masks (x=0, box 3^3): monolithic cadical --lrat on the
  Lean-exported DIMACS (certs ~100KB, in-Lean verifyCert route).
- The 34 stragglers (x=1): per-leaf DIMACS = base + cube units from
  cube_strag34_done.jsonl (literal numbering matches: python 1-based =
  Lean-export 1-based), cadical --lrat per leaf (cake_lpr route).

Checkpointed: skips masks/leaves whose .lrat already exists. Exit code 20
(UNSAT) required; anything else is an alarm.

Run:  ./runpy.sh gen_empty_certs.py [workers=32]
"""
import json
import multiprocessing as mp
import os
import subprocess
import sys
import time

WORKERS = int(sys.argv[1]) if len(sys.argv) > 1 else 32
CAD = "/home/bepis/.elan/toolchains/leanprover--lean4---v4.25.0/bin/cadical"
JOBS = "empty_certs_jobs.txt"
DIR = "empty_certs"
CUBES = "cube_strag34_done.jsonl"


def load_jobs():
    jobs = []
    for line in open(JOBS):
        ws = line.split()
        if len(ws) == 6:
            mask, w, h, d, x, out = ws
            ci = int(os.path.basename(out).split("_")[0])
            jobs.append((ci, mask, x, out))
    return jobs


def run_cadical(cnf_path, lrat_path):
    """Returns (verdict, size). verdict: UNSAT / SAT / OTHER."""
    r = subprocess.run([CAD, "--lrat", cnf_path, lrat_path],
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    if r.returncode == 20:
        return ("UNSAT", os.path.getsize(lrat_path))
    if r.returncode == 10:
        return ("SAT", 0)
    return (f"EXIT{r.returncode}", 0)


def do_mask(job):
    ci, mask, x, out = job
    lrat = out.replace(".cnf", ".lrat")
    if os.path.exists(lrat):
        return (ci, "cached", 0)
    return (ci, *run_cadical(out, lrat))


def do_leaf(arg):
    ci, out, leaf_id, cube = arg
    leaf_cnf = out.replace(".cnf", f"_leaf{leaf_id}.cnf")
    leaf_lrat = out.replace(".cnf", f"_leaf{leaf_id}.lrat")
    if os.path.exists(leaf_lrat):
        return (ci, leaf_id, "cached", 0)
    with open(out) as f, open(leaf_cnf, "w") as g:
        header = f.readline()
        pv, cv, nvars, ncls = header.split()
        g.write(f"p cnf {nvars} {int(ncls) + len(cube)}\n")
        for line in f:
            g.write(line)
        for lit in cube:
            g.write(f"{lit} 0\n")
    v, size = run_cadical(leaf_cnf, leaf_lrat)
    os.remove(leaf_cnf)
    return (ci, leaf_id, v, size)


def main():
    jobs = load_jobs()
    cheap = [j for j in jobs if j[2] == "0"]
    strags = [j for j in jobs if j[2] == "1"]
    print(f"cheap {len(cheap)}, stragglers {len(strags)}", flush=True)

    cubes_by_ci = {}
    for line in open(CUBES):
        r = json.loads(line)
        if r["verdict"] == "UNSAT":
            cubes_by_ci.setdefault(r["i"], []).append(r["cube"])

    t0 = time.time()
    n_bad = 0
    with mp.Pool(WORKERS) as pool:
        for k, (ci, verdict, size) in enumerate(
                pool.imap_unordered(do_mask, cheap, chunksize=4)):
            if verdict not in ("UNSAT", "cached"):
                n_bad += 1
                print(f"*** ALARM cheap {ci}: {verdict}", flush=True)
            if (k + 1) % 200 == 0:
                print(f"  cheap {k + 1}/{len(cheap)} "
                      f"[{time.time() - t0:.0f}s]", flush=True)
        leaf_jobs = []
        for ci, mask, x, out in strags:
            for lid, cube in enumerate(cubes_by_ci.get(ci, [])):
                leaf_jobs.append((ci, out, lid, cube))
        print(f"straggler leaves: {len(leaf_jobs)} [{time.time() - t0:.0f}s]",
              flush=True)
        for ci, lid, verdict, size in pool.imap_unordered(
                do_leaf, leaf_jobs, chunksize=1):
            if verdict not in ("UNSAT", "cached"):
                n_bad += 1
                print(f"*** ALARM leaf {ci}/{lid}: {verdict}", flush=True)
    print(f"DONE bad={n_bad} [{time.time() - t0:.0f}s]", flush=True)


if __name__ == "__main__":
    main()
