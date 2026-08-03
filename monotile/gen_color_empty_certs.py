"""R2 pipeline: box-UNSAT certificates for the color empty frontier.

The 196,058 non-density-killed empty color profiles reduce to 65,250
locally-maximal empty masks (the frontier): every empty profile m has a
frontier superset M, and emptiness transports downward by mask inclusion
(tiling_mono in Lean). So box-UNSAT certificates are only needed for the
frontier.

Per frontier mask M (at its verdict tier's box size):
  1. CNF export via lean-flocq's ExportEmptyCNF (batch mode) — the SAME
     encoder whose correctness (`empty_sound`) is proven in Lean.
  2. cadical --lrat (binary) — UNSAT required (exit 20), else alarm.
  3. cake_lpr verify — VERIFIED UNSAT logged to
     color_frontier_verified.txt; .cnf/.lrat then deleted (disk bound).

Also emits color_empty_inheritance.json: for each non-frontier empty
profile, its maximal frontier superset (maskLe witness for the Lean
inheritance batch).

Checkpointed at every stage (safe to kill and relaunch).

Run:  ./runpy.sh gen_color_empty_certs.py [workers=48]
"""
import json
import multiprocessing as mp
import os
import subprocess
import sys
import time

WORKERS = int(sys.argv[1]) if len(sys.argv) > 1 else 48
ROOT = '/home/bepis/prog/verus-cad/monotile'
LEAN = '/home/bepis/prog/verus-cad/lean-flocq'
CAD = '/home/bepis/.elan/toolchains/leanprover--lean4---v4.25.0/bin/cadical'
CAKE = f'{ROOT}/tools/cake_lpr/cake_lpr'
DIR = f'{ROOT}/color_empty_certs'
VLOG = f'{ROOT}/color_frontier_verified.txt'
TIER_DIMS = {'empty3': 3, 'empty5': 5, 'empty6': 6, 'empty7': 7}


def load_empty():
    kills = set(k['i'] for k in json.load(
        open(f'{ROOT}/color_density_kills.json')))
    v = {}
    for line in open(f'{ROOT}/classify_color.jsonl'):
        r = json.loads(line)
        v[r['i']] = r['verdict']
    canon = json.load(open(f'{ROOT}/color3d_canonical.json'))['canonical']
    masks = {}
    for i, ver in v.items():
        if ver in TIER_DIMS and i not in kills:
            n = 0
            for b in canon[i]:
                n |= 1 << b
            masks[n] = (i, TIER_DIMS[ver])
    return masks


def compute_frontier():
    """Locally-maximal empty masks + inheritance map m -> frontier M."""
    if os.path.exists(f'{ROOT}/color_empty_frontier.json'):
        d = json.load(open(f'{ROOT}/color_empty_frontier.json'))
        return d['frontier'], d['inheritance']
    masks = load_empty()
    E = set(masks)
    print(f'empty (not density-killed): {len(E)}', flush=True)
    frontier = []
    for m in E:
        if not any(not (m >> b) & 1 and (m | (1 << b)) in E
                   for b in range(84)):
            frontier.append(m)
    F = set(frontier)
    inheritance = {}
    for m in E:
        if m in F:
            continue
        cur = m
        while cur not in F:
            for b in range(84):
                if not (cur >> b) & 1 and (cur | (1 << b)) in E:
                    cur |= 1 << b
                    break
        inheritance[str(m)] = cur
    print(f'frontier: {len(frontier)}, '
          f'inheritance pairs: {len(inheritance)}', flush=True)
    json.dump({'frontier': frontier, 'inheritance': inheritance},
              open(f'{ROOT}/color_empty_frontier.json', 'w'))
    return frontier, inheritance


def export_chunk(jf):
    return subprocess.run(
        ['lake', 'env', 'lean', '--run',
         'LeanFlocq/ExportEmptyCNF.lean', 'batch', jf],
        cwd=LEAN, capture_output=True, text=True).returncode


def solve_verify(args):
    i, m, dims = args
    cnf = f'{DIR}/{i}.cnf'
    lrat = f'{DIR}/{i}.lrat'
    if not os.path.exists(lrat):
        r = subprocess.run([CAD, '--lrat', cnf, lrat],
                           capture_output=True, text=True)
        if r.returncode != 20:
            return (i, f'SOLVER-RC{r.returncode}')
    r = subprocess.run([CAKE, cnf, lrat],
                       capture_output=True, text=True)
    if 'VERIFIED UNSAT' not in r.stdout:
        return (i, 'CAKE-FAIL')
    with open(VLOG, 'a') as f:
        f.write(f'{i}\n')
    os.remove(lrat)
    os.remove(cnf)
    return (i, 'ok')


def main():
    os.makedirs(DIR, exist_ok=True)
    t0 = time.time()
    frontier, _ = compute_frontier()
    masks = load_empty()

    # stage 1: CNF export (parallel lean batch processes)
    jobs = []
    for m in frontier:
        i, dims = masks[m]
        out = f'{DIR}/{i}.cnf'
        if not os.path.exists(out):
            jobs.append(f'{m} {dims} {dims} {dims} 0 {out}')
    print(f'cnf export: {len(jobs)} jobs', flush=True)
    if jobs:
        nchunks = WORKERS
        chunks = [jobs[k::nchunks] for k in range(nchunks)]
        jfiles = []
        for k, ch in enumerate(chunks):
            jf = f'{DIR}/jobs_{k}.txt'
            with open(jf, 'w') as f:
                f.write('\n'.join(ch))
            jfiles.append(jf)

        with mp.Pool(WORKERS) as pool:
            rcs = pool.map(export_chunk, jfiles)
        assert all(rc == 0 for rc in rcs), f'export failures: {rcs}'
    print(f'cnf export done [{time.time() - t0:.0f}s]', flush=True)

    # stage 2+3: cadical + cake_lpr (checkpointed)
    verified = set(open(VLOG).read().split()) if os.path.exists(VLOG) \
        else set()
    todo = []
    for m in frontier:
        i, dims = masks[m]
        if str(i) not in verified:
            todo.append((i, m, dims))
    print(f'solve+verify: {len(todo)} to do', flush=True)

    fails = []
    with mp.Pool(WORKERS) as pool:
        for k, (i, status) in enumerate(
                pool.imap_unordered(solve_verify, todo, chunksize=64)):
            if status != 'ok':
                fails.append((i, status))
                print(f'  *** {i}: {status} ***', flush=True)
            if (k + 1) % 5000 == 0:
                print(f'  {k + 1}/{len(todo)} verified '
                      f'[{time.time() - t0:.0f}s]', flush=True)
    print(f'DONE: {len(todo) - len(fails)} verified, {len(fails)} failures '
          f'[{time.time() - t0:.0f}s]', flush=True)
    assert not fails, f'failures: {fails[:10]}'


if __name__ == '__main__':
    main()
