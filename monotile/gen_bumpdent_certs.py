"""R6 unified evidence: bump/dent trust debt at the color-pipeline
standard.

Re-evidences ALL bump/dent external trust debt through the R2 color
pipeline's exact discipline (ExportEmptyCNF = the encoder whose
correctness is proven in Lean → cadical --lrat → cake_lpr → ledger;
certs deleted after each check):

  * 3,371 cheap frontier masks (box 3^3, x=0 = `emptyCNF`) — the
    historical `empty_certs/*.cnf` were spot-verified byte-identical to
    the proven encoder's output (11/11), so they are reused as-is.
    This justifies `frontierEmptyFacts` (AnyK3DMain.lean).
  * 387 straggler leaves (x=1 = `emptyCNFX`): the 34 cube-and-conquer
    bases are RE-EXPORTED fresh from the current encoder (historical
    bases matched only up to clause order), then each leaf = base +
    cube units from cube_strag34_done.jsonl. This justifies the 34
    `stragLeafUnsat` axioms (AnyK3DStragTrees.lean).

Ledger: bumpdent_frontier_verified.txt — one line `i` per cheap mask,
one line `i:c1,c2,...` per straggler leaf (strag_verified.txt format).
Checkpointed (verified keys are skipped on restart). WORKERS=4 default
(>4 parallel jobs destabilize this machine).

Run:  ./runpy.sh gen_bumpdent_certs.py [workers=4]
"""
import json
import multiprocessing as mp
import os
import subprocess
import sys
import time

WORKERS = int(sys.argv[1]) if len(sys.argv) > 1 else 4
ROOT = '/home/bepis/prog/verus-cad/monotile'
LEAN = '/home/bepis/prog/verus-cad/lean-flocq'
CAD = '/home/bepis/.elan/toolchains/leanprover--lean4---v4.25.0/bin/cadical'
CAKE = f'{ROOT}/tools/cake_lpr/cake_lpr'
SRC = f'{ROOT}/empty_certs'
DIR = f'{ROOT}/bumpdent_certs'
VLOG = f'{ROOT}/bumpdent_frontier_verified.txt'


def load_jobs():
    """cheap: {i: (mask, w, h, d)}; strag bases: {i: (mask, w, h, d)}."""
    cheap, strag = {}, {}
    for line in open(f'{ROOT}/empty_certs_jobs.txt'):
        ws = line.split()
        m, w, h, d, x, out = ws[0], int(ws[1]), int(ws[2]), int(ws[3]), \
            int(ws[4]), ws[5]
        i = int(os.path.basename(out).split('_')[0])
        (strag if x == 1 else cheap)[i] = (m, w, h, d)
    return cheap, strag


def load_leaves():
    """{i: [cube, ...]} from the cube-and-conquer checkpoint."""
    leaves = {}
    for line in open(f'{ROOT}/cube_strag34_done.jsonl'):
        r = json.loads(line)
        if r['verdict'] == 'UNSAT':
            leaves.setdefault(r['i'], []).append(r['cube'])
    return leaves


def export_strag_bases(strag):
    """Re-export the 34 bases from the current encoder (batch mode)."""
    os.makedirs(DIR, exist_ok=True)
    jobs = []
    for i, (m, w, h, d) in strag.items():
        out = f'{DIR}/base_{i}.cnf'
        if not os.path.exists(out):
            jobs.append(f'{m} {w} {h} {d} 1 {out}')
    print(f'strag base export: {len(jobs)} jobs', flush=True)
    if jobs:
        jf = f'{DIR}/jobs_strag.txt'
        with open(jf, 'w') as f:
            f.write('\n'.join(jobs))
        rc = subprocess.run(
            ['lake', 'env', 'lean', '--run', 'LeanFlocq/ExportEmptyCNF.lean',
             'batch', jf], cwd=LEAN, capture_output=True, text=True)
        assert rc.returncode == 0, f'export failed: {rc.stderr[:500]}'


def check_axiom_dims(strag):
    """Cross-check the jobs-file (mask, dims) of every straggler against
    the axiom comments in AnyK3DStragTrees.lean."""
    import re
    src = open(f'{LEAN}/LeanFlocq/AnyK3DStragTrees.lean').read()
    found = re.findall(r'straggler (\d+): mask (\d+), box (\d+)\^3', src)
    assert len(found) == 34, f'expected 34 axiom comments, got {len(found)}'
    for i, m, d in found:
        i, m, d = int(i), m, int(d)
        assert i in strag, f'straggler {i} not in jobs file'
        mj, w, h, dj = strag[i]
        assert mj == m and w == d and h == d and dj == d, \
            f'straggler {i}: jobs ({mj}, {w},{h},{dj}) != axiom ({m}, {d}^3)'
    print('axiom dims cross-check: 34/34 OK', flush=True)


def verified_set():
    return set(open(VLOG).read().split()) if os.path.exists(VLOG) else set()


def solve_verify_cheap(args):
    i, m, w, h, d = args
    cnf = f'{SRC}/{i}_{m}.cnf'
    lrat = f'{DIR}/{i}.lrat'
    r = subprocess.run([CAD, '--lrat', cnf, lrat],
                       capture_output=True, text=True)
    if r.returncode != 20:
        return (str(i), f'SOLVER-RC{r.returncode}')
    r = subprocess.run([CAKE, cnf, lrat], capture_output=True, text=True)
    if 'VERIFIED UNSAT' not in r.stdout:
        return (str(i), 'CAKE-FAIL')
    with open(VLOG, 'a') as f:
        f.write(f'{i}\n')
    os.remove(lrat)
    os.remove(cnf)
    return (str(i), 'ok')


def solve_verify_leaf(args):
    i, idx, cube = args
    base = f'{DIR}/base_{i}.cnf'
    with open(base) as f:
        header = f.readline()
        body = f.read()
    _, _, nvars, ncls = header.split()
    cnf = f'{DIR}/leaf_{i}_{idx}.cnf'
    lrat = f'{DIR}/leaf_{i}_{idx}.lrat'
    with open(cnf, 'w') as g:
        g.write(f'p cnf {nvars} {int(ncls) + len(cube)}\n')
        g.write(body)
        for lit in cube:
            g.write(f'{lit} 0\n')
    key = f'{i}:{",".join(map(str, cube))}'
    r = subprocess.run([CAD, '--lrat', cnf, lrat],
                       capture_output=True, text=True)
    if r.returncode != 20:
        os.remove(cnf)
        return (key, f'SOLVER-RC{r.returncode}')
    r = subprocess.run([CAKE, cnf, lrat], capture_output=True, text=True)
    if 'VERIFIED UNSAT' not in r.stdout:
        return (key, 'CAKE-FAIL')
    with open(VLOG, 'a') as f:
        f.write(key + '\n')
    os.remove(lrat)
    os.remove(cnf)
    return (key, 'ok')


def main():
    os.makedirs(DIR, exist_ok=True)
    t0 = time.time()
    cheap, strag = load_jobs()
    leaves = load_leaves()
    print(f'cheap {len(cheap)}, strag bases {len(strag)}, '
          f'leaves {sum(len(v) for v in leaves.values())}', flush=True)
    assert len(cheap) == 3371 and len(strag) == 34
    assert sum(len(v) for v in leaves.values()) == 387
    assert set(leaves) == set(strag)
    check_axiom_dims(strag)
    export_strag_bases(strag)

    verified = verified_set()
    todo_cheap = [(i,) + c for i, c in cheap.items() if str(i) not in verified]
    todo_leaves = []
    for i, cubes in leaves.items():
        for idx, cube in enumerate(cubes):
            key = f'{i}:{",".join(map(str, cube))}'
            if key not in verified:
                todo_leaves.append((i, idx, cube))
    print(f'todo: {len(todo_cheap)} cheap, {len(todo_leaves)} leaves',
          flush=True)

    fails = []
    with mp.Pool(WORKERS) as pool:
        for k, (key, status) in enumerate(pool.imap_unordered(
                solve_verify_cheap, todo_cheap, chunksize=32)):
            if status != 'ok':
                fails.append((key, status))
                print(f'  *** cheap {key}: {status} ***', flush=True)
            if (k + 1) % 500 == 0:
                print(f'  cheap {k + 1}/{len(todo_cheap)} '
                      f'[{time.time() - t0:.0f}s]', flush=True)
        for k, (key, status) in enumerate(pool.imap_unordered(
                solve_verify_leaf, todo_leaves, chunksize=16)):
            if status != 'ok':
                fails.append((key, status))
                print(f'  *** leaf {key}: {status} ***', flush=True)
            if (k + 1) % 50 == 0:
                print(f'  leaves {k + 1}/{len(todo_leaves)} '
                      f'[{time.time() - t0:.0f}s]', flush=True)
    print(f'DONE: {len(todo_cheap) + len(todo_leaves) - len(fails)} '
          f'verified, {len(fails)} failures [{time.time() - t0:.0f}s]',
          flush=True)
    assert not fails, f'failures: {fails[:10]}'

    # cleanup: strag bases and historical strag base cnfs (regenerable)
    for i in strag:
        for p in (f'{DIR}/base_{i}.cnf',):
            if os.path.exists(p):
                os.remove(p)
    # final ledger assertions
    v = verified_set()
    new_cheap = sum(1 for i in cheap if str(i) in v)
    new_leaves = sum(
        1 for i, cubes in leaves.items() for cube in cubes
        if f'{i}:{",".join(map(str, cube))}' in v)
    print(f'ledger coverage: cheap {new_cheap}/3371, '
          f'leaves {new_leaves}/387', flush=True)
    assert new_cheap == 3371 and new_leaves == 387


if __name__ == '__main__':
    main()
