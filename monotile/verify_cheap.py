"""cake_lpr verification of the 3,371 cheap (empty3) frontier certs.

Monolithic binary LRAT certs from gen_empty_certs.py (cadical,
box 3^3, Lean-exported CNFs). Each is cake_lpr-checked, logged to
cheap_verified.txt, and the .lrat deleted (bounds disk). This justifies
the cheap 3,371 of the 3,405 `frontierEmptyFacts` (AnyK3DMain.lean);
the 34 stragglers are covered by verify_strag_leaves.py.

Checkpointed (skip verified on restart).

Run:  ./runpy.sh verify_cheap.py [workers=48]
"""
import json
import multiprocessing as mp
import os
import subprocess
import sys
import time

WORKERS = int(sys.argv[1]) if len(sys.argv) > 1 else 48
ROOT = '/home/bepis/prog/verus-cad/monotile'
CAKE = f'{ROOT}/tools/cake_lpr/cake_lpr'
VLOG = f'{ROOT}/cheap_verified.txt'
DIR = f'{ROOT}/empty_certs'


def do_one(cnf):
    ci = os.path.basename(cnf).split('_')[0]
    lrat = cnf.replace('.cnf', '.lrat')
    assert os.path.exists(lrat), f"missing {lrat}"
    verified = set()
    if os.path.exists(VLOG):
        verified = set(open(VLOG).read().split())
    if ci in verified:
        return (ci, 'skip', 0)
    r = subprocess.run([CAKE, cnf, lrat], capture_output=True, text=True)
    if 'VERIFIED UNSAT' in r.stdout:
        with open(VLOG, 'a') as f:
            f.write(ci + '\n')
        os.remove(lrat)
        return (ci, 'ok', 0)
    return (ci, 'FAIL', 0)


def main():
    cheap = []
    for line in open(f'{ROOT}/empty_certs_jobs.txt'):
        ws = line.split()
        if len(ws) == 6 and ws[4] == '0':
            cheap.append(ws[5])
    print(f"{len(cheap)} cheap certs", flush=True)
    t0 = time.time()
    st = {'ok': 0, 'skip': 0, 'FAIL': 0}
    with mp.Pool(WORKERS) as pool:
        for k, (ci, v, _) in enumerate(
                pool.imap_unordered(do_one, cheap, chunksize=4)):
            st[v] += 1
            if v == 'FAIL':
                print(f"*** cake_lpr REJECTED {ci}", flush=True)
            if (k + 1) % 200 == 0:
                print(f"  {k + 1}/{len(cheap)} {st} [{time.time() - t0:.0f}s]",
                      flush=True)
    print(f"DONE {st} [{time.time() - t0:.0f}s]", flush=True)


if __name__ == '__main__':
    main()
