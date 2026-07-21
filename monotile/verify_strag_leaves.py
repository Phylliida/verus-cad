"""cake_lpr verification of the 387 straggler leaf certs.

For each leaf (from cube_strag34_done.jsonl): regenerate the leaf CNF
(Lean-exported base + cube units, header clause-count fixed), run
cake_lpr, require 'VERIFIED UNSAT', log to strag_verified.txt, delete
the .lrat (bounds disk). Checkpointed: verified leaves are skipped on
restart. This justifies the stragLeafUnsat axioms in
AnyK3DStragTrees.lean.

Run:  ./runpy.sh verify_strag_leaves.py
"""
import json
import os
import subprocess
import time

ROOT = '/home/bepis/prog/verus-cad/monotile'
CAKE = f'{ROOT}/tools/cake_lpr/cake_lpr'
VLOG = f'{ROOT}/strag_verified.txt'

leaves = []
per_ci = {}
for line in open(f'{ROOT}/cube_strag34_done.jsonl'):
    r = json.loads(line)
    if r['verdict'] == 'UNSAT':
        ci = r['i']
        idx = per_ci.get(ci, 0)
        per_ci[ci] = idx + 1
        leaves.append((ci, idx, r['cube']))
print(f"{len(leaves)} leaves", flush=True)

# base CNF per straggler
bases = {}
for fn in os.listdir(f'{ROOT}/empty_certs'):
    if fn.endswith('.cnf') and '_leaf' not in fn:
        ci = int(fn.split('_')[0])
        bases[ci] = f'{ROOT}/empty_certs/{fn}'

verified = set()
if os.path.exists(VLOG):
    verified = set(open(VLOG).read().split())
vfh = open(VLOG, 'a')

st = {'ok': 0, 'skip': 0, 'fail': 0}
t0 = time.time()
for ci, idx, cube in leaves:
    kk = f"{ci}:{','.join(map(str, cube))}"
    if kk in verified:
        st['skip'] += 1
        continue
    base = bases[ci]
    lrat = base.replace('.cnf', f"_leaf{idx}.lrat")
    assert os.path.exists(lrat), f"missing cert {lrat}"
    with open(base) as f:
        header = f.readline()
        body = f.read()
    _, _, nvars, ncls = header.split()
    tmp = f'/tmp/svl_{abs(hash(kk))}.cnf'
    with open(tmp, 'w') as g:
        g.write(f"p cnf {nvars} {int(ncls) + len(cube)}\n")
        g.write(body)
        for lit in cube:
            g.write(f"{lit} 0\n")
    r = subprocess.run([CAKE, tmp, lrat], capture_output=True, text=True)
    os.remove(tmp)
    if 'VERIFIED UNSAT' in r.stdout:
        st['ok'] += 1
        vfh.write(kk + '\n')
        vfh.flush()
        os.remove(lrat)
    else:
        st['fail'] += 1
        print(f"*** cake_lpr REJECTED leaf {ci} cube={cube}", flush=True)
    if (st['ok'] + st['skip'] + st['fail']) % 50 == 0:
        print(f"  {st} [{time.time() - t0:.0f}s]", flush=True)
print(f"DONE {st} [{time.time() - t0:.0f}s]", flush=True)
