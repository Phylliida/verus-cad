"""Streaming cube-and-conquer verification for genArena.cnf with cake_lpr.

Single DFS pass over the tree (FORCE=6 forced centers, then adaptive split via
split_cache.txt). At each node:
  - already-verified (hash in verified.txt)  -> skip (cert already deleted)
  - a cert on disk that cake_lpr ACCEPTS     -> log + DELETE cert (bounds disk)
  - a cert on disk that cake_lpr REJECTS     -> corrupt (e.g. a killed cadical
                                                run) -> delete + re-solve
  - known internal (split_cache) / unsolved  -> solve, branching on cadical:
        rc=20 UNSAT -> verify with cake_lpr, then a leaf (log + delete)
        rc=10 SAT   -> *** genArena satisfiable *** -> STOP, critical
        rc=0  timeout -> hard cube -> mark split, recurse into both children
Every accepted leaf is cake_lpr-checked (CakeML/HOL4-verified). Resumable via
verified.txt. Writes manifest.json + a trie-completeness (cover) check at the end.
"""
import subprocess, os, hashlib, json, time
from arena2 import PTS

ROOT = '/home/bepis/prog/verus-cad/monotile'
CAKE = f'{ROOT}/tools/cake_lpr/cake_lpr'
CAD = '/home/bepis/.elan/toolchains/leanprover--lean4---v4.25.0/bin/cadical'
FORCE = 6
BUDGET = 60

centers, corners, edges = [], [], []
for i, p in enumerate(PTS):
    ax = max(range(3), key=lambda k: abs(p[k]))
    tang = sorted(abs(p[k]) for k in range(3) if k != ax)
    if tuple(tang) == (0, 0): centers.append(i)
    elif tuple(tang) == (2, 2): corners.append(i)
    else: edges.append(i)
order = centers + corners[:4] + corners[4:] + edges

clauses = open(f'{ROOT}/genArena.cnf').read().rstrip().split('\n')[1:]
CDIR = f'{ROOT}/cube_certs'
split_set = set(open(f'{CDIR}/split_cache.txt').read().split()) if os.path.exists(f'{CDIR}/split_cache.txt') else set()
split_fh = open(f'{CDIR}/split_cache.txt', 'a')
VLOG = f'{CDIR}/verified.txt'
verified_set = set(open(VLOG).read().split()) if os.path.exists(VLOG) else set()
vlog_fh = open(VLOG, 'a')

def key(cube): return hashlib.md5(str(cube).encode()).hexdigest()[:16]
def lit(p, b): return (p + 1) if b else -(p + 1)
def nxt_var(cube):
    used = {p for p, _ in cube}
    return next((v for v in order if v not in used), None)
def write_cnf(cube):
    units = [f'{lit(p, b)} 0' for p, b in cube]
    tmp = f'/tmp/sv_{key(cube)}.cnf'
    open(tmp, 'w').write(f'p cnf 6997 {len(clauses)+len(units)}\n' + '\n'.join(clauses + units) + '\n')
    return tmp

manifest = []
st = {'ok': 0, 'skip': 0, 'proved': 0, 'resolved': 0, 'freed': 0}  # every leaf ends UNSAT; keys are just the route
t0 = time.time()

def cake_ok(cube, cert):
    tmp = write_cnf(cube)
    r = subprocess.run([CAKE, tmp, cert], capture_output=True, text=True)
    os.remove(tmp)
    return 'VERIFIED UNSAT' in r.stdout

def cadical_rc(cube, cert):
    tmp = write_cnf(cube)
    r = subprocess.run([CAD, '-t', str(BUDGET), '--lrat', tmp, cert], capture_output=True, text=True)
    os.remove(tmp)
    return r.returncode, r.stdout  # 20 UNSAT, 10 SAT, else timeout/indeterminate

def accept(kk, cube, cert):
    manifest.append({'key': kk, 'cube': cube})
    vlog_fh.write(kk + '\n'); vlog_fh.flush()
    if os.path.exists(cert):
        st['freed'] += os.path.getsize(cert); os.remove(cert)

def mark_split(kk):
    split_set.add(kk); split_fh.write(kk + '\n'); split_fh.flush()

def progress():
    if (st['ok'] + st['proved'] + st['resolved']) % 25 == 0:
        print(f'[{time.strftime("%H:%M:%S")}] ok={st["ok"]} proved_unsat={st["proved"]} '
              f'resolved={st["resolved"]} skip={st["skip"]} freed={st["freed"]//10**9}G '
              f'df={_free()}G', flush=True)

def solve(kk, cube, cert, tag):
    """solve an unsolved cube; branch on cadical's verdict."""
    rc, out = cadical_rc(cube, cert)
    if rc == 20:
        if not cake_ok(cube, cert):
            print(f'HARD FAIL {kk} d={len(cube)}: freshly-solved cert rejected by cake_lpr -- STOPPING', flush=True)
            raise SystemExit(1)
        accept(kk, cube, cert); st[tag] += 1; progress()
    elif rc == 10:  # SATISFIABLE -- capture the surviving decoration, loudly halt
        model = [int(x) for line in out.splitlines() if line.startswith('v ')
                 for x in line[2:].split() if x != '0']
        json.dump({'key': kk, 'depth': len(cube), 'cube': cube, 'model': model},
                  open(f'{CDIR}/SAT_FOUND.json', 'w'))
        print('\n' + '*' * 64 + f'\n*** SAT *** {kk} d={len(cube)}: genArena is SATISFIABLE\n'
              f'*** a SURVIVING decoration -- saved to cube_certs/SAT_FOUND.json\n' + '*' * 64 + '\n', flush=True)
        raise SystemExit(2)
    else:  # timeout -> hard cube, split
        if os.path.exists(cert): os.remove(cert)
        mark_split(kk)
        v = nxt_var(cube)
        if v is None:
            print(f'EXHAUSTED {kk} d={len(cube)} (budget too small)', flush=True); return
        print(f'SPLIT {kk} d={len(cube)}: hard cube (cadical timeout at {BUDGET}s), splitting', flush=True)
        visit(cube + [(v, False)]); visit(cube + [(v, True)])

def visit(cube):
    if len(cube) < FORCE:
        v = order[len(cube)]; visit(cube + [(v, False)]); visit(cube + [(v, True)]); return
    kk = key(cube); cert = f'{CDIR}/{kk}.lrat'
    if kk in verified_set:
        manifest.append({'key': kk, 'cube': cube}); st['skip'] += 1; return
    if os.path.exists(cert) and os.path.getsize(cert) > 0:
        if cake_ok(cube, cert):
            accept(kk, cube, cert); st['ok'] += 1; progress(); return
        os.remove(cert)  # corrupt cert (e.g. a killed cadical run) -> re-solve
        print(f'RESOLVE {kk} d={len(cube)}: cake_lpr rejected existing cert; re-solving', flush=True)
        solve(kk, cube, cert, 'resolved'); return
    if kk in split_set:
        v = nxt_var(cube); visit(cube + [(v, False)]); visit(cube + [(v, True)]); return
    if nxt_var(cube) is None:
        print(f'EXHAUSTED d={len(cube)} (budget too small)', flush=True); return
    solve(kk, cube, cert, 'proved')

def _free():
    s = os.statvfs(ROOT); return s.f_bavail * s.f_frsize // 10**9

def trie_complete(cubes):
    paths = [tuple((p, b) for p, b in c['cube']) for c in cubes]
    pos = {order[i]: i for i in range(len(order))}
    norm = [tuple(sorted(pth, key=lambda pb: pos[pb[0]])) for pth in paths]
    leafset = set(norm)
    if len(leafset) != len(norm): return False, 'duplicate leaves'
    prefixes = set()
    for pth in norm:
        for i in range(len(pth)): prefixes.add(pth[:i])
    nodes = prefixes | leafset
    for nd in prefixes:
        v = order[len(nd)]
        if (nd + ((v, False),)) not in nodes or (nd + ((v, True),)) not in nodes:
            return False, f'incomplete at depth {len(nd)}'
        if nd in leafset: return False, f'leaf is also internal at depth {len(nd)}'
    return True, f'{len(leafset)} leaves cover all assignments'

if __name__ == '__main__':
    visit([])
    json.dump(manifest, open(f'{CDIR}/manifest.json', 'w'))
    ok, msg = trie_complete(manifest)
    print(f'\n== DONE ok={st["ok"]} proved_unsat={st["proved"]} resolved={st["resolved"]} '
          f'skip={st["skip"]} in {time.time()-t0:.0f}s; freed {st["freed"]//10**9}G; df={_free()}G ==', flush=True)
    print(f'== COVER: {"COMPLETE" if ok else "INCOMPLETE"} - {msg} ==', flush=True)
    print(f'== manifest: {len(manifest)} leaf cubes, all cake_lpr-VERIFIED UNSAT ==', flush=True)
