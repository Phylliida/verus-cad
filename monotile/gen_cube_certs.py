"""Resumable cube-and-conquer on genArena.cnf -> one LRAT cert per leaf.
Leaves (prefix-free) cover all assignments; each is UNSAT. For Lean huns.

RESUMABLE: cert files are keyed by a hash of the cube (survive restarts), and
internal (SPLIT) nodes are cached in split_cache.txt. On restart the DFS
re-traverses but SKIPS any node already solved (cert on disk) or known-split
(in cache) WITHOUT re-running cadical -- so it continues from the frontier
instead of redoing the easy prefix every time."""
import subprocess, time, os, hashlib, json
from arena2 import PTS

CAD = '/home/bepis/.elan/toolchains/leanprover--lean4---v4.25.0/bin/cadical'
ROOT = '/home/bepis/prog/verus-cad/monotile'
BUDGET = 60          # seconds; >= 35 so depth-54 hard cubes solve, not exhaust
FORCE = 6            # split the 6 centers unconditionally

centers, corners, edges = [], [], []
for i, p in enumerate(PTS):
    ax = max(range(3), key=lambda k: abs(p[k]))
    tang = sorted(abs(p[k]) for k in range(3) if k != ax)
    if tuple(tang) == (0, 0): centers.append(i)
    elif tuple(tang) == (2, 2): corners.append(i)
    else: edges.append(i)
order = centers + corners[:4] + corners[4:] + edges

clauses = open(f'{ROOT}/genArena.cnf').read().rstrip().split('\n')[1:]
os.makedirs(f'{ROOT}/cube_certs', exist_ok=True)
CACHE = f'{ROOT}/cube_certs/split_cache.txt'
split_set = set(open(CACHE).read().split()) if os.path.exists(CACHE) else set()
cache_fh = open(CACHE, 'a')

manifest = []
solved = [0]; cadruns = [0]; skipped = [0]

def key(cube): return hashlib.md5(str(cube).encode()).hexdigest()[:16]
def lit(p, b): return (p + 1) if b else -(p + 1)

def split(cube):
    used = {p for p, _ in cube}
    nxt = next((v for v in order if v not in used), None)
    if nxt is None:
        print(f'EXHAUSTED depth {len(cube)} (budget {BUDGET}s too small!)', flush=True)
        return
    solve(cube + [(nxt, False)]); solve(cube + [(nxt, True)])

def solve(cube):
    if len(cube) < FORCE:
        nxt = order[len(cube)]
        solve(cube + [(nxt, False)]); solve(cube + [(nxt, True)]); return
    kk = key(cube); cert = f'{ROOT}/cube_certs/{kk}.lrat'
    if os.path.exists(cert) and os.path.getsize(cert) > 0:      # already-solved leaf
        manifest.append({'key': kk, 'cube': cube}); solved[0] += 1; skipped[0] += 1; return
    if kk in split_set:                                          # known internal node
        split(cube); return
    units = [f'{lit(p, b)} 0' for p, b in cube]; cl = clauses + units
    tmp = f'/tmp/cc_{kk}.cnf'
    open(tmp, 'w').write(f'p cnf 6997 {len(cl)}\n' + '\n'.join(cl) + '\n')
    r = subprocess.run([CAD, '-t', str(BUDGET), '--lrat', tmp, cert], capture_output=True, text=True)
    os.remove(tmp); cadruns[0] += 1
    if r.returncode == 20:                                       # UNSAT -> leaf
        manifest.append({'key': kk, 'cube': cube}); solved[0] += 1
        if cadruns[0] % 20 == 0:
            print(f'[{time.strftime("%H:%M:%S")}] {solved[0]} leaves ({skipped[0]} resumed, '
                  f'{cadruns[0]} new cadical runs, last depth {len(cube)})', flush=True)
        return
    if os.path.exists(cert): os.remove(cert)
    split_set.add(kk); cache_fh.write(kk + '\n'); cache_fh.flush()  # persist split decision
    split(cube)

t0 = time.time()
solve([])
json.dump(manifest, open(f'{ROOT}/cube_certs/manifest.json', 'w'))
print(f'DONE: {len(manifest)} leaf cubes all UNSAT in {time.time()-t0:.0f}s '
      f'({skipped[0]} resumed, {cadruns[0]} solved this session)', flush=True)
