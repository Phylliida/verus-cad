#!/usr/bin/env python3
"""Probe 1b (v2): extract the separating invariant found by probe1 E3 in
human-readable form, plus the surprise dim-5 acyclic rank-3 kernel.

v2: support minimization is done on the KERNEL side — each greedy test is an
incremental O(kdim^2) rank update in the kernel-coefficient space, instead of a
fresh full elimination per feature (v1 was hours at degree 4; v2 is seconds).

Part A: exact rational kernel basis for rank-3 acyclic pure d<=3 (20 features).
Part B: minimal separating degree for signed features on the twin-hub class.
Part C: kernel-side greedy support minimization -> sparse separating invariant
        -> EXACT integer verification on all pairs -> readable formula + values.
"""
import numpy as np, random, time
from fractions import Fraction
from math import lcm

P = 2147483647

def mutate(B, k):
    n = len(B)
    Bp = [[0]*n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if i == k or j == k: Bp[i][j] = -B[i][j]
            else: Bp[i][j] = B[i][j] + (abs(B[i][k])*B[k][j] + B[i][k]*abs(B[k][j]))//2
    return Bp

def skew(entries, n):
    B = [[0]*n for _ in range(n)]
    for (i,j,v) in entries: B[i][j] = v; B[j][i] = -v
    return B

def upper(B):
    n = len(B)
    return tuple(B[i][j] for i in range(n) for j in range(i+1,n))

def exp_tuples(nv, d):
    out = []
    def rec(pos, rem, cur):
        if pos == nv: out.append(tuple(cur)); return
        for e in range(rem+1): cur.append(e); rec(pos+1, rem-e, cur); cur.pop()
    rec(0, d, [])
    return out

def pure_features(nv, d):
    return [(t, tuple(e % 2 for e in t)) for t in exp_tuples(nv, d)]

def signed_features(nv, d):
    feats = []
    for t in exp_tuples(nv, d):
        sup = [i for i in range(nv) if t[i] >= 1]
        for bits in range(1 << len(sup)):
            s = [0]*nv
            for b, i in enumerate(sup): s[i] = (bits >> b) & 1
            feats.append((t, tuple(s)))
    return feats

def feat_matrix(points, feats, p):
    N, nv = len(points), len(points[0])
    absarr = np.array([[abs(x) % p for x in pt] for pt in points], dtype=np.int64)
    sgnarr = np.array([[(0 if x == 0 else (1 if x > 0 else -1)) for x in pt] for pt in points], dtype=np.int64)
    maxe = max(max(t) for t, s in feats)
    pows = np.ones((N, nv, maxe+1), dtype=np.int64)
    for e in range(1, maxe+1): pows[:,:,e] = (pows[:,:,e-1] * absarr) % p
    M = np.empty((N, len(feats)), dtype=np.int64)
    for j, (t, s) in enumerate(feats):
        col = np.ones(N, dtype=np.int64); sg = np.ones(N, dtype=np.int64)
        for v in range(nv):
            if t[v]: col = (col * pows[:,v,t[v]]) % p
            if s[v]: sg = sg * sgnarr[:,v]
        M[:,j] = (col * sg) % p
    return M

def rref(Ain, p):
    A = Ain.copy() % p
    rows, cols = A.shape
    piv = []; r = 0
    for c in range(cols):
        nz = np.nonzero(A[r:,c])[0]
        if nz.size == 0: continue
        i = r + int(nz[0])
        if i != r: A[[r,i]] = A[[i,r]]
        A[r] = (A[r] * pow(int(A[r,c]), p-2, p)) % p
        colv = A[:,c].copy(); colv[r] = 0
        nzr = np.nonzero(colv)[0]
        if nzr.size: A[nzr] = (A[nzr] - colv[nzr,None]*A[r][None,:]) % p
        piv.append(c); r += 1
        if r == rows: break
    return A, piv, r

def kernel_basis(A, piv, cols, p):
    pivset = set(piv)
    free = [c for c in range(cols) if c not in pivset]
    K = np.zeros((len(free), cols), dtype=np.int64)
    for idx, f in enumerate(free):
        K[idx, f] = 1
        for i, pc in enumerate(piv): K[idx, pc] = (-int(A[i, f])) % p
    return K

def matmod(A, B, p):
    Bh, Bl = B >> 16, B & 0xFFFF
    return ((A @ Bl) % p + (((A @ Bh) % p) << 16)) % p

def kernel_of_constraints(pairs, feats, p, label=""):
    t0 = time.time()
    xs = [x for x, y in pairs]; ys = [y for x, y in pairs]
    ncols = len(feats)
    n1 = min(len(pairs), int(2.5*ncols) + 50)
    C1 = (feat_matrix(ys[:n1], feats, p) - feat_matrix(xs[:n1], feats, p)) % p
    A, piv, rank = rref(C1, p)
    K = kernel_basis(A, piv, ncols, p)
    i = n1
    while i < len(pairs) and K.shape[0] > 0:
        j = min(len(pairs), i+4000)
        C = (feat_matrix(ys[i:j], feats, p) - feat_matrix(xs[i:j], feats, p)) % p
        R = matmod(C, K.T % p, p)
        if np.any(R):
            A2, piv2, _ = rref(R, p)
            K = matmod(kernel_basis(A2, piv2, K.shape[0], p), K % p, p)
        i = j
    print(f"   [{label}] kernel dim {K.shape[0]} ({time.time()-t0:.1f}s)", flush=True)
    return K

def eval_feat_exact(pt, t, s):
    v = 1
    for i in range(len(pt)):
        if t[i]:
            v *= abs(pt[i])**t[i]
            if s[i] and pt[i] < 0: v = -v
            if s[i] and pt[i] == 0: return 0
    return v

def feat_name(t, s, names):
    parts = []
    for i, (ti, si) in enumerate(zip(t, s)):
        if ti == 0: continue
        if si:
            parts.append(names[i] if ti == 1 else f"{names[i]}*|{names[i]}|^{ti-1}".replace("^1",""))
        else:
            parts.append(f"|{names[i]}|" + (f"^{ti}" if ti > 1 else ""))
    return "*".join(parts) if parts else "1"

def frac_kernel_on_support(pairs, sub):
    rows = []
    for x, y in pairs:
        rows.append([Fraction(eval_feat_exact(y,t,s) - eval_feat_exact(x,t,s)) for t, s in sub])
    ncol = len(sub); piv = []; r = 0
    for c in range(ncol):
        pr = next((i for i in range(r, len(rows)) if rows[i][c] != 0), None)
        if pr is None: continue
        rows[r], rows[pr] = rows[pr], rows[r]
        inv = 1/rows[r][c]
        rows[r] = [v*inv for v in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c] != 0:
                f = rows[i][c]
                rows[i] = [a - f*b for a, b in zip(rows[i], rows[r])]
        piv.append(c); r += 1
    free = [c for c in range(ncol) if c not in piv]
    basis = []
    for f in free:
        fd = {sub[f]: Fraction(1)}
        for i, pc in enumerate(piv):
            if rows[i][f] != 0: fd[sub[pc]] = -rows[i][f]
        basis.append(fd)
    return basis

# ================= Part A =================
print("=== A: rank-3 acyclic pure d<=3 kernel (exact rational) ===", flush=True)
random.seed(7)
acyc_pairs, cyc_pairs = [], []
def orient3(B):
    x, y, z = B[0][1], B[1][2], B[2][0]
    if x == 0 or y == 0 or z == 0: return "degen"
    if (x > 0 and y > 0 and z > 0) or (x < 0 and y < 0 and z < 0): return "cyc"
    return "acyc"
while len(acyc_pairs) < 4000 or len(cyc_pairs) < 4000:
    B = skew([(0,1,random.randint(-9,9)),(0,2,random.randint(-9,9)),(1,2,random.randint(-9,9))],3)
    B1 = mutate(B, random.randrange(3))
    o0, o1 = orient3(B), orient3(B1)
    if o0 == o1 == "acyc" and len(acyc_pairs) < 4000: acyc_pairs.append((upper(B),upper(B1)))
    if o0 == o1 == "cyc" and len(cyc_pairs) < 4000: cyc_pairs.append((upper(B),upper(B1)))
pure3 = pure_features(3,3)
names3 = ["b01","b02","b12"]
basisA = frac_kernel_on_support(acyc_pairs[:600], pure3)
print(f"exact kernel dim {len(basisA)} (on 600 pairs); verifying on all 4000:", flush=True)
for fd in basisA:
    bad = sum(1 for x, y in acyc_pairs
              if sum(c*(eval_feat_exact(y,t,s)-eval_feat_exact(x,t,s)) for (t,s),c in fd.items()) != 0)
    L = lcm(*[c.denominator for c in fd.values()])
    txt = " ".join(f"{int(c*L):+d}*{feat_name(t,s,names3)}" for (t,s),c in sorted(fd.items(), key=lambda kv:(sum(kv[0][0]),kv[0])) if c)
    print(f"   [{'OK ' if bad==0 else f'{bad} BAD'}] {txt}", flush=True)

# ================= Part B =================
print("=== B: minimal separating degree (signed features, twin-hub class) ===", flush=True)
def tmpl_twin(c): return skew([(0,1,1),(1,2,1),(0,3,1),(3,2,1),(0,2,c)],4)
BITGUARD = 1500
class_pairs, seen = [], set()
random.seed(11)
for c in range(3,23):
    for _ in range(60):
        B = tmpl_twin(c)
        for _step in range(10):
            B1 = mutate(B, random.randrange(4))
            if max(abs(e).bit_length() for row in B1 for e in row) > BITGUARD: break
            kk = (upper(B), upper(B1)) if upper(B) <= upper(B1) else (upper(B1), upper(B))
            if kk not in seen:
                seen.add(kk); class_pairs.append((upper(B), upper(B1)))
            B = B1
print(f"{len(class_pairs)} class pairs", flush=True)

mindeg, Kmin, featsmin, smin = None, None, None, None
for d in (1, 2, 3, 4):
    feats = signed_features(6, d)
    K = kernel_of_constraints(class_pairs, feats, P, label=f"signed d<={d}, {len(feats)} feats")
    Fm = feat_matrix([upper(tmpl_twin(5)), upper(tmpl_twin(6))], feats, P)
    s = (Fm[1] - Fm[0]) % P
    v = matmod(K % P, s[:,None], P).ravel()
    sep = bool(np.any(v))
    print(f"  signed d<={d}: separates 5 vs 6: {sep}", flush=True)
    if sep:
        mindeg, Kmin, featsmin, smin = d, K, feats, s
        break
if mindeg is None:
    print("no separation up to degree 4?!"); raise SystemExit

# ================= Part C =================
print(f"=== C: kernel-side support minimization at degree {mindeg} ===", flush=True)
K = Kmin % P
kdim, nfeat = K.shape
v = matmod(K, smin[:,None], P).ravel()

def reduce_vec(vec, R, p):
    w = vec % p
    for piv, row in R:
        if w[piv]: w = (w - w[piv]*row) % p
    return w

R = []          # echelon rows in kernel-coefficient space (removed features)
kept = set(range(nfeat))
complexity = lambda j: (sum(featsmin[j][0]), sum(featsmin[j][1]), featsmin[j])
for _pass in range(3):
    changed = False
    for j in sorted(kept, key=complexity, reverse=True):
        col = K[:, j].copy()
        r = reduce_vec(col, R, P)
        nz = np.nonzero(r)[0]
        if nz.size == 0:
            kept.discard(j); changed = True; continue
        piv = int(nz[0])
        rn = (r * pow(int(r[piv]), P-2, P)) % P
        vred = reduce_vec(v, R, P)
        v2 = (vred - vred[piv]*rn) % P if vred[piv] else vred
        if np.any(v2):
            R.append((piv, rn)); kept.discard(j); changed = True
    if not changed: break
print(f"greedy kept {len(kept)} features", flush=True)

# extract a concrete separating kernel vector supported on kept
if R:
    Rm = np.stack([row for _, row in R])
    A2, piv2, _ = rref(Rm, P)
    N = kernel_basis(A2, piv2, kdim, P)     # null space of removed-constraints
else:
    N = np.eye(kdim, dtype=np.int64)
w = matmod(N, v[:,None], P).ravel()
ai = int(np.nonzero(w)[0][0])
a = N[ai]
f = matmod(a[None,:], K, P).ravel()
support = [j for j in range(nfeat) if f[j] != 0]
print(f"separating vector support size {len(support)} (subset of kept: {set(support) <= kept})", flush=True)

# exact rational kernel on the support, pick separating + exactly-invariant combo
names4 = ["b01","b02","b03","b12","b13","b23"]
sub = [featsmin[j] for j in support]
basis = frac_kernel_on_support(class_pairs, sub)
print(f"exact kernel dim on support: {len(basis)}", flush=True)
best = None
for fd in basis:
    bad = sum(1 for x, y in class_pairs
              if sum(c*(eval_feat_exact(y,t,s)-eval_feat_exact(x,t,s)) for (t,s),c in fd.items()) != 0)
    v5 = sum(c*eval_feat_exact(upper(tmpl_twin(5)),t,s) for (t,s),c in fd.items())
    v6 = sum(c*eval_feat_exact(upper(tmpl_twin(6)),t,s) for (t,s),c in fd.items())
    print(f"  candidate: violations={bad}/{len(class_pairs)}, f(tmpl5)={v5}, f(tmpl6)={v6}", flush=True)
    if bad == 0 and v5 != v6 and best is None: best = fd
if best:
    L = lcm(*[c.denominator for c in best.values()])
    disp = {k: int(c*L) for k, c in best.items() if c}
    print("SEPARATING INVARIANT (exact, integer-scaled):")
    for (t, s), c in sorted(disp.items(), key=lambda kv: (sum(kv[0][0]), kv[0])):
        print(f"   {c:+d} * {feat_name(t, s, names4)}")
    vals = [sum(c2*eval_feat_exact(upper(tmpl_twin(cc)),t,s) for (t,s),c2 in disp.items())
            for cc in range(3,13)]
    print("values on tmpl(c), c=3..12:", vals)
else:
    print("no exactly-verified separating combo on this support — enlarge support/degree")
