#!/usr/bin/env python3
"""Probe 1: automated chamber-wise invariant search for quiver mutation.

Searches for polynomial and signed-monomial ("chamber-wise polynomial") mutation
invariants by exact linear algebra mod a large prime. Constraint rows are
feat(mu_k(x)) - feat(x) over sampled mutation pairs; the kernel = candidate
invariant space. Includes:

  E1: rank-3 calibration (ground truth known)
      - acyclic-restricted, pure monomials deg<=3: must find K = b01^2+b02^2+b12^2 + b01*b02*b12
      - cyclic-restricted, pure monomials: should find ONLY constants
        (weight Markov C = sq - |prod| is NOT polynomial in signed entries)
      - cyclic-restricted, signed features: must recover C
  E2: rank-4 global invariants (pure deg<=4, signed deg<=4); expect {1, Pf^2}
  E3: rank-4 twin-hub-class-restricted invariants + SEPARATION TEST:
      does ANY invariant of the family separate tmpl(5) from tmpl(6)/tmpl(7)?

All kernel computations are exact mod p (p = 2^31-1), cross-checked at a second
prime for the headline systems. Anchors are verified with exact integer arithmetic.
"""
import numpy as np, random, time
from collections import deque
from math import comb

P1 = 2147483647
P2 = 2147483629

# ---------------- mutation ----------------
def mutate(B, k):
    n = len(B)
    Bp = [[0]*n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if i == k or j == k:
                Bp[i][j] = -B[i][j]
            else:
                Bp[i][j] = B[i][j] + (abs(B[i][k])*B[k][j] + B[i][k]*abs(B[k][j]))//2
    return Bp

def skew(entries, n):
    B = [[0]*n for _ in range(n)]
    for (i,j,v) in entries:
        B[i][j] = v; B[j][i] = -v
    return B

def upper(B):
    n = len(B)
    return tuple(B[i][j] for i in range(n) for j in range(i+1,n))

# ---------------- feature bases ----------------
def exp_tuples(nv, d):
    out = []
    def rec(pos, rem, cur):
        if pos == nv:
            out.append(tuple(cur)); return
        for e in range(rem+1):
            cur.append(e); rec(pos+1, rem-e, cur); cur.pop()
    rec(0, d, [])
    return out

def pure_features(nv, d):
    # (t, s) with s = t mod 2 encodes the plain monomial prod b^t
    return [(t, tuple(e % 2 for e in t)) for t in exp_tuples(nv, d)]

def signed_features(nv, d):
    # all prod sgn(b_i)^{s_i} |b_i|^{t_i}, s_i in {0,1}, s_i=0 where t_i=0
    feats = []
    for t in exp_tuples(nv, d):
        sup = [i for i in range(nv) if t[i] >= 1]
        for bits in range(1 << len(sup)):
            s = [0]*nv
            for b, i in enumerate(sup):
                s[i] = (bits >> b) & 1
            feats.append((t, tuple(s)))
    return feats

def feat_matrix(points, feats, p):
    """points: list of tuples of python ints. Returns N x M matrix mod p."""
    N, nv = len(points), len(points[0])
    absarr = np.array([[abs(x) % p for x in pt] for pt in points], dtype=np.int64)
    sgnarr = np.array([[(0 if x == 0 else (1 if x > 0 else -1)) for x in pt] for pt in points], dtype=np.int64)
    maxe = max(max(t) for t, s in feats)
    pows = np.ones((N, nv, maxe+1), dtype=np.int64)
    for e in range(1, maxe+1):
        pows[:,:,e] = (pows[:,:,e-1] * absarr) % p
    M = np.empty((N, len(feats)), dtype=np.int64)
    for j, (t, s) in enumerate(feats):
        col = np.ones(N, dtype=np.int64)
        sg = np.ones(N, dtype=np.int64)
        for v in range(nv):
            if t[v]: col = (col * pows[:,v,t[v]]) % p
            if s[v]: sg = sg * sgnarr[:,v]
        M[:,j] = (col * sg) % p
    return M

# ---------------- exact linear algebra mod p ----------------
def rref(Ain, p):
    A = Ain.copy() % p
    rows, cols = A.shape
    piv = []
    r = 0
    for c in range(cols):
        nz = np.nonzero(A[r:,c])[0]
        if nz.size == 0: continue
        i = r + int(nz[0])
        if i != r: A[[r,i]] = A[[i,r]]
        inv = pow(int(A[r,c]), p-2, p)
        A[r] = (A[r] * inv) % p
        colv = A[:,c].copy(); colv[r] = 0
        nzr = np.nonzero(colv)[0]
        if nzr.size:
            A[nzr] = (A[nzr] - colv[nzr,None] * A[r][None,:]) % p
        piv.append(c); r += 1
        if r == rows: break
    return A, piv, r

def kernel_basis(A, piv, cols, p):
    pivset = set(piv)
    free = [c for c in range(cols) if c not in pivset]
    K = np.zeros((len(free), cols), dtype=np.int64)
    for idx, f in enumerate(free):
        K[idx, f] = 1
        for i, pc in enumerate(piv):
            K[idx, pc] = (-int(A[i, f])) % p
    return K

def matmod(A, B, p):
    """(A @ B) mod p for int64 arrays with entries in [0,p). Split to avoid overflow."""
    Bh, Bl = B >> 16, B & 0xFFFF
    return ((A @ Bl) % p + (((A @ Bh) % p) << 16)) % p

def kernel_of_constraints(pairs, feats, p, stage1_rows=None, label=""):
    """pairs: list of (x_tuple, y_tuple). Returns exact kernel (mod p) of all rows."""
    t0 = time.time()
    xs = [x for x, y in pairs]; ys = [y for x, y in pairs]
    ncols = len(feats)
    n1 = min(len(pairs), stage1_rows or int(2.5*ncols) + 50)
    Mx = feat_matrix(xs[:n1], feats, p); My = feat_matrix(ys[:n1], feats, p)
    C1 = (My - Mx) % p
    A, piv, rank = rref(C1, p)
    K = kernel_basis(A, piv, ncols, p)
    # refinement with remaining rows (exact): project constraints onto kernel coords
    i = n1
    CHUNK = 4000
    while i < len(pairs) and K.shape[0] > 0:
        j = min(len(pairs), i+CHUNK)
        Mx = feat_matrix(xs[i:j], feats, p); My = feat_matrix(ys[i:j], feats, p)
        R = matmod((My - Mx) % p, K.T % p, p)           # (chunk x kdim)
        if np.any(R):
            A2, piv2, r2 = rref(R, p)
            K2 = kernel_basis(A2, piv2, K.shape[0], p)   # (k' x kdim)
            K = matmod(K2, K % p, p)
        i = j
    print(f"   [{label}] {len(pairs)} pairs, {ncols} features -> kernel dim {K.shape[0]} "
          f"({time.time()-t0:.1f}s)")
    return K

# ---------------- exact anchors ----------------
def eval_feat_exact(pt, t, s):
    v = 1
    for i in range(len(pt)):
        if t[i]: v *= abs(pt[i])**t[i]
        if s[i] and pt[i] < 0: v = -v
        if s[i] and pt[i] == 0: v = 0
    return v

def check_exact_invariant(fdict, pairs):
    """fdict: {(t,s): coeff}. True iff f(y)-f(x)==0 exactly on all pairs."""
    for x, y in pairs:
        d = sum(c*(eval_feat_exact(y,t,s) - eval_feat_exact(x,t,s)) for (t,s),c in fdict.items())
        if d != 0: return False
    return True

def in_kernel(fdict, feats, K, p):
    v = np.zeros(len(feats), dtype=np.int64)
    idx = {f: i for i, f in enumerate(feats)}
    for f, c in fdict.items():
        v[idx[f]] = c % p
    # f in kernel  <=>  f is orthogonal-complement... membership: solve K^T a = v
    # cheap check: rank([K; v]) == rank(K)
    A, piv, r0 = rref(K % p, p)
    A2, piv2, r1 = rref(np.vstack([K % p, v[None,:]]), p)
    return r1 == r0

# =========================================================================
random.seed(7)
print("=== E1: rank-3 calibration ===")
acyc_pairs, cyc_pairs = [], []
def orient3(B):
    x, y, z = B[0][1], B[1][2], B[2][0]
    if x == 0 or y == 0 or z == 0: return "degen"
    if (x > 0 and y > 0 and z > 0) or (x < 0 and y < 0 and z < 0): return "cyc"
    return "acyc"
while len(acyc_pairs) < 4000 or len(cyc_pairs) < 4000:
    B = skew([(0,1,random.randint(-9,9)),(0,2,random.randint(-9,9)),(1,2,random.randint(-9,9))],3)
    k = random.randrange(3)
    B1 = mutate(B,k)
    o0, o1 = orient3(B), orient3(B1)
    if o0 == o1 == "acyc" and len(acyc_pairs) < 4000: acyc_pairs.append((upper(B),upper(B1)))
    if o0 == o1 == "cyc" and len(cyc_pairs) < 4000: cyc_pairs.append((upper(B),upper(B1)))

pure3 = pure_features(3,3)
sgn3  = signed_features(3,3)
K_acyc = kernel_of_constraints(acyc_pairs, pure3, P1, label="E1a acyc, pure d<=3")
# anchor: K = b01^2 + b02^2 + b12^2 + b01*b02*b12  (signed form of Markov K on acyclic)
mk = lambda t: (t, tuple(e%2 for e in t))
K3 = {mk((2,0,0)):1, mk((0,2,0)):1, mk((0,0,2)):1, mk((1,1,1)):1}
print("   anchor K3 exact-invariant on acyc pairs:", check_exact_invariant(K3, acyc_pairs),
      "| in kernel:", in_kernel(K3, pure3, K_acyc, P1))
K_cycp = kernel_of_constraints(cyc_pairs, pure3, P1, label="E1b cyc, pure d<=3")
K_cycs = kernel_of_constraints(cyc_pairs, sgn3, P1, label="E1c cyc, signed d<=3")
# anchor: weight Markov C = |b01|^2+|b02|^2+|b12|^2 - |b01||b02||b12| (pure abs features)
C3 = {((2,0,0),(0,0,0)):1, ((0,2,0),(0,0,0)):1, ((0,0,2),(0,0,0)):1, ((1,1,1),(0,0,0)):-1}
print("   anchor C3 exact-invariant on cyc pairs:", check_exact_invariant(C3, cyc_pairs),
      "| in kernel:", in_kernel(C3, sgn3, K_cycs, P1))

print("=== E2: rank-4 global invariants ===")
glob_pairs = []
while len(glob_pairs) < 6000:
    B = skew([(i,j,random.randint(-8,8)) for i in range(4) for j in range(i+1,4)],4)
    k = random.randrange(4)
    glob_pairs.append((upper(B), upper(mutate(B,k))))
pure4 = pure_features(6,4)
sgn4  = signed_features(6,3)
Kg_p = kernel_of_constraints(glob_pairs, pure4, P1, label="E2a global, pure d<=4")
Kg_s = kernel_of_constraints(glob_pairs, sgn4, P1, label="E2b global, signed d<=3")
# anchor: Pf^2, vars (b01,b02,b03,b12,b13,b23), Pf = v0*v5 - v1*v4 + v2*v3
Pf2 = {mk((2,0,0,0,0,2)):1, mk((0,2,0,0,2,0)):1, mk((0,0,2,2,0,0)):1,
       mk((1,1,0,0,1,1)):-2, mk((1,0,1,1,0,1)):2, mk((0,1,1,1,1,0)):-2}
print("   anchor Pf^2 exact-invariant globally:", check_exact_invariant(Pf2, glob_pairs),
      "| in kernel:", in_kernel(Pf2, pure4, Kg_p, P1))

print("=== E3: rank-4 twin-hub class-restricted + separation test ===")
def tmpl_twin(c):
    return skew([(0,1,1),(1,2,1),(0,3,1),(3,2,1),(0,2,c)],4)
BITGUARD = 1500
class_pairs, seen = [], set()
random.seed(11)
for c in range(3,23):
    for _ in range(60):
        B = tmpl_twin(c)
        for _step in range(10):
            k = random.randrange(4)
            B1 = mutate(B,k)
            if max(abs(e).bit_length() for row in B1 for e in row) > BITGUARD: break
            key = (upper(B), upper(B1)) if upper(B) <= upper(B1) else (upper(B1), upper(B))
            if key not in seen:
                seen.add(key)
                class_pairs.append((upper(B), upper(B1)))
            B = B1
print(f"   collected {len(class_pairs)} distinct class mutation pairs")
pure6 = pure_features(6,6)
sgn4b = signed_features(6,4)
results = {}
for prime in (P1, P2):
    Kc_p = kernel_of_constraints(class_pairs, pure6, prime, label=f"E3a class, pure d<=6, p={prime}")
    Kc_s = kernel_of_constraints(class_pairs, sgn4b, prime, label=f"E3b class, signed d<=4, p={prime}")
    # separation rows
    for name, K, feats in (("pure d<=6", Kc_p, pure6), ("signed d<=4", Kc_s, sgn4b)):
        for target in (6, 7):
            pts = [upper(tmpl_twin(5)), upper(tmpl_twin(target))]
            Fm = feat_matrix(pts, feats, prime)
            s = (Fm[1] - Fm[0]) % prime
            v = matmod(K % prime, s[:,None], prime)
            sep = bool(np.any(v))
            results[(name, target, prime)] = (int(K.shape[0]), sep)
            print(f"   [{name}, p={prime}] kernel dim {K.shape[0]}: separates tmpl(5) vs tmpl({target})? {sep}")
print("=== summary E3 ===")
for k in sorted(results, key=str): print("  ", k, "->", results[k])
