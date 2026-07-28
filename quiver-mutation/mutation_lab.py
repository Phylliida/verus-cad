"""Quick experimental lab for quiver mutation (skew-symmetric integer matrices).

Sanity checks for the mutation-equivalence paper plan:
  1. mutation is an involution, preserves skew-symmetry
  2. transvection primitive: unit arm i->k, k->j weight v  =>  mu_k adds v to b_ij (sign-gated)
  3. Markov polynomial K = x^2+y^2+z^2 - xyz chamber behavior in rank 3
  4. Pfaffian behavior in rank 4 (|Pf| mutation-invariant?)
  5. BFS hunt for a "+1 ratchet" gadget in rank 4 (counter increment with full state restore)
"""
import random
from collections import deque

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

def is_skew(B):
    n = len(B)
    return all(B[i][j] == -B[j][i] for i in range(n) for j in range(n))

# --- 1. involution + skew preservation ---
random.seed(0)
ok = True
for _ in range(500):
    n = random.choice([3,4,5])
    B = skew([(i,j,random.randint(-5,5)) for i in range(n) for j in range(i+1,n)], n)
    k = random.randrange(n)
    B1 = mutate(B,k)
    ok &= is_skew(B1) and mutate(B1,k) == B
print("1. involution+skew over 500 random trials:", "OK" if ok else "FAIL")

# --- 2. transvection primitive ---
# rank 3: 0 --1--> 1 --v--> 2, accumulator b_02 = w
for v in [5, -5]:
    for w in [3, -3, 0]:
        B = skew([(0,1,1),(1,2,v),(0,2,w)], 3)
        B1 = mutate(B,1)
        print(f"2. arm=1, v={v:+d}, acc w={w:+d}: mu_1 => acc {B[0][2]:+d} -> {B1[0][2]:+d}"
              f"   (arms now {B1[0][1]:+d},{B1[1][2]:+d})")

# --- 3. Markov polynomial chamber behavior, rank 3 ---
def K(B):
    x,y,z = B[0][1], B[1][2], B[2][0]
    return x*x + y*y + z*z - x*y*z
def orientation(B):
    x,y,z = B[0][1], B[1][2], B[2][0]
    if x>0 and y>0 and z>0: return "cyc+"
    if x<0 and y<0 and z<0: return "cyc-"
    if 0 in (x,y,z): return "degen"
    return "acyc"
stats = {}
for _ in range(20000):
    B = skew([(0,1,random.randint(-6,6)),(1,2,random.randint(-6,6)),(0,2,random.randint(-6,6))],3)
    k = random.randrange(3)
    B1 = mutate(B,k)
    key = (orientation(B), orientation(B1), K(B1)==K(B))
    stats[key] = stats.get(key,0)+1
print("3. Markov K=x^2+y^2+z^2-xyz  (from-chamber, to-chamber, K preserved?) counts:")
for key in sorted(stats): print("   ", key, stats[key])

# --- 4. Pfaffian, rank 4 ---
def pf(B):
    return B[0][1]*B[2][3] - B[0][2]*B[1][3] + B[0][3]*B[1][2]
pf_ok = pf_sign = 0
for _ in range(2000):
    B = skew([(i,j,random.randint(-5,5)) for i in range(4) for j in range(i+1,4)],4)
    k = random.randrange(4)
    B1 = mutate(B,k)
    if abs(pf(B1)) == abs(pf(B)): pf_ok += 1
    if pf(B1) == -pf(B): pf_sign += 1
print(f"4. rank-4 Pfaffian: |Pf| preserved in {pf_ok}/2000, Pf -> -Pf in {pf_sign}/2000")

# --- 5. ratchet hunt: rank-4 templates, BFS for word: template(c) -> template(c+delta) ---
def tmpl_twin(c, arm=1):
    # twin unit hubs 1 and 3 both bridging 0 -> 2; accumulator b_02 = c; b_13 = 0 (Pfaffian-safe)
    return skew([(0,1,1),(1,2,1),(0,3,arm),(3,2,1),(0,2,c)],4)

def bfs_word(start, target, cap=64, maxdepth=14, maxstates=3_000_000):
    key = lambda B: tuple(map(tuple,B))
    q = deque([(start,())])
    seen = {key(start)}
    while q:
        B,w = q.popleft()
        if len(w) >= maxdepth: continue
        for k in range(len(B)):
            if w and w[-1] == k: continue
            B1 = mutate(B,k)
            if any(abs(e) > cap for row in B1 for e in row): continue
            kk = key(B1)
            if kk in seen: continue
            seen.add(kk)
            if len(seen) > maxstates: return None, len(seen)
            w1 = w + (k,)
            if B1 == target: return w1, len(seen)
            q.append((B1,w1))
    return None, len(seen)

def apply_word(B, w):
    for k in w: B = mutate(B,k)
    return B

for name, tm in [("twin-unit-hubs", lambda c: tmpl_twin(c,1)),
                 ("twin-hubs-arm2", lambda c: tmpl_twin(c,2))]:
    for delta in [1,2]:
        w, ns = bfs_word(tm(5), tm(5+delta))
        if w is None:
            print(f"5. [{name}] c -> c+{delta}: NO word (depth<=14, cap 64, {ns} states explored)")
        else:
            # verify the word is c-uniform
            uni = all(apply_word(tm(c), w) == tm(c+delta) for c in [7,23,101])
            print(f"5. [{name}] c -> c+{delta}: FOUND word {w}, uniform over c in {{7,23,101}}: {uni}")

# --- 6. weight-level Markov constant on cyclic quivers ---
def weights_cyclic(B):
    x,y,z = B[0][1], B[1][2], B[2][0]
    if x>0 and y>0 and z>0: return (x,y,z)
    if x<0 and y<0 and z<0: return (-x,-y,-z)
    return None
cyc_ok = cyc_tot = 0
random.seed(1)
for _ in range(50000):
    B = skew([(0,1,random.randint(1,8)),(1,2,random.randint(1,8)),(0,2,-random.randint(1,8))],3)
    k = random.randrange(3)
    B1 = mutate(B,k)
    w0, w1 = weights_cyclic(B), weights_cyclic(B1)
    if w0 and w1:
        cyc_tot += 1
        a,b,c = w0; A,Bb,C = w1
        if a*a+b*b+c*c-a*b*c == A*A+Bb*Bb+C*C-A*Bb*C: cyc_ok += 1
print(f"6. weight-level C=a^2+b^2+c^2-abc on cyclic->cyclic mutations: {cyc_ok}/{cyc_tot}")

# --- 7. more ratchet templates + reachable-set sizes under cap ---
def tmpl_tri(c):
    # cyclic "charged" control triangle (0,1,3) w/ weights 2 + unit tap 3->2, accumulator b_02=c
    return skew([(0,1,2),(1,3,2),(3,0,2),(3,2,1),(0,2,c)],4)
def tmpl_mixed(c):
    # asymmetric: hub 1 arms (1,1); hub 3 arms (1,-1) => one adds when pos-armed, other when neg-armed
    return skew([(0,1,1),(1,2,1),(0,3,1),(3,2,-1),(0,2,c)],4)

def reach_size_and_hit(tm, deltas, cap=64, maxdepth=20):
    start = tm(5)
    key = lambda B: tuple(map(tuple,B))
    seen = {key(start)}
    q = deque([(start,())])
    hits = {}
    targets = {d: key(tm(5+d)) for d in deltas}
    while q:
        B,w = q.popleft()
        if len(w) >= maxdepth: continue
        for k in range(len(B)):
            if w and w[-1]==k: continue
            B1 = mutate(B,k)
            if any(abs(e)>cap for row in B1 for e in row): continue
            kk = key(B1)
            if kk in seen: continue
            seen.add(kk)
            for d,t in targets.items():
                if kk == t and d not in hits: hits[d] = w+(k,)
            q.append((B1,w+(k,)))
    return len(seen), hits

for name, tm in [("charged-triangle", tmpl_tri), ("mixed-sign-hubs", tmpl_mixed)]:
    ns, hits = reach_size_and_hit(tm, [1,2,-1])
    print(f"7. [{name}] cap-64 reachable set size {ns}; ratchet hits: "
          f"{ {d: w for d,w in hits.items()} if hits else 'NONE'}")

# --- 8. mod-2 congruence obstruction test: is tmpl(5) ~ tmpl(6) even possible? ---
# mutation acts by B -> E B E^T with E in GL_n(Z), so the GL_n(Z/m)-congruence
# class of B mod m is a mutation invariant. Check m=2 for the twin-hub template.
def congruent_mod2(A, B):
    n = 4
    import itertools
    Am = [[a % 2 for a in row] for row in A]
    Bm = [[b % 2 for b in row] for row in B]
    def det2(M):
        M = [row[:] for row in M]; d = 1
        for c in range(n):
            p = next((r for r in range(c,n) if M[r][c]), None)
            if p is None: return 0
            M[c],M[p] = M[p],M[c]
            for r in range(c+1,n):
                if M[r][c]: M[r] = [(x+y)%2 for x,y in zip(M[r],M[c])]
        return 1
    for bits in range(1<<16):
        E = [[(bits>>(4*i+j))&1 for j in range(n)] for i in range(n)]
        if not det2(E): continue
        # E Am E^T mod 2
        T = [[sum(E[i][a]*Am[a][b] for a in range(n))%2 for b in range(n)] for i in range(n)]
        C = [[sum(T[i][b]*E[j][b] for b in range(n))%2 for j in range(n)] for i in range(n)]
        if C == Bm: return True
    return False

t5, t6, t7 = tmpl_twin(5), tmpl_twin(6), tmpl_twin(7)
print("8. mod-2 congruence: tmpl(5)~tmpl(6)?", congruent_mod2(t5,t6),
      "| tmpl(5)~tmpl(7)?", congruent_mod2(t5,t7))
