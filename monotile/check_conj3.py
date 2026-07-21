import json
import numpy as np
import arena2
from arena2 import ROTS, ROT_KEY
from faceeq3d import EQ_IDX, EQ_OF, eq_norm

EQPERM = json.load(open("anyk3d_canonical.json"))["eqperm"]

def teq(ax, o1, o2):
    return EQ_IDX[eq_norm(EQ_OF[(ax, o1, o2)])]

# representative triple for each equation
rep = {}
for ax in range(3):
    for o1 in range(24):
        for o2 in range(24):
            rep.setdefault(teq(ax, o1, o2), (ax, o1, o2))
assert len(rep) == 84

E = np.eye(3, dtype=int)
PI = []
ok = True
for g in range(24):
    M = ROTS[g]
    Minv = M.T
    h = [ROT_KEY[tuple((M @ ROTS[o]).flatten())] for o in range(24)]
    hinv = [0]*24
    for i, j in enumerate(h): hinv[j] = i
    # tau_g: (ax, o1, o2) -> (b, hinv(o1), hinv(o2)) with sign from Minv @ E[ax]
    pi = [None]*84
    consistent = True
    for ax in range(3):
        w = Minv @ E[ax]
        b = int(np.flatnonzero(w)[0])
        sign = int(w[b])
        for o1 in range(24):
            for o2 in range(24):
                t2 = (b, hinv[o1], hinv[o2]) if sign == 1 else (b, hinv[o2], hinv[o1])
                e1, e2 = teq(ax, o1, o2), teq(*t2)
                if pi[e1] is None:
                    pi[e1] = e2
                elif pi[e1] != e2:
                    consistent = False
    if not consistent or sorted(pi) != list(range(84)):
        print(f"g={g}: consistent={consistent} bijective={sorted(x for x in pi if x is not None) == list(range(84))}")
        ok = False
    PI.append(pi)
print("pi_g well-defined permutation for all g:", ok)

# compare with EQPERM
def inv_perm(p):
    q = [0]*84
    for i, j in enumerate(p): q[j] = i
    return q
EQPi = [inv_perm(p) for p in EQPERM]
# rotation inverse index: g' with ROTS[g'] = M.T
ginv = [ROT_KEY[tuple(ROTS[g].T.flatten())] for g in range(24)]
same = sum(1 for g in range(24) if PI[g] == EQPERM[g])
same_inv = sum(1 for g in range(24) if PI[g] == EQPERM[ginv[g]])
same_epinv = sum(1 for g in range(24) if PI[g] == EQPi[g])
print(f"pi==EQPERM[g]: {same}/24, pi==EQPERM[ginv]: {same_inv}/24, pi==inv(EQPERM[g]): {same_epinv}/24")
json.dump(PI, open("anyk3d_tripleperm.json", "w"))
print("wrote anyk3d_tripleperm.json")
