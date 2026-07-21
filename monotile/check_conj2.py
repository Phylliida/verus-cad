import json
import numpy as np
import arena2
from arena2 import ROTS, ROT_KEY
from faceeq3d import EQ_IDX, EQ_OF, eq_norm

EQPERM = json.load(open("anyk3d_canonical.json"))["eqperm"]

def teq(ax, o1, o2):
    return EQ_IDX[eq_norm(EQ_OF[(ax, o1, o2)])]

# inverse of a permutation
def inv_perm(p):
    q = [0]*len(p)
    for i, j in enumerate(p): q[j] = i
    return q

E = np.eye(3, dtype=int)
Hs = {
  "L":  lambda M: [ROT_KEY[tuple((M @ ROTS[o]).flatten())] for o in range(24)],
  "Li": lambda M: [ROT_KEY[tuple((M.T @ ROTS[o]).flatten())] for o in range(24)],
  "R":  lambda M: [ROT_KEY[tuple((ROTS[o] @ M).flatten())] for o in range(24)],
  "Ri": lambda M: [ROT_KEY[tuple((ROTS[o] @ M.T).flatten())] for o in range(24)],
}
best = []
for ep_name, epf in [("EP", lambda g: EQPERM[g]), ("EPi", lambda g: inv_perm(EQPERM[g]))]:
    for Mname, Mf in [("M", lambda M: M), ("Mt", lambda M: M.T)]:
        for hname in Hs:
            bad = 0
            for g in range(24):
                M = ROTS[g]
                ep = epf(g)
                h = Hs[hname](M)
                Mp = Mf(M)
                for ax in range(3):
                    w = Mp @ E[ax]
                    bx = int(np.flatnonzero(w)[0])
                    sign = int(w[bx])
                    for o1 in range(24):
                        for o2 in range(24):
                            lhs = ep[teq(ax, o1, o2)]
                            rhs = (teq(bx, h[o1], h[o2]) if sign == 1
                                   else teq(bx, h[o2], h[o1]))
                            bad += (lhs != rhs)
            print(f"{ep_name} {Mname} {hname}: bad={bad}")
