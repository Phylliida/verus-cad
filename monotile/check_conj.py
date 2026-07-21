import json
import numpy as np
import arena2
from arena2 import ROTS, ROT_KEY
from faceeq3d import EQ_IDX, EQ_OF, eq_norm

canon = json.load(open("anyk3d_canonical.json"))
EQPERM = canon["eqperm"]

def teq(ax, o1, o2):
    return EQ_IDX[eq_norm(EQ_OF[(ax, o1, o2)])]

E = np.eye(3, dtype=int)
bad = 0
for g in range(24):
    M = ROTS[g]
    gmap = [ROT_KEY[tuple((M @ ROTS[o]).flatten())] for o in range(24)]
    for ax in range(3):
        w = M @ E[ax]
        bx = int(np.flatnonzero(w)[0])
        sign = int(w[bx])
        for o1 in range(24):
            for o2 in range(24):
                lhs = EQPERM[g][teq(ax, o1, o2)]
                rhs = (teq(bx, gmap[o1], gmap[o2]) if sign == 1
                       else teq(bx, gmap[o2], gmap[o1]))
                if lhs != rhs:
                    bad += 1
                    if bad < 4:
                        print("MISMATCH", g, ax, o1, o2, lhs, rhs)
print("conjugation identity: bad =", bad, "of", 24*3*24*24)
