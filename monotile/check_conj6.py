import json
import numpy as np
import arena2
from arena2 import ROTS, ROT_KEY
from faceeq3d import EQ_IDX, EQ_OF, eq_norm

EQPERM = json.load(open("anyk3d_canonical.json"))["eqperm"]

def teq(ax, o1, o2):
    return EQ_IDX[eq_norm(EQ_OF[(ax, o1, o2)])]

bad = 0
R = [[ROT_KEY[tuple((ROTS[o] @ ROTS[g]).flatten())] for o in range(24)]
     for g in range(24)]
for g in range(24):
    for ax in range(3):
        for o1 in range(24):
            for o2 in range(24):
                lhs = EQPERM[g][teq(ax, o1, o2)]
                rhs = teq(ax, R[g][o1], R[g][o2])
                if lhs != rhs:
                    bad += 1
                    if bad < 4:
                        print("MISMATCH", g, ax, o1, o2, lhs, rhs)
print("EQPERM[g][teq(ax,o1,o2)] == teq(ax, r_g o1, r_g o2): bad =", bad,
      "of", 24*3*24*24)
json.dump(R, open("anyk3d_rmul.json", "w"))
