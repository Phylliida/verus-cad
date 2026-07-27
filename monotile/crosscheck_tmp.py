import json
import numpy as np
import arena2

dec = json.load(open("color_755_decoration.json"))
faces = dec["faces"]
# arena2 PTS for K=4: NPTS = 6*16 = 96; arena2's K is read from env ARENA_K
import os
os.environ["ARENA_K"] = "4"
import importlib
importlib.reload(arena2)

decarr = np.array([x + 1 for f in faces for x in f], dtype=np.int8)
placed = arena2.placed_vectors(decarr)
compat = arena2.compat_tables(placed)

# JS convention check: equality rule (colors equal, not complementary)
# arena2 compat is bump/dent COMPLEMENT (v1[i] + v2[j] == 0); for colors
# we need EQUALITY: recompute directly
NPTS = arena2.NPTS
ok = {}
for ax in range(3):
    for o1 in range(24):
        for o2 in range(24):
            good = all(placed[o1][i] == placed[o2][j]
                       for i, j in arena2.PAIRS[ax][o1][o2]
                       for _ in [0]) if False else None
# PAIRS maps (o1,o2) to pairs of point indices (jA, jB) — compat equality:
out = {}
for ax in range(3):
    for o1 in range(24):
        for o2 in range(24):
            out[(ax, o1, o2)] = all(
                placed[o1][jA] == placed[o2][jB]
                for jA, jB in arena2.IFACE_PAIRS[ax])
allowed = [o2 for o2 in range(24) if out[(0, 0, o2)]]
print("py allowed at +x (rot 0 at origin):", ",".join(map(str, allowed)))
allowed = [o2 for o2 in range(24) if out[(1, 0, o2)]]
print("py allowed at +y:", ",".join(map(str, allowed)))
allowed = [o2 for o2 in range(24) if out[(2, 0, o2)]]
print("py allowed at +z:", ",".join(map(str, allowed)))
