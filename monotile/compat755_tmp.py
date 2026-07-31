import os
os.environ["ARENA_K"] = "4"
import json
import numpy as np
import arena2

dec = json.load(open("color_755_decoration.json"))
faces = dec["faces"]
decarr = np.array([x + 1 for f in faces for x in f], dtype=np.int8)
placed = arena2.placed_vectors(decarr)

# compat with EQUALITY (colors) instead of complement
compat = np.zeros((3, 24, 24), dtype=bool)
for ax in range(3):
    pairs = arena2.IFACE_PAIRS[ax]
    for o1 in range(24):
        v1 = placed[o1]
        for o2 in range(24):
            v2 = placed[o2]
            compat[ax, o1, o2] = all(v1[i] == v2[j] for i, j in pairs)

# which base faces can show on world face w across all 24 orientations?
ROTS = arena2.ROTS
def face_shown(o, w):
    """base face shown on world direction w by orientation o"""
    # placed[o][j] for j on world face w -> base face of PERMINV[o][j]
    j = next(i for i, p in enumerate(arena2.PTS)
           if max(range(3), key=lambda k: abs(p[k])) == w // 2
           and p[w // 2] == (arena2.K if w % 2 == 0 else -arena2.K))
    return arena2.face_and_coords(arena2.PERMINV[o][j])[0]

import faceeq3d
for o in range(24):
    shown = [faceeq3d.face_and_coords(arena2.PERMINV[o][j])[0]
             for j in range(arena2.NPTS)]
    pass

# adjacency matrix by world face types
# for each orientation o, what base face shows on +x,-x,+y,-y,+z,-z
def world_faces(o):
    out = []
    for ax in range(3):
        for s in (arena2.K, -arena2.K):
            j = next(i for i, p in enumerate(arena2.PTS)
                     if p[ax] == s)
            out.append(faceeq3d.face_and_coords(arena2.PERMINV[o][j])[0])
    return out

# self-adjacency: compat[ax, o, o] for which (ax, o)?
print("self-adjacencies (ax, o) holding:")
for ax in range(3):
    ok = [o for o in range(24) if compat[ax, o, o]]
    print(f"  ax {ax}: {ok}")

# face-type pair counts: for ax=0, which (shown +x face of o1, shown -x face of o2) pairs hold?
from collections import Counter
for ax in range(3):
    cnt = Counter()
    for o1 in range(24):
        for o2 in range(24):
            if compat[ax, o1, o2]:
                cnt[(world_faces(o1)[2 * ax], world_faces(o2)[2 * ax + 1])] += 1
    print(f"ax {ax} allowed (pos-face, neg-face) pairs:", dict(sorted(cnt.items())))
