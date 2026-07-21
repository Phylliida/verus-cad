import json

EQPERM = json.load(open("anyk3d_canonical.json"))["eqperm"]
PI = json.load(open("anyk3d_tripleperm.json"))

EP = {tuple(p): g for g, p in enumerate(EQPERM)}
match = {}
for g, p in enumerate(PI):
    t = tuple(p)
    if t in EP:
        match[g] = EP[t]
print("pi_g in EQPERM set:", len(match), "/24, map g->g':", match)

# orbits of a test set under each action
import random
rng = random.Random(1)
def orbit(PI, m):
    out = set()
    for p in PI:
        out.add(tuple(sorted(p[e] for e in m)))
    return out
same_orbits = True
for _ in range(20):
    m = tuple(sorted(rng.sample(range(84), rng.randrange(0, 30))))
    if orbit(PI, m) != orbit(EQPERM, m):
        same_orbits = False
        break
print("orbit sets coincide on 20 random profiles:", same_orbits)
