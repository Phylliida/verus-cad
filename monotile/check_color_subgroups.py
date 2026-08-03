"""Probe: which subgroups of the 8-element color gain group are
exact-stabilizer feasible (K=2,3,4 2-color patterns)?"""
from color_census import setup_color, feasibility_witnesses

nf, n, G, eqmaps = setup_color()
subs, missing, witnesses = feasibility_witnesses(G)
print('group order', len(G))
print('subgroups:', len(subs))
print('missing:', len(missing))
for H in sorted(subs, key=lambda h: (len(h), sorted(h))):
    tag = 'MISSING' if H in missing else f'K={witnesses[H][0]}'
    print(f'  size {len(H)}: {tag}')
