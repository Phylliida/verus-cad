"""Export the cube-and-conquer tree as a compact preorder shape for Lean.

Reads cube_certs/manifest.json (leaf cubes), reconstructs the DFS tree (cubes are
prefixes of `order`), emits:
  - order  : the split-var sequence (List Nat)
  - shape  : preorder shape string ('T'=internal split on order[depth], 'F'=leaf)
Round-trip verified (parse shape back -> cube set == manifest cube set). Writes a
Lean file ConcreteTree.lean: realTree := parseTree order shape, + cover, + the
huns skeleton (per-cube UNSAT as a cake_lpr-backed axiom).
"""
import json, sys
from arena2 import PTS

ROOT = '/home/bepis/prog/verus-cad/monotile'
LEAN = '/home/bepis/prog/verus-cad/lean-flocq/LeanFlocq/ConcreteTree.lean'

centers, corners, edges = [], [], []
for i, p in enumerate(PTS):
    ax = max(range(3), key=lambda k: abs(p[k]))
    tang = sorted(abs(p[k]) for k in range(3) if k != ax)
    if tuple(tang) == (0, 0): centers.append(i)
    elif tuple(tang) == (2, 2): corners.append(i)
    else: edges.append(i)
order = centers + corners[:4] + corners[4:] + edges
pos = {order[i]: i for i in range(len(order))}

manifest = json.load(open(f'{ROOT}/cube_certs/manifest.json'))
cubes = [c['cube'] for c in manifest]

def to_path(cube):
    d = sorted(cube, key=lambda vb: pos[vb[0]])
    for i, (v, b) in enumerate(d):
        assert v == order[i], f"cube not an order-prefix at depth {i}: {cube}"
    return [b for (v, b) in d]

paths = [to_path(c) for c in cubes]

def build_shape(ps):
    if len(ps) == 1 and ps[0] == []:
        return [False]
    assert all(p for p in ps), "empty path coincides with non-leaf (not prefix-free)"
    lo = [p[1:] for p in ps if p[0] is False]
    hi = [p[1:] for p in ps if p[0] is True]
    assert len(lo) + len(hi) == len(ps)
    return [True] + build_shape(lo) + build_shape(hi)

shape = build_shape(paths)

# round-trip: parse shape -> cube set, compare to manifest cube set
def parse(sh, depth, i):
    if sh[i]:
        lo, i1 = parse(sh, depth + 1, i + 1)
        hi, i2 = parse(sh, depth + 1, i1)
        return ([[(order[depth], False)] + c for c in lo] +
                [[(order[depth], True)] + c for c in hi], i2)
    return ([[]], i + 1)

recovered, ni = parse(shape, 0, 0)
assert ni == len(shape), f"shape not fully consumed: {ni}/{len(shape)}"
orig = {frozenset((v, b) for v, b in c) for c in cubes}
rec = {frozenset(c) for c in recovered}
assert orig == rec, f"ROUND-TRIP MISMATCH: {len(orig)} vs {len(rec)}, sym diff {len(orig ^ rec)}"

print(f"leaves={len(cubes)} shape_tokens={len(shape)} internal={shape.count(True)} "
      f"leaf_tokens={shape.count(False)} max_depth={max(len(p) for p in paths)}")
print("ROUND-TRIP OK: parseTree order shape reproduces exactly the manifest cube set")

shapeStr = ''.join('T' if b else 'F' for b in shape)
orderStr = ', '.join(str(v) for v in order)
lean = f'''/-
The concrete cube-and-conquer tree for `genArenaCNF`, function-generated from the
cake_lpr-verified manifest ({len(cubes)} leaves). `realTree.cubes` = exactly the
cubes cake_lpr verified UNSAT (round-trip checked in export_tree.py). The cover is
kernel-proven (`VTree.covers`); per-cube UNSAT is the cake_lpr axiom.
-/
import LeanFlocq.CubeCover
import LeanFlocq.GenArenaLexEncBody

open CubeCover Std.Sat

namespace ConcreteTree

/-- DFS split order (6 centers, 8 corners, 40 edges). -/
def order : List Nat := [{orderStr}]

/-- preorder shape: 'T' = internal (split on order[depth]), 'F' = leaf. -/
def shapeStr : String :=
  "{shapeStr}"

/-- the real search tree, reconstructed from the exported shape. -/
def realTree : VTree := parseTree order (shapeStr.data.map (· == 'T'))

/-- **cover** — kernel-proven, no per-cube enumeration in the proof. -/
theorem realCover (a : Nat → Bool) : ∃ cube ∈ realTree.cubes, CNF.eval a cube = true :=
  realTree.covers a

/-- per-cube UNSAT, verified externally by cake_lpr (CakeML/HOL4). This is the
sole cake_lpr-trusted input; the cover + composition above are kernel-proven. -/
axiom perCubeUnsat :
    ∀ cube ∈ realTree.cubes, (GenArenaLex.genArenaCNF ++ cube).Unsat

/-- **`huns` assembled**: `genArenaCNF.Unsat`, cover kernel-proven, per-cube
UNSAT by cake_lpr. -/
theorem huns : GenArenaLex.genArenaCNF.Unsat := realTree.unsat _ perCubeUnsat

#check @huns

end ConcreteTree
'''
open(LEAN, 'w').write(lean)
print(f"wrote {LEAN} (shapeStr {len(shapeStr)} chars)")
