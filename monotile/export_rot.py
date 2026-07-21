import json
import numpy as np
import arena2
from arena2 import ROTS, ROT_KEY

R = [[ROT_KEY[tuple((ROTS[o] @ ROTS[g]).flatten())] for o in range(24)]
     for g in range(24)]
rotinv = [ROT_KEY[tuple(ROTS[g].T.flatten())] for g in range(24)]
# sanity: group
for g in range(24):
    for o in range(24):
        assert R[rotinv[g]][R[g][o]] == o and R[g][R[rotinv[g]][o]] == o
json.dump({"rmul": R, "rotInv": rotinv}, open("anyk3d_rmul.json", "w"))

rm_body = ",\n  ".join("#[" + ", ".join(map(str, p)) + "]" for p in R)
ri_body = ", ".join(map(str, rotinv))
out = f"""
/-- Right multiplication by rotation g on orientations:
rmul[g][o] = the index of ROTS[o] @ ROTS[g]. -/
def rmul : Array (Array Nat) := #[
  {rm_body}
]

/-- Index of the inverse rotation: ROTS[rotInv[g]] = ROTS[g].T. -/
def rotInv : Array Nat := #[{ri_body}]

end AnyK3D
"""
path = "../lean-flocq/LeanFlocq/AnyK3DFrontier.lean"
txt = open(path).read()
assert txt.rstrip().endswith("end AnyK3D")
txt = txt.rstrip()[: -len("end AnyK3D")] + out
txt = txt.replace(
    "   checks). -/",
    "   checks). -/\n   rmul/rotInv: orientation right-multiplication and\n   inverse-rotation tables (monotile/export_rot.py, group-checked). -/")
open(path, "w").write(txt)
print("appended rmul + rotInv to AnyK3DFrontier.lean")
