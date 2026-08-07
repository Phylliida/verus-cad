"""Chirality test for the Phase-B conjecture:

    corner decoration tiles Z^3  <=>  decoration is achiral
                                   <=>  period-(2,2,2) witness exists.

A decoration is achiral iff its mirror image (reflect corner coordinate
x -> 1-x) lies in its own rotation orbit. Compare the achiral set against
the actual periodic/empty verdicts for:
  * corner-only T=2 (23)  — corner3d_T2_results.jsonl
  * corner-only T=3 (333) — corner3d_T3_results.jsonl
  * mixed face+corner T=2 (776) — corner_mixed3d_T2_results.jsonl
    (joint achirality: one reflection applied to faces AND corners must
    land in the joint rotation orbit)

Also prints the Burnside cross-check of achiral counts (rotation orbits
A + 2C vs full-octahedral orbits A + C).

Run:  ./runpy.sh corner3d_chiral.py
"""
import json
import sys

sys.argv = ["corner3d.py"]
import corner3d as C3

SIG = C3.SIG
ROTS = C3.ROTS

# corner reflection x -> 1-x, in CORNERS list-position numbering
MIRROR_C = [C3.CORNERS.index((1 - c[0], c[1], c[2])) for c in C3.CORNERS]


def achiral_corner(dec):
    mir = tuple(dec[MIRROR_C[p]] for p in range(8))
    return any(all(mir[p] == dec[SIG[o][p]] for p in range(8))
               for o in range(24))


def load_verdicts(path):
    out = {}
    for line in open(path):
        r = json.loads(line)
        if r["rule"] == "equal":
            out[r["i"]] = r["verdict"]
    return out


def compare(name, decs, verdicts):
    mism = []
    n_achiral = 0
    for i, dec in enumerate(decs):
        ach = achiral_corner(dec)
        n_achiral += ach
        periodic = verdicts[i].startswith("periodic")
        if ach != periodic:
            mism.append((i, ach, verdicts[i]))
    print(f"{name}: {len(decs)} decorations, {n_achiral} achiral; "
          f"verdict-chirality mismatches: {len(mism)}")
    for m in mism[:10]:
        print("   MISMATCH:", m)
    return n_achiral, mism


# corner-only T=2 and T=3
decs2 = C3.census(2)
v2 = load_verdicts("corner3d_T2_results.jsonl")
compare("corner T=2", decs2, v2)

decs3 = C3.census(3)
v3 = load_verdicts("corner3d_T3_results.jsonl")
compare("corner T=3", decs3, v3)

# mixed face+corner T=2: joint achirality under the SAME reflection
import corner_mixed3d as M

SIGF = M.SIGF
# face reflection x -> 1-x swaps +x and -x faces (f = 2a + side)
MIRROR_F = [1, 0, 2, 3, 4, 5]


def achiral_mixed(dec):
    fd, cd = dec[:6], dec[6:]
    mir_f = tuple(fd[MIRROR_F[f]] for f in range(6))
    mir_c = tuple(cd[MIRROR_C[p]] for p in range(8))
    for o in range(24):
        if (all(mir_f[f] == fd[SIGF[o][f]] for f in range(6))
                and all(mir_c[p] == cd[SIG[o][p]] for p in range(8))):
            return True
    return False


decs_m = M.census()
vm = {}
for line in open("corner_mixed3d_T2_results.jsonl"):
    r = json.loads(line)
    vm[r["i"]] = r["verdict"]
mism = []
n_achiral = 0
for i, dec in enumerate(decs_m):
    ach = achiral_mixed(dec)
    n_achiral += ach
    periodic = vm[i].startswith("periodic")
    if ach != periodic:
        mism.append((i, ach, vm[i]))
print(f"mixed T=2: {len(decs_m)} decorations, {n_achiral} achiral; "
      f"verdict-chirality mismatches: {len(mism)}")
for m in mism[:10]:
    print("   MISMATCH:", m)
