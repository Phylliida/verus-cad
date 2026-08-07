"""Phase B hard direction: the dimer/screw mechanism for chiral corners.

For the chiral T=2 pair #10/#11 (4 marks = even-tet edge + odd-tet edge
in a fixed screw), the tiling constraint reduces EXACTLY to a face-dimer
model:
  * each cube picks an E-face (carrying its 2 even-parity-vertex marks,
    which always form a face diagonal) and an O-face (odd marks);
  * the two faces must be adjacent with screw handedness = h(d);
  * vertex glue: at every even vertex v, the e-faces through v cover all
    8 incident cubes or none (sum of x_f over the 12 faces at v is 0 or
    4); similarly odd vertices with o-faces.

This script checks three things:
  1. EXACTNESS of the reduction for #10: the rotation orbit of its
     (E-face, O-face) pair = precisely the 12 adjacent pairs with
     handedness h(d) = +1.
  2. RIGIDITY: subsets of the even (FCC) vertices meeting every
     cube-tetrahedron in exactly 2 points — enumerate all solutions on
     even tori; are they forced to be axis-layered (x/y/z mod 2, 2
     phases -> 6 solutions)?
  3. The reduced dimer model reproduces #10's verdict profile
     (box 3^3 SAT, box 4^3 UNSAT, small tori UNSAT).

Run:  ./runpy.sh corner3d_dimer.py
"""
import itertools
import sys

sys.argv = ["corner3d.py"]
import corner3d as C
from pysat.solvers import Glucose3
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool

# ------------------------------------------------- face/diagonal geometry
# faces of the unit cube: (axis, side); face (a, s) = {x_a = s}
FACES = [(a, s) for a in range(3) for s in (0, 1)]


def face_vertices(f):
    a, s = f
    others = [b for b in range(3) if b != a]
    out = []
    for u, w in itertools.product((0, 1), repeat=2):
        v = [0, 0, 0]
        v[a] = s
        v[others[0]] = u
        v[others[1]] = w
        out.append(tuple(v))
    return out


def parity(v):
    return sum(v) % 2


def diag(f, par):
    """The diagonal of face f joining its two corners of parity par."""
    vs = [v for v in face_vertices(f) if parity(v) == par]
    assert len(vs) == 2
    return tuple(vs)


def handedness(f, g):
    """Screw sign of (even diagonal of f, odd diagonal of g) for one cube.
    Canonical directions: lexicographically smaller -> larger endpoint.
    Returns +1/-1, or 0 if opposite faces / degenerate."""
    if f[0] == g[0]:
        return 0
    e1, e2 = sorted(diag(f, 0))
    o1, o2 = sorted(diag(g, 1))
    de = [e2[k] - e1[k] for k in range(3)]
    do = [o2[k] - o1[k] for k in range(3)]
    dm = [(o1[k] + o2[k] - e1[k] - e2[k]) / 2 for k in range(3)]
    det = (de[0] * (do[1] * dm[2] - do[2] * dm[1])
           - de[1] * (do[0] * dm[2] - do[2] * dm[0])
           + de[2] * (do[0] * dm[1] - do[1] * dm[0]))
    assert det != 0, (f, g)
    return 1 if det > 0 else -1


def cube_pair(dec):
    """The (E-face, O-face) pair of a 2-even-mark + 2-odd-mark decoration."""
    em = [C.CORNERS[p] for p in range(8) if dec[p] == 1 and parity(C.CORNERS[p]) == 0]
    om = [C.CORNERS[p] for p in range(8) if dec[p] == 1 and parity(C.CORNERS[p]) == 1]
    assert len(em) == 2 and len(om) == 2
    ef = next(f for f in FACES if all(v in face_vertices(f) for v in em))
    of = next(f for f in FACES if all(v in face_vertices(f) for v in om))
    return ef, of


def rot_face(sig_e):
    """Rotation as a map on faces, derived from its corner action."""
    out = []
    for f in FACES:
        vs = face_vertices(f)
        imgs = [C.CORNERS[sig_e[C.CORNERS.index(v)]] for v in vs]
        out.append(next(g for g in FACES
                        if set(face_vertices(g)) == set(imgs)))
    return out


# ---- 1. exactness of the reduction for #10
decs = C.census(2)
dec10 = decs[10]
ef0, of0 = cube_pair(dec10)
h0 = handedness(ef0, of0)
print(f"#10: E-face {ef0}, O-face {of0}, handedness {h0}")
# rotation orbit on ordered face pairs AND on the decoration itself
SIGFACE = [rot_face(C.SIG[o]) for o in range(24)]
orbit = {(SIGFACE[o][FACES.index(ef0)], SIGFACE[o][FACES.index(of0)])
         for o in range(24)}
adjacent_h0 = {(f, g) for f in FACES for g in FACES
               if f != g and handedness(f, g) == h0}
print(f"  (E,O)-pair orbit size {len(orbit)}; adjacent pairs with h={h0}: "
      f"{len(adjacent_h0)}; equal: {orbit == adjacent_h0}")

dec_orbit = {tuple(dec10[C.SIG[o][p]] for p in range(8)) for o in range(24)}
dec11 = decs[11]
print(f"  #10 decoration orbit size {len(dec_orbit)}; "
      f"#11 in orbit: {dec11 in dec_orbit}; #11 = {dec11}")
pair_of = {}
for d_ in dec_orbit:
    pair_of.setdefault(cube_pair(d_), set()).add(d_)
print(f"  distinct (E,O) pairs in orbit: {len(pair_of)}")
for pr, ds in sorted(pair_of.items()):
    print(f"    pair {pr}: {len(ds)} decorations, h={handedness(*pr)}")

# ---- 2. rigidity of 2-per-tet subsets on even tori
def rigidity(dims, cap=3000):
    d1, d2, d3 = dims
    assert all(d % 2 == 0 for d in dims)
    verts = [(x, y, z) for x in range(d1) for y in range(d2)
             for z in range(d3)]
    vidx = {v: i + 1 for i, v in enumerate(verts)}
    cnf = []
    for c in verts:  # every cube: exactly 2 of its 4 even corners
        lits = []
        for p in C.CORNERS:
            v = tuple((c[k] + p[k]) % dims[k] for k in range(3))
            if parity(v) == 0:
                lits.append(vidx[v])
        assert len(lits) == 4
        # exactly-2-of-4, no aux vars:
        for tri in itertools.combinations(lits, 3):
            cnf.append([-x for x in tri])   # at most 2 (no 3 true)
            cnf.append([x for x in tri])    # at least 2 (no 3 false)
    models = []
    with Glucose3(bootstrap_with=cnf) as s:
        for m in s.enum_models():
            pos = {x for x in m if x > 0}
            models.append({v for v in verts if vidx[v] in pos})
            if len(models) >= cap:
                break
    def layered(M):
        for a in range(3):
            for ph in (0, 1):
                if all((v[a] % 2 == ph) == (v in M) for v in verts
                       if parity(v) == 0):
                    return (a, ph)
        return None
    cls = {}
    for M in models:
        cls[layered(M)] = cls.get(layered(M), 0) + 1
    print(f"rigidity {dims}: {len(models)} solutions"
          f"{' (capped)' if len(models) >= cap else ''}, classes: {cls}",
          flush=True)


rigidity((4, 4, 4))
rigidity((6, 6, 6))

# ---- 3. reduced dimer model reproduces #10's profile
# WIP (parked 2026-08-07): the vertex-glue encoding (sum over the 12
# faces at each vertex in {0,4}) needs a proper cardinality gate; the
# exactness + rigidity checks above are complete and are the load-bearing
# evidence for the reduction. Resume here when the 3D proof work picks up.
print("parts 1-2 done (dimer SAT encoding parked as WIP)")
