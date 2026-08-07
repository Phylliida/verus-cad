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

# ---- 3. reduced dimer model: exact SAT encoding
#
# Reduction (exact for #10, derived 2026-08-07; see DESIGN doc):
#   * each cube c picks an ordered adjacent face pair (A,B): A = face whose
#     absolute-even-vertex diagonal is marked, B = same for odd vertices;
#   * the axis-cyclic class of (axis A, axis B) must be +1 at even cubes,
#     -1 at odd cubes (the parity flip: for odd cubes the local E/O roles
#     swap, flipping the class) — 12 allowed pairs per cube;
#   * vertex glue: at every lattice vertex the 8 incident cubes agree on
#     whether it is marked (all-equal, no cardinality gate needed).
#
# Exactness: given a solution, l(v) = covered-by-incident-cubes is
# well-defined (glue) and every cube's marked set is an even face diagonal
# plus an odd face diagonal with the right class by parity, i.e. a member
# of orbit(#10); conversely every #10 tiling projects to a solution.
# (Verified below by lifting solutions back and by cross-checking SAT/UNSAT
# verdicts against corner_sat on the full orientation encoding.)

AXSIGN = {(0, 1): 1, (1, 2): 1, (2, 0): 1,
          (1, 0): -1, (2, 1): -1, (0, 2): -1}


def pairs_for(cube_parity):
    """The 12 allowed (A-face, B-face) ordered pairs for a cube of the
    given parity: adjacent faces (different axes) whose axis-cyclic class
    is +1 for even cubes, -1 for odd cubes."""
    want = 1 if cube_parity == 0 else -1
    return [(f, g) for f in FACES for g in FACES
            if f[0] != g[0] and AXSIGN[(f[0], g[0])] == want]


# sanity: for #10 the orbit on (even-mark face, odd-mark face) is exactly
# pairs_for(0) (the doc's class claim; handedness is NOT the invariant)
orbit_pairs = set()
for d_ in dec_orbit:
    orbit_pairs.add(cube_pair(d_))
assert orbit_pairs == set(pairs_for(0)), (orbit_pairs, pairs_for(0))
print("class claim OK: orbit(#10) on (E-face, O-face) = pairs_for(even)",
      flush=True)

PAIRS = [pairs_for(0), pairs_for(1)]


def marked_by(e, pair, cube_parity):
    """Is local corner e marked in a cube of the given parity whose
    (absolute-even face, absolute-odd face) is pair = (A, B)?"""
    f, g = pair
    ef, of = (f, g) if cube_parity == 0 else (g, f)  # local E/O faces
    loc_e = C.CORNERS[e]
    if parity(loc_e) == 0:
        return loc_e in face_vertices(ef)
    return loc_e in face_vertices(of)


def dimer_sat(dims, periodic, conf_budget=None):
    """Tri-state like C.corner_sat: (True, pair grid) / (False, None) /
    (None, None). periodic tori need all dims even (cube parity must be
    well-defined around the wrap)."""
    d1, d2, d3 = dims
    if periodic:
        assert all(d % 2 == 0 for d in dims), "parity ill-defined on odd tori"
    cells = [(x, y, z) for x in range(d1) for y in range(d2)
             for z in range(d3)]
    idx = {c: i for i, c in enumerate(cells)}
    cpar = {c: sum(c) % 2 for c in cells}

    def pvar(ci, j):
        return ci * 12 + j + 1

    top = len(cells) * 12

    def mvar(ci, e):
        return top + ci * 8 + e + 1

    cnf = []
    # exactly one pair per cube
    for ci, c in enumerate(cells):
        cnf.append([pvar(ci, j) for j in range(12)])
        for j1 in range(12):
            for j2 in range(j1 + 1, 12):
                cnf.append([-pvar(ci, j1), -pvar(ci, j2)])
    # mark channeling: mvar(ci,e) <-> OR of pairs marking corner e
    for ci, c in enumerate(cells):
        for e in range(8):
            sup = [j for j in range(12)
                   if marked_by(e, PAIRS[cpar[c]][j], cpar[c])]
            assert sup, (c, e)
            for j in sup:
                cnf.append([-pvar(ci, j), mvar(ci, e)])
            cnf.append([-mvar(ci, e)] + [pvar(ci, j) for j in sup])
    # vertex glue: all 8 incident marks equal (chain of equivalences)
    if periodic:
        verts = list(cells)
    else:
        verts = [(x, y, z) for x in range(1, d1) for y in range(1, d2)
                 for z in range(1, d3)]
    for v in verts:
        inc = []
        for e in C.CORNERS:
            if periodic:
                c = tuple((v[k] - e[k]) % dims[k] for k in range(3))
            else:
                c = (v[0] - e[0], v[1] - e[1], v[2] - e[2])
            inc.append(mvar(idx[c], C.cidx(e)))
        for i in range(7):
            cnf.append([-inc[i], inc[i + 1]])
            cnf.append([inc[i], -inc[i + 1]])

    with Glucose3(bootstrap_with=cnf) as s:
        if conf_budget is None:
            r = s.solve()
        else:
            s.conf_budget(conf_budget)
            r = s.solve_limited()
        if r is None:
            return None, None
        if not r:
            return False, None
        pos = set(x for x in s.get_model() if x > 0)
        grid = {}
        for c in cells:
            ci = idx[c]
            grid[c] = next(j for j in range(12) if pvar(ci, j) in pos)
        return True, grid


def dimer_lift_check(grid, dims, periodic):
    """Lift a reduced-model solution and verify every cube's marked-corner
    pattern lies in orbit(#10). (The all-equal glue makes the induced
    vertex coloring well-defined by construction.)"""
    decs2 = C.census(2)
    dec10 = decs2[10]
    orb = {tuple(dec10[C.SIG[o][p]] for p in range(8)) for o in range(24)}
    for c, j in grid.items():
        cp = sum(c) % 2
        pat = tuple(1 if marked_by(e, PAIRS[cp][j], cp) else 0
                    for e in range(8))
        if pat not in orb:
            return False
    return True


print("--- reduced dimer model: profile vs corner_sat (#10) ---", flush=True)
show10 = C.show_table(C.census(2)[10])
shapes = [
    ("box", (2, 2, 2)), ("box", (3, 3, 3)), ("box", (4, 3, 3)),
    ("box", (4, 4, 3)), ("box", (4, 4, 4)),
    ("torus", (2, 2, 2)), ("torus", (2, 2, 4)), ("torus", (2, 4, 4)),
    ("torus", (4, 4, 4)),
]
for kind, dims in shapes:
    per = kind == "torus"
    ok_d, grid = dimer_sat(dims, per, 2_000_000)
    ok_c, grid_c = C.corner_sat(show10, dims, "equal", per, 2_000_000)
    lift = ""
    if ok_d:
        lift = f", lift-check {dimer_lift_check(grid, dims, per)}"
    tag = {True: "SAT", False: "UNSAT", None: "?"}
    match = "MATCH" if ok_d == ok_c else "**MISMATCH**"
    print(f"  {kind} {dims}: dimer {tag[ok_d]} vs corner_sat {tag[ok_c]}"
          f"  {match}{lift}", flush=True)
