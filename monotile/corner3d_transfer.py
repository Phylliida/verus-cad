"""Phase B hard direction: transfer-graph analysis of the reduced dimer
model (corner3d_dimer.py part 3) on small cylinders.

Cylinder = box cross-section W x H, extended along z. A slice is one
layer of W*H cubes; the interface between slices is the grid of
INTERIOR vertex marks of the shared plane: (W-1)*(H-1) bits (9 bits for
the critical 4x4 cross-section). Glue at an interior plane vertex is
"all 8 incident cube marks equal", which factors as: both slices' (up
to) 4 incident marks equal the interface bit.

R_k(B, T): slice k (cube parity (x+y+k)%2) admits pair assignments with
bottom interface B and top interface T. Forward reachability from a
free box end:

    S_1     = { T : R_0(*, T) }                    (1-slice boxes)
    S_{k+1} = { T : exists B in S_k, R_k(B, T) }

Box (W,H,L) is SAT iff S_L is nonempty. Empirically (corner3d_dimer):
4x4 dies at L=3, 4x3 and 3x3 survive at L=3. This script maps where
each cross-section dies and inspects the reachable sets for the
invariant that kills 4x4 — the candidate minimal contradiction.

Run:  ./runpy.sh corner3d_transfer.py
"""
import itertools
import sys

sys.argv = ["corner3d.py"]
import corner3d as C
from pysat.solvers import Glucose3

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


FV = {f: set(face_vertices(f)) for f in FACES}


def parity(v):
    return sum(v) % 2


AXSIGN = {(0, 1): 1, (1, 2): 1, (2, 0): 1,
          (1, 0): -1, (2, 1): -1, (0, 2): -1}

PAIRS = [
    [(f, g) for f in FACES for g in FACES
     if f[0] != g[0] and AXSIGN[(f[0], g[0])] == sgn]
    for sgn in (1, -1)
]


def marked_by(e, pair, cube_parity):
    f, g = pair
    ef, of = (f, g) if cube_parity == 0 else (g, f)
    loc = C.CORNERS[e]
    return loc in FV[ef] if parity(loc) == 0 else loc in FV[of]


class SliceSolver:
    """SAT for one W x H slice with interface bits as free variables.

    Interfaces are bit-vectors over interior plane vertices
    (x, y), 1 <= x < W, 1 <= y < H, bit index (x-1) + (W-1)*(y-1).
    ch_bottom/ch_top: whether the plane's vertices are box-interior
    (channeled to the bits) or box-boundary (unconstrained).
    """

    def __init__(self, W, H, kpar, ch_bottom=True, ch_top=True):
        self.W, self.H = W, H
        cells = [(x, y) for x in range(W) for y in range(H)]
        self.idx = {c: i for i, c in enumerate(cells)}
        self.cpar = {c: (c[0] + c[1] + kpar) % 2 for c in cells}

        # variable blocks (computed once — do NOT close over a mutated
        # accumulator or the blocks alias each other)
        n_pair = len(cells) * 12
        n_mark = n_pair + len(cells) * 8
        n_bot = n_mark + (W - 1) * (H - 1)

        def pvar(ci, j):
            return ci * 12 + j + 1

        def mvar(ci, e):
            return n_mark - len(cells) * 8 + ci * 8 + e + 1

        self.mvar = mvar

        def bbit(x, y):
            return n_bot - (W - 1) * (H - 1) + (x - 1) + (W - 1) * (y - 1) + 1

        def tbit(x, y):
            return n_bot + (x - 1) + (W - 1) * (y - 1) + 1

        self.bbit, self.tbit = bbit, tbit
        self.nbits = (W - 1) * (H - 1)

        cnf = []
        for ci, c in enumerate(cells):
            cnf.append([pvar(ci, j) for j in range(12)])
            for j1 in range(12):
                for j2 in range(j1 + 1, 12):
                    cnf.append([-pvar(ci, j1), -pvar(ci, j2)])
        for ci, c in enumerate(cells):
            for e in range(8):
                sup = [pvar(ci, j) for j in range(12)
                       if marked_by(e, PAIRS[self.cpar[c]][j],
                                    self.cpar[c])]
                for lit in sup:
                    cnf.append([-lit, mvar(ci, e)])
                cnf.append([-mvar(ci, e)] + sup)
        # interface channeling at interior vertices of channeled planes
        for plane, bit, ch in ((0, bbit, ch_bottom), (1, tbit, ch_top)):
            if not ch:
                continue
            for x in range(1, W):
                for y in range(1, H):
                    b = bit(x, y)
                    for i in (x - 1, x):
                        for j in (y - 1, y):
                            if (i, j) in self.idx:
                                e = C.cidx((x - i, y - j, plane))
                                m = mvar(self.idx[(i, j)], e)
                                cnf.append([-m, b])
                                cnf.append([m, -b])
        self.cnf = cnf

    def image(self, B):
        """All T such that the slice goes from bottom interface B."""
        assum = [self.bbit(x, y) if (B >> ((x - 1) + (self.W - 1) * (y - 1))) & 1
                 else -self.bbit(x, y)
                 for x in range(1, self.W) for y in range(1, self.H)]
        out = set()
        with Glucose3(bootstrap_with=self.cnf) as s:
            while s.solve(assumptions=assum):
                m = set(v for v in s.get_model() if v > 0)
                T = 0
                block = []
                for x in range(1, self.W):
                    for y in range(1, self.H):
                        b = self.tbit(x, y)
                        i = (x - 1) + (self.W - 1) * (y - 1)
                        if b in m:
                            T |= 1 << i
                            block.append(-b)
                        else:
                            block.append(b)
                out.add(T)
                s.add_clause(block)
        return out

    def feasible(self, B=None):
        """SAT check with bottom interface B fixed (None = free)."""
        assum = []
        if B is not None:
            assum = [
                self.bbit(x, y)
                if (B >> ((x - 1) + (self.W - 1) * (y - 1))) & 1
                else -self.bbit(x, y)
                for x in range(1, self.W) for y in range(1, self.H)]
        with Glucose3(bootstrap_with=self.cnf) as s:
            return bool(s.solve(assumptions=assum))


class Cylinder:
    """Transfer machinery for cross-section W x H.

    first[k]: slice with free bottom, channeled top (box start)
    mid[k]:   both planes channeled (interior slice)
    last[k]:  channeled bottom, free top (box end)
    k = slice parity.
    """

    def __init__(self, W, H):
        self.W, self.H = W, H
        self.first = [SliceSolver(W, H, k, ch_bottom=False) for k in (0, 1)]
        self.mid = [SliceSolver(W, H, k) for k in (0, 1)]
        self.last = [SliceSolver(W, H, k, ch_top=False) for k in (0, 1)]
        self._img = {}  # (k, B) -> image set cache

    def image(self, k, B):
        if (k, B) not in self._img:
            self._img[(k, B)] = self.mid[k % 2].image(B)
        return self._img[(k, B)]

    def reachable(self, max_len):
        """S_1, S_2, ...: interfaces reachable after 1, 2, ... slices
        (S_k = top of slice k-1)."""
        S = self._first_image()
        hist = [S]
        k = 1
        while S and k < max_len:
            nxt = set()
            for B in S:
                nxt |= self.image(k, B)
            S = nxt
            hist.append(S)
            k += 1
        return hist

    def _first_image(self):
        out = set()
        s0 = self.first[0]
        n = s0.nbits
        with Glucose3(bootstrap_with=s0.cnf) as s:
            while s.solve():
                m = set(v for v in s.get_model() if v > 0)
                T = 0
                block = []
                for x in range(1, self.W):
                    for y in range(1, self.H):
                        b = s0.tbit(x, y)
                        i = (x - 1) + (self.W - 1) * (y - 1)
                        if b in m:
                            T |= 1 << i
                            block.append(-b)
                        else:
                            block.append(b)
                out.add(T)
                s.add_clause(block)
        return out

    def box_sat(self, L):
        """Box (W, H, L) satisfiable in the reduced model?"""
        if L == 1:
            return True
        hist = self.reachable(L - 1)  # S_1 .. S_{L-1}
        if len(hist) < L - 1 or not hist[-1]:
            return False
        sv = self.last[(L - 1) % 2]
        return any(sv.feasible(B) for B in hist[-1])

    def torus_sat(self, L):
        """z-periodic cylinder of length L (L even): closed walk of
        length L through alternating slice parities, i.e. B_0 with
        B_0 in (image_{L-1} o ... o image_0)(B_0)."""
        assert L % 2 == 0
        # forward-reach from every start state, tracking the start
        cur = {B: {B} for B in range(1 << self.mid[0].nbits)}
        for k in range(L):
            nxt = {}
            for B0, dests in cur.items():
                s = set()
                for B in dests:
                    s |= self.image(k, B)
                nxt[B0] = s
            cur = nxt
        return any(B0 in dests for B0, dests in cur.items())


def show_bits(S, W, H):
    """Render an interface set as 2D bit grids."""
    rows = []
    for T in sorted(S):
        grid = []
        for y in range(1, H):
            row = "".join(
                "1" if (T >> ((x - 1) + (W - 1) * (y - 1))) & 1 else "."
                for x in range(1, W))
            grid.append(row)
        rows.append("/".join(grid))
    return rows


def main():
    print("=== box death table (transfer) ===", flush=True)
    cyls = {}
    for W, H in [(2, 2), (2, 3), (3, 3), (2, 4), (3, 4), (4, 3), (4, 4)]:
        cyl = Cylinder(W, H)
        cyls[(W, H)] = cyl
        prof = [cyl.box_sat(L) for L in range(1, 7)]
        print(f"  {W}x{H}: box L=1..6 SAT = {[int(b) for b in prof]}",
              flush=True)
    print("=== cross-check vs full orientation encoding (corner_sat) ===",
          flush=True)
    show10 = C.show_table(C.census(2)[10])
    for (W, H), L in [((3, 3), 3), ((3, 3), 4), ((4, 3), 3), ((4, 3), 4),
                      ((4, 4), 2), ((4, 4), 3)]:
        tb = cyls[(W, H)].box_sat(L)
        ok_c, _ = C.corner_sat(show10, (W, H, L), "equal", False, 2_000_000)
        match = "MATCH" if tb == bool(ok_c) else "**MISMATCH**"
        print(f"  box ({W},{H},{L}): transfer {tb} vs corner_sat {ok_c}"
              f"  {match}", flush=True)

    print("=== z-periodic cylinders (torus in z only) ===", flush=True)
    for (W, H), L in [((2, 2), 2), ((2, 2), 4), ((3, 3), 2), ((3, 3), 4),
                      ((4, 4), 2), ((4, 4), 4)]:
        print(f"  {W}x{H} x L={L}: {cyls[(W, H)].torus_sat(L)}", flush=True)

    print("=== 4x4 reachable-set detail ===", flush=True)
    hist = cyls[(4, 4)].reachable(6)
    for k, S in enumerate(hist, start=1):
        print(f"S_{k} ({len(S)} states):")
        for r in show_bits(S, 4, 4):
            print(f"   {r}")


if __name__ == "__main__":
    main()
