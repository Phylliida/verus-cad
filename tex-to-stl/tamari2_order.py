#!/usr/bin/env python3
"""The 2-Tamari lattice on 2-Dyck paths (n=4), with the true covering
relation, mapped to Bergeron's Figure-6 vertex labels.

Label decoding: a vertex label like '642' is the area vector read
high-to-low: a = (a1,a2,a3,a4) = (0,2,4,6) (a1=0 implicit, trailing zeros
trimmed).  Area vector from the path N E^{e1} N E^{e2} N E^{e3} N E^{e4}:
a_1 = 0, a_{i+1} = a_i + m - e_i.

Cover (rotation): pick a valley (E immediately followed by N); let S be the
shortest subpath starting at that N with m*(#N) - (#E) = 0 (the primitive
m-excursion); move the E after S.  This goes UP: min = (NE^m)^n = label 0,
max = N^n E^{mn} = label 642.
"""
from itertools import product

M = 2
N = 4


def all_paths():
    """2-Dyck paths as step strings over {'N','E'}, ballot condition."""
    out = []

    def rec(path, n_used, e_used):
        if n_used == N and e_used == M * N:
            out.append("".join(path))
            return
        if n_used < N:
            path.append('N')
            rec(path, n_used + 1, e_used)
            path.pop()
        if e_used < M * n_used and e_used < M * N:
            path.append('E')
            rec(path, n_used, e_used + 1)
            path.pop()

    rec([], 0, 0)
    return out


def f_vector(path):
    """f_i = number of E steps before the i-th N step (i = 1..N)."""
    f = []
    e = 0
    for s in path:
        if s == 'N':
            f.append(e)
        else:
            e += 1
    return tuple(f)


def label_of(path):
    f = f_vector(path)
    digits = [str(x) for x in (f[3], f[2], f[1])]  # f1 = 0 implicit
    s = "".join(digits).rstrip("0")
    return s if s else "0"


def covers(path):
    """All paths covering `path` (one rotation up)."""
    out = []
    steps = list(path)
    L = len(steps)
    for i in range(L - 1):
        if steps[i] == 'E' and steps[i + 1] == 'N':
            # primitive m-excursion S starting at i+1
            bal = 0
            j = i + 1
            while j < L:
                bal += M if steps[j] == 'N' else -1
                j += 1
                if bal == 0:
                    break
            assert bal == 0
            newp = steps[:i] + steps[i + 1:j] + ['E'] + steps[j:]
            out.append("".join(newp))
    return out


def hasse_edges():
    """All covering pairs as (lower_label, upper_label)."""
    paths = all_paths()
    assert len(paths) == 55, len(paths)
    labels = {p: label_of(p) for p in paths}
    assert len(set(labels.values())) == 55
    E = set()
    for p in paths:
        for q in covers(p):
            E.add((labels[p], labels[q]))
    return E


if __name__ == "__main__":
    E = hasse_edges()
    print(f"55 paths, {len(E)} covering relations")
    lows = {a for a, b in E}
    ups = {b for a, b in E}
    bottom = set(l for l in (set(lows) | set(ups))) - ups
    top = (lows | ups) - lows
    print("bottom:", bottom, " top:", top)
