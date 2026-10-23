"""cover_check: separately written check that the unit list covers every solution.

Usage: python3 -I cover_check.py n m datadir units.tsv
Independently of units.py it (1) derives each class's rowsum and compressed vector
from the first row mask in rows.bin (not from classes.tsv), (2) enumerates, with a
dictionary join, every class tuple with sorted rowsum magnitudes, sorted classes
within equal rowsums, and compressed PAF sums (4n, 0, ..., 0), (3) acts with every
unit multiplier on actual row masks, recompresses, and checks that the least image
of every such tuple is a listed unit, and that every listed unit is such a tuple
and is least in its orbit. Exit 0 iff the cover holds."""
import os, sys
from math import gcd
import numpy as np


def main():
    n, m = int(sys.argv[1]), int(sys.argv[2])
    H, L = (n - 1) // 2, n // m
    rows = np.fromfile(os.path.join(sys.argv[3], "rows.bin"), dtype="<u4")
    offs = [(int(l.split("\t")[5]), int(l.split("\t")[4])) for l in open(os.path.join(sys.argv[3], "classes.tsv"))]

    def full_row(mask):
        x = [1] * n
        for i in range(1, H + 1):
            if (mask >> (i - 1)) & 1:
                x[i] = x[n - i] = -1
        return x

    def comp(x):
        return tuple(sum(x[j + L * t] for t in range(m)) for j in range(L))

    def mult_row(x, u):
        return [x[(u * i) % n] for i in range(n)]

    first = [int(rows[o]) for o, c in offs]
    cvec = [comp(full_row(mk)) for mk in first]
    rsum = [sum(full_row(mk)) for mk in first]
    by_vec = {}
    for i, v in enumerate(cvec):
        by_vec.setdefault(v, []).append(i)
    assert all(len(v) == 1 for v in by_vec.values()), "two classes with one compressed vector"
    cid = {v: ids[0] for v, ids in by_vec.items()}
    units_in = [tuple(int(v) for v in l.split()[1:5]) for l in open(sys.argv[4])]

    def cpaf(v, s):
        return sum(v[j] * v[(j + s) % L] for j in range(L))
    paf = [tuple(cpaf(v, s) for s in range(L)) for v in cvec]
    # multiplier images of each class, through the row masks
    us = [u for u in range(1, n) if gcd(u, n) == 1]
    img = {u: [cid[comp(mult_row(full_row(mk), u))] for mk in first] for u in us}
    mags = sorted({abs(r) for r in rsum})
    groups = {}
    for i, r in enumerate(rsum):
        groups.setdefault(r, []).append(i)
    sols = set()
    target = tuple([4 * n] + [0] * (L - 1))
    rs_sorted = sorted(groups, key=abs)
    for r1 in rs_sorted:
        for r2 in rs_sorted:
            for r3 in rs_sorted:
                for r4 in rs_sorted:
                    if not (abs(r1) <= abs(r2) <= abs(r3) <= abs(r4)) or r1 * r1 + r2 * r2 + r3 * r3 + r4 * r4 != 4 * n:
                        continue
                    right = {}
                    for c3 in groups[r3]:
                        for c4 in groups[r4]:
                            if r3 == r4 and c3 > c4:
                                continue
                            key = tuple(target[s] - paf[c3][s] - paf[c4][s] for s in range(L))
                            right.setdefault(key, []).append((c3, c4))
                    for c1 in groups[r1]:
                        for c2 in groups[r2]:
                            if r1 == r2 and c1 > c2:
                                continue
                            key = tuple(paf[c1][s] + paf[c2][s] for s in range(L))
                            for c3, c4 in right.get(key, ()):
                                t = (c1, c2, c3, c4)
                                rr = (r1, r2, r3, r4)
                                if (r2 == r3 and c2 > c3) or (r1 == r3 and c1 > c3) or (r2 == r4 and c2 > c4) or (r1 == r4 and c1 > c4):
                                    continue
                                sols.add(t)

    def canon(t):
        best = None
        for u in us:
            im = [img[u][c] for c in t]
            r = [rsum[c] for c in im]
            # sort positions by (|rowsum|, class id): rowsums are preserved by u
            im = [c for _, c in sorted(zip([(abs(x), 0) for x in r], im))]
            if best is None or tuple(im) < best:
                best = tuple(im)
        return best
    U = set(units_in)
    if len(U) != len(units_in):
        print("FAIL: duplicate units"); sys.exit(1)
    missing = [t for t in sols if canon(t) not in U]
    stray = [t for t in units_in if t not in sols or canon(t) != t]
    orbit_ok = len(set(canon(t) for t in sols)) == len(U)
    print("cover_check n=%d m=%d classes=%d sorted_tuples=%d units=%d uncovered=%d invalid_or_noncanonical_units=%d %s" % (
        n, m, len(first), len(sols), len(U), len(missing), len(stray), "PASS" if not missing and not stray and orbit_ok else "FAIL"))
    sys.exit(0 if not missing and not stray and orbit_ok else 1)


if __name__ == "__main__":
    main()
