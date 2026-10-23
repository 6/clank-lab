"""units: every sorted compressed quadruple satisfying the compressed PAF
equations, reduced to one representative per orbit of (Z_L)^*/{+-1}.

Usage: python3 -I units.py n m classes.tsv out.tsv [orbits|sorted|all]
Output rows: unit_id c1 c2 c3 c4 orbit_size (class ids from classes.tsv).
Written from the problem statement only; no code from the earlier search."""
import sys
from math import gcd
import numpy as np


def main():
    n, m = int(sys.argv[1]), int(sys.argv[2])
    mode = sys.argv[5] if len(sys.argv) > 5 else "orbits"  # orbits | sorted | all (controls)
    L, h = n // m, (n // m - 1) // 2
    cls = []  # (id, key, rowsum, X list full length L)
    for line in open(sys.argv[3]):
        f = line.split("\t")
        half = [int(v) for v in f[3].split(",")]
        full = [half[min(j, L - j)] for j in range(L)]
        cls.append((int(f[0]), int(f[1]), int(f[2]), full))
    assert [c[0] for c in cls] == list(range(len(cls)))
    X = np.array([c[3] for c in cls], dtype=np.int64)
    rsum = np.array([c[2] for c in cls], dtype=np.int64)
    assert np.all(X.sum(axis=1) == rsum)
    # compressed PAF, shifts 0..h
    paf = np.stack([(X * np.roll(X, -s, axis=1)).sum(axis=1) for s in range(h + 1)], axis=1)
    # multiplier action on classes: X'_j = X_{u j mod L}
    key_to_id = {tuple(c[3]): c[0] for c in cls}
    mults = sorted({min(u % L, (-u) % L) for u in range(1, L) if gcd(u, L) == 1})
    act = []
    for u in mults:
        img = np.empty(len(cls), dtype=np.int64)
        for c in cls:
            y = tuple(c[3][(u * j) % L] for j in range(L))
            img[c[0]] = key_to_id[y]  # KeyError would mean a missing image class
        act.append(img)
    # rowsum types: sorted magnitudes with sum of squares 4n; sign fixed by r == n mod 4
    def sgn(a):
        return a if (a - n) % 4 == 0 else -a
    types = []
    for a in range(1, n + 1, 2):
        for b in range(a, n + 1, 2):
            for c in range(b, n + 1, 2):
                for d in range(c, n + 1, 2):
                    if a * a + b * b + c * c + d * d == 4 * n:
                        types.append(tuple(sgn(v) for v in (a, b, c, d)))
    by_r = {}
    for c in cls:
        by_r.setdefault(c[2], []).append(c[0])
    base = 8 * n + 1
    def enc(v):  # injective integer code of a vector with entries in [-4n, 4n]
        out = np.zeros(v.shape[0], dtype=object if (h + 1) * np.log2(base) > 62 else np.int64)
        for s in range(v.shape[1]):
            out = out * base + (v[:, s] + 4 * n)
        return out
    target = np.zeros(h + 1, dtype=np.int64); target[0] = 4 * n
    units = []
    total_sorted = 0
    if mode == "all":  # every ordering of every rowsum type: no row-permutation reduction
        from itertools import permutations
        types = sorted({p for t in types for p in permutations(t)})
    for t in types:
        L1, L2, L3, L4 = (np.array(by_r.get(r, []), dtype=np.int64) for r in t)
        if min(len(L1), len(L2), len(L3), len(L4)) == 0:
            continue
        a1, a2 = np.repeat(L1, len(L2)), np.tile(L2, len(L1))
        a3, a4 = np.repeat(L3, len(L4)), np.tile(L4, len(L3))
        kl = enc(paf[a1] + paf[a2]); kr = enc(target - paf[a3] - paf[a4])
        ol, orr = np.argsort(kl, kind="stable"), np.argsort(kr, kind="stable")
        kl, kr = kl[ol], kr[orr]
        lo = np.searchsorted(kr, kl, side="left"); hi = np.searchsorted(kr, kl, side="right")
        groups = [g for g in range(4)]
        for i in np.nonzero(hi > lo)[0]:
            p = ol[i]
            for j in range(lo[i], hi[i]):
                q = orr[j]
                tup = (int(a1[p]), int(a2[p]), int(a3[q]), int(a4[q]))
                if mode != "all" and any(t[x] == t[y] and tup[x] > tup[y] for x in range(4) for y in range(x + 1, 4)):
                    continue  # keep only tuples sorted within equal-rowsum positions
                total_sorted += 1
                if mode != "orbits":
                    units.append((tup, 1))
                    continue
                images = set()
                for img in act:
                    im = [int(img[c]) for c in tup]
                    # re-sort within equal-rowsum positions (rowsums are preserved)
                    for x in range(4):
                        for y in range(x + 1, 4):
                            if t[x] == t[y] and im[x] > im[y]:
                                im[x], im[y] = im[y], im[x]
                    images.add(tuple(im))
                if tup == min(images):
                    units.append((tup, len(images)))
    with open(sys.argv[4], "w") as f:
        for i, (tup, osz) in enumerate(units):
            f.write("%d\t%d\t%d\t%d\t%d\t%d\n" % (i, *tup, osz))
    print("n=%d m=%d classes=%d sorted_tuples=%d units=%d orbit_sum=%d group=%d"
          % (n, m, len(cls), total_sorted, len(units), sum(o for _, o in units), len(mults)))


if __name__ == "__main__":
    main()
