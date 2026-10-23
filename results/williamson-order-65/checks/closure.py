"""closure: compare solution sets up to the Williamson symmetries.

Usage: python3 -I closure.py n reference.txt found.txt   |   closure.py n --emit found.txt
reference.txt: every ordered normalized solution (4 masks per line), from baseline.
found.txt: solutions from the reduced search (4 masks per line, or SOLUTION lines).
Checks that closure(found) under row permutations and unit multipliers equals the
reference set exactly, and prints the number of equivalence classes.
Equivalence (odd n): permuting the four rows, negating rows (removed by
normalization) and a common multiplier x_i -> x_{ui}, gcd(u,n)=1."""
import sys
from itertools import permutations
from math import gcd


def read(path):
    out = set()
    for line in open(path):
        f = line.split()
        if not f:
            continue
        if f[0] == "SOLUTION":
            f = f[2:]
        out.add(tuple(int(v) for v in f[:4]))
    return out


def main():
    n = int(sys.argv[1]); H = (n - 1) // 2
    perms = []  # bit permutation for each multiplier u (u and n-u act the same on symmetric rows)
    for u in range(1, n):
        if gcd(u, n) != 1:
            continue
        src = []
        for i in range(1, H + 1):
            p = (u * i) % n
            src.append(min(p, n - p) - 1)
        perms.append(src)

    def mult(mask, src):
        return sum(((mask >> s) & 1) << i for i, s in enumerate(src))

    def orbit(t):
        out = set()
        for src in perms:
            im = tuple(mult(m, src) for m in t)
            for p in permutations(im):
                out.add(p)
        return out

    if len(sys.argv) == 4 and sys.argv[2] == "--emit":  # print the closure of a found set (a reference for larger n)
        clo = set()
        for t in read(sys.argv[3]):
            clo |= orbit(t)
        for t in sorted(clo):
            print("%d\t%d\t%d\t%d" % t)
        return
    ref = read(sys.argv[2]); found = read(sys.argv[3])
    clo = set()
    for t in found:
        clo |= orbit(t)
    classes = set(min(orbit(t)) for t in ref)
    # every found tuple must itself be a solution present in the reference
    print("n=%d reference=%d found=%d closure=%d classes=%d found_subset=%s closure_equal=%s" % (
        n, len(ref), len(found), len(clo), len(classes), found <= ref, clo == ref))
    sys.exit(0 if (found <= ref and clo == ref) else 1)


if __name__ == "__main__":
    main()
