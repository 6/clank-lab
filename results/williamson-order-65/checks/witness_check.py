"""witness_check: exact check of claimed Williamson quadruples, independent of the search.

Usage: python3 -I witness_check.py n file
Each line holds four masks (optionally after 'SOLUTION <unit>'). For each it builds
the four symmetric circulant +-1 matrices of order n and checks A^2+B^2+C^2+D^2 = 4nI
with exact integer arithmetic. Exit 0 iff every line passes (an empty file passes)."""
import sys
import numpy as np


def row(n, mask):
    H = (n - 1) // 2
    x = np.ones(n, dtype=np.int64)
    for i in range(1, H + 1):
        if (mask >> (i - 1)) & 1:
            x[i] = x[n - i] = -1
    return x


def circ(x):
    n = len(x)
    return np.array([[x[(j - i) % n] for j in range(n)] for i in range(n)], dtype=np.int64)


def main():
    n = int(sys.argv[1]); bad = 0; cnt = 0
    for line in open(sys.argv[2]):
        f = line.split()
        if not f:
            continue
        if f[0] == "SOLUTION":
            f = f[2:]
        masks = [int(v) for v in f[:4]]
        cnt += 1
        if any(m < 0 or m >= 1 << ((n - 1) // 2) for m in masks):
            bad += 1; print("FAIL (mask range)", masks); continue
        M = [circ(row(n, m)) for m in masks]
        ok = all((A == A.T).all() for A in M) and all(set(np.unique(A)) <= {-1, 1} for A in M)
        S = sum(A @ A for A in M)
        ok = ok and (S == 4 * n * np.eye(n, dtype=np.int64)).all()
        if not ok:
            bad += 1; print("FAIL", masks)
    print("witness_check n=%d lines=%d failed=%d %s" % (n, cnt, bad, "PASS" if bad == 0 else "FAIL"))
    sys.exit(0 if bad == 0 else 1)


if __name__ == "__main__":
    main()
