#!/usr/bin/env python3
"""Check a pruning certificate (shares no code with prune.py).

Usage: check_prune.py B.json CERT.json

Recomputes from B alone, exactly, the lattice points of P = B[0,1]^d and every
unimodular lattice simplex in P. Accepts iff the certificate deletes each of them
exactly once and, for every deletion [s, q], the facet F = s - {q} is not contained
in a facet of P and every unimodular simplex in P with facet F and apex strictly on
the other side of aff(F) from q was deleted earlier.

Why this proves that P has no unimodular triangulation T: if T existed, let s be
the first simplex of T in the list. Its facet F is not in the boundary of P, so
relint F lies in the interior of P and T has a simplex t with facet F on the other
side of aff(F); t is unimodular, lies in P, and was deleted before s, contradicting
the choice of s. Since T is nonempty and every simplex is deleted, no T exists.
Exit 0 and print PASS, or exit 1.
"""
import sys, json, itertools
from fractions import Fraction as Fr


def fail(msg):
    print('FAIL:', msg)
    sys.exit(1)


def det(M):
    M = [[Fr(x) for x in r] for r in M]
    n, s = len(M), Fr(1)
    for c in range(n):
        p = next((r for r in range(c, n) if M[r][c] != 0), None)
        if p is None:
            return Fr(0)
        if p != c:
            M[c], M[p] = M[p], M[c]
            s = -s
        s *= M[c][c]
        for r in range(c + 1, n):
            f = M[r][c] / M[c][c]
            for k in range(c, n):
                M[r][k] -= f * M[c][k]
    return s


def main():
    B = json.load(open(sys.argv[1]))['B']
    cert = json.load(open(sys.argv[2]))
    if cert['B'] != B:
        fail('certificate is for another parallelepiped')
    d = len(B)
    D = det([[B[i][j] for j in range(d)] for i in range(d)])
    if D == 0:
        fail('singular B')
    # t = B^{-1} x through the adjugate: t_j = det(B with column j replaced by x) / det(B)
    def t(x):
        return tuple(det([[x[i] if j == k else B[i][j] for j in range(d)] for i in range(d)]) / D
                     for k in range(d))
    lo = [sum(min(0, B[i][j]) for j in range(d)) for i in range(d)]
    hi = [sum(max(0, B[i][j]) for j in range(d)) for i in range(d)]
    T = {}
    for x in itertools.product(*[range(lo[i], hi[i] + 1) for i in range(d)]):
        c = t(x)
        if all(0 <= v <= 1 for v in c):
            T[x] = c
    uni = set()
    for c in itertools.combinations(sorted(T), d + 1):
        if abs(det([[c[k][i] - c[0][i] for i in range(d)] for k in range(1, d + 1)])) == 1:
            uni.add(frozenset(c))
    dels = [(frozenset(tuple(p) for p in s), tuple(q)) for s, q in cert['deletions']]
    if len(dels) != len(uni) or {s for s, q in dels} != uni:
        fail('deletions are not exactly the %d unimodular simplices of P' % len(uni))

    def orient(F, q):
        F = sorted(F)
        v = det([[f[i] - F[0][i] for i in range(d)] for f in F[1:]] + [[q[i] - F[0][i] for i in range(d)]])
        return (v > 0) - (v < 0)

    other = {}  # facet -> {orientation: simplices}
    for s in uni:
        for q in s:
            other.setdefault(s - {q}, {1: [], -1: []})[orient(s - {q}, q)].append(s)
    gone = set()
    for k, (s, q) in enumerate(dels):
        if q not in s:
            fail('deletion %d: apex is not a vertex' % k)
        F = s - {q}
        if any(all(T[p][i] == 0 for p in F) or all(T[p][i] == 1 for p in F) for i in range(d)):
            fail('deletion %d: witness facet lies in a facet of P' % k)
        if any(u not in gone for u in other[F][-orient(F, q)]):
            fail('deletion %d: a partner across the witness facet is still present' % k)
        gone.add(s)
    print('PASS: pruning deletes all %d unimodular simplices of P (d=%d det=%s, %d lattice points)'
          % (len(uni), d, abs(D), len(T)))


if __name__ == '__main__':
    main()
