#!/usr/bin/env python3
"""Exact checker for a unimodular-cover certificate.

Usage: check_cover.py B.json CERT.txt

Replays the preorder tree of CERT.txt over open
polyhedra {x : a.x < b}, starting from int P, P = B[0,1]^d. At "s i" the piece R
is split by the unimodular simplex S_i (i-th in lexicographic order of the sorted
vertex tuples, recomputed here from B) into the d+1 pieces
R & {f_0 > 0, ..., f_{j-1} > 0, f_j < 0}; together with S_i and finitely many
hyperplanes they cover R. At "y k1 ..." the piece must be empty: an exact solution
y of sum_k y_k a_k = 0, sum_k y_k = 1 on the listed constraints is computed, and
y >= 0 and sum_k y_k b_k <= 0 are required (then no x satisfies all a_k.x < b_k).
If the replay ends with every piece certified empty, int P minus the union U of
the subtracted simplices has empty interior, so U (closed) contains P: the
unimodular simplices of P cover P. Exit 0 and print PASS, or exit 1.

CERT.txt: a JSON line {"B": B}, then the search tree in preorder, one node a line:
"s i" (subtract simplex i of the lexicographically sorted list of unimodular
simplices; its d+1 child pieces follow) or "y k1 k2 ..." (an empty piece: the
indices, in the piece's constraint list, of the support of a Farkas certificate).
The constraint list of int P is t_1 > 0, t_1 < 1, t_2 > 0, ... ; child j of a
piece appends f_0 > 0, ..., f_{j-1} > 0, f_j < 0 (facets of the simplex in vertex
order, f_j the facet opposite vertex j, f_j >= 0 inside it).
"""
import sys, json, itertools
from fractions import Fraction as Fr


def fail(m):
    print('FAIL:', m)
    sys.exit(1)


def det(M):
    n = len(M)
    if n == 0:
        return 1
    return sum((-1) ** j * M[0][j] * det([r[:j] + r[j + 1:] for r in M[1:]]) for j in range(n) if M[0][j])


def solve(A, b):
    m, n = len(A), len(A[0])
    M = [[Fr(v) for v in A[i]] + [Fr(b[i])] for i in range(m)]
    piv, r = [], 0
    for c in range(n):
        p = next((i for i in range(r, m) if M[i][c] != 0), None)
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        M[r] = [v / M[r][c] for v in M[r]]
        for i in range(m):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [x - f * y for x, y in zip(M[i], M[r])]
        piv.append(c)
        r += 1
    if any(M[i][n] != 0 for i in range(r, m)):
        return None
    y = [Fr(0)] * n
    for i, c in enumerate(piv):
        y[c] = M[i][n]
    return y


def main():
    lines = open(sys.argv[2]).read().split('\n')
    B = json.load(open(sys.argv[1]))['B']
    if json.loads(lines[0])['B'] != B:
        fail('certificate is for another parallelepiped')
    d = len(B)
    D = det(B)
    if D == 0:
        fail('singular B')
    # Cramer: t_k(x) = det(B with column k replaced by x) / D = (g_k . x) / D
    g = [[det([[int(i == r) if j == k else B[i][j] for j in range(d)] for i in range(d)]) for r in range(d)]
         for k in range(d)]
    sg = 1 if D > 0 else -1
    root = []
    for k in range(d):
        a = [sg * v for v in g[k]]
        root.append(([-v for v in a], 0))
        root.append((a, abs(D)))
    lo = [sum(min(0, B[i][j]) for j in range(d)) for i in range(d)]
    hi = [sum(max(0, B[i][j]) for j in range(d)) for i in range(d)]
    pts = [x for x in itertools.product(*[range(lo[i], hi[i] + 1) for i in range(d)])
           if all(0 <= sum(a[i] * x[i] for i in range(d)) * -1 for a, _ in root[0::2])
           and all(sum(a[i] * x[i] for i in range(d)) <= b for a, b in root[1::2])]
    simp = sorted(tuple(sorted(c)) for c in itertools.combinations(pts, d + 1)
                  if abs(det([[c[k][i] - c[0][i] for i in range(d)] for k in range(1, d + 1)])) == 1)

    def facets(s):
        out = []
        for j in range(d + 1):
            F = [s[k] for k in range(d + 1) if k != j]
            # h(x) = det(F_1-F_0, ..., F_{d-1}-F_0, x-F_0) is affine in x and vanishes on aff(F)
            E = [[F[r][i] - F[0][i] for i in range(d)] for r in range(1, d)]
            n = [det(E + [[int(i == c) for i in range(d)]]) for c in range(d)]
            c0 = sum(n[i] * F[0][i] for i in range(d))
            if sum(n[i] * s[j][i] for i in range(d)) < c0:
                n, c0 = [-v for v in n], -c0
            out.append((n, c0))  # n.x >= c0 on the simplex
        return out

    pos = [1]
    used = set()
    leaves = 0

    def node(C):
        nonlocal leaves
        if pos[0] >= len(lines) or not lines[pos[0]]:
            fail('certificate ends early')
        tok = lines[pos[0]].split()
        pos[0] += 1
        if tok[0] == 'y':
            S = [int(k) for k in tok[1:]]
            if not S or len(set(S)) != len(S) or any(not 0 <= k < len(C) for k in S):
                fail('bad leaf at line %d' % pos[0])
            A = [[C[k][0][i] for k in S] for i in range(d)] + [[1] * len(S)]
            y = solve(A, [0] * d + [1])
            if y is None or any(v < 0 for v in y) or sum(v * C[k][1] for v, k in zip(y, S)) > 0:
                fail('leaf at line %d is not certified empty' % pos[0])
            leaves += 1
            return
        if tok[0] != 's':
            fail('bad token')
        i = int(tok[1])
        if not 0 <= i < len(simp):
            fail('bad simplex index')
        used.add(i)
        prev = []
        for n, c0 in facets(simp[i]):
            node(C + prev + [(n, c0)])
            prev.append(([-v for v in n], -c0))

    sys.setrecursionlimit(100000)
    node(root)
    if any(l.strip() for l in lines[pos[0]:]):
        fail('trailing lines')
    print('PASS: %d unimodular simplices of P (d=%d det=%d, %d lattice points) cover P; %d empty pieces certified'
          % (len(used), d, abs(D), len(pts), leaves))


if __name__ == '__main__':
    main()
