#!/usr/bin/env python3
"""Facet-partner pruning for unimodular triangulations of a lattice parallelepiped.

Usage: prune.py B.json OUT.json

Start from all unimodular lattice simplices in P = B[0,1]^d (B: generators as
columns). Repeatedly delete a simplex s having a facet F, not contained in a facet
of P, such that no remaining simplex has F as a facet with its apex on the other
side of aff(F). No simplex of a unimodular triangulation T is ever deleted (its
partner across F is in T), so if every simplex is deleted, P has no unimodular
triangulation. OUT.json lists the deletions in order as [simplex, apex]: the
simplex's vertex coordinates and the vertex opposite the witness facet F.
"""
import sys, json, itertools
from fractions import Fraction as Fr


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


def coords(B, x):
    d = len(B)
    A = [[Fr(B[i][j]) for j in range(d)] + [Fr(x[i])] for i in range(d)]
    for i in range(d):
        p = next(r for r in range(i, d) if A[r][i] != 0)
        A[i], A[p] = A[p], A[i]
        A[i] = [v / A[i][i] for v in A[i]]
        for r in range(d):
            if r != i and A[r][i] != 0:
                f = A[r][i]
                A[r] = [a - f * b for a, b in zip(A[r], A[i])]
    return tuple(A[i][d] for i in range(d))


def main():
    B = json.load(open(sys.argv[1]))['B']
    d = len(B)
    corners = [[sum(B[i][j] * e[j] for j in range(d)) for i in range(d)]
               for e in itertools.product((0, 1), repeat=d)]
    box = [range(min(c[i] for c in corners), max(c[i] for c in corners) + 1) for i in range(d)]
    T = {}
    for x in itertools.product(*box):
        t = coords(B, x)
        if all(0 <= v <= 1 for v in t):
            T[x] = t
    pts = sorted(T)
    simp = [c for c in itertools.combinations(pts, d + 1)
            if abs(det([[c[k][i] - c[0][i] for i in range(d)] for k in range(1, d + 1)])) == 1]

    def side(F, q):
        v = det([[f[i] - F[0][i] for i in range(d)] for f in F[1:]] + [[q[i] - F[0][i] for i in range(d)]])
        return 1 if v > 0 else -1

    def interior(F):
        return not any(all(T[p][i] == 0 for p in F) or all(T[p][i] == 1 for p in F) for i in range(d))

    fac = {}
    for s in simp:
        for q in s:
            F = tuple(p for p in s if p != q)
            fac.setdefault(F, {1: set(), -1: set()})[side(F, q)].add(s)
    alive, order = set(simp), []
    while True:
        dead = []
        for s in sorted(alive):
            for q in s:
                F = tuple(p for p in s if p != q)
                if interior(F) and not (fac[F][-side(F, q)] & alive):
                    dead.append((s, q))
                    break
        if not dead:
            break
        for s, q in dead:
            alive.discard(s)
        order += dead
    json.dump({'B': B, 'deletions': [[list(map(list, s)), list(q)] for s, q in order]}, open(sys.argv[2], 'w'))
    print('lattice points %d unimodular simplices %d deleted %d remaining %d'
          % (len(pts), len(simp), len(order), len(alive)))


if __name__ == '__main__':
    main()
