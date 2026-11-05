#!/usr/bin/env python3
"""Second checker of the vertex fans of Proposition 1.5 (checker B), written separately from
check_fans.py and sharing no code with it or with the search (localfan.py).

Usage: fans_check.py B.json FANS.jsonl

Exact arithmetic throughout (integers and fractions.Fraction). For each vertex v of P = P(B):
  - the rays p - v of every cone are lattice points of P - v, found as the integer x with
    adj(B) x in [0, det B]^4 (or [det B, 0]^4), and every cone is unimodular;
  - proper intersection: two cones cone(R), cone(S) meet in cone(R & S) unless some x = S mu with
    mu >= 0 has coordinates lam = R^-1 x >= 0 that are positive somewhere outside R & S; that
    linear system is shown infeasible by Fourier-Motzkin elimination;
  - covering: every facet of a cone that does not lie in a facet of the vertex cone (where one
    coordinate in the edge basis vanishes on all its rays) is a facet of another cone lying on
    the other side of it. With proper intersection this makes the union of the cones the whole
    vertex cone: otherwise a generic segment from the interior of a cone to an uncovered interior
    point of the vertex cone leaves the union through the relative interior of a facet with no
    cone on its other side.
At v = 0 it also computes the Hilbert basis of the cone (the nonzero lattice points of P that are
not the sum of two nonzero lattice points of P) and checks the counts 56, 19, 8 and 11.
Exit 0 and print PASS lines, or exit 1.
"""
import sys, json
from fractions import Fraction
from itertools import product, combinations


def die(msg):
    print('FAIL:', msg)
    sys.exit(1)


def bareiss(A):
    A = [list(r) for r in A]
    m, sign, prev = len(A), 1, 1
    for k in range(m - 1):
        if A[k][k] == 0:
            sw = next((i for i in range(k + 1, m) if A[i][k]), None)
            if sw is None:
                return 0
            A[k], A[sw] = A[sw], A[k]
            sign = -sign
        for i in range(k + 1, m):
            for j in range(k + 1, m):
                A[i][j] = (A[i][j] * A[k][k] - A[i][k] * A[k][j]) // prev
        prev = A[k][k]
    return sign * A[m - 1][m - 1]


def adjugate(A):
    m = len(A)
    minor = lambda i, j: [[A[r][c] for c in range(m) if c != j] for r in range(m) if r != i]
    return [[(-1) ** (i + j) * bareiss(minor(j, i)) for j in range(m)] for i in range(m)]


def matvec(A, x):
    return [sum(a * b for a, b in zip(row, x)) for row in A]


def feasible(rows):
    """Fourier-Motzkin: is there mu in Q^k with a . mu >= b for every (a, b) in rows?"""
    rows = [([Fraction(c) for c in a], Fraction(b)) for a, b in rows]
    k = len(rows[0][0])
    for j in range(k):
        pos = [(a, b) for a, b in rows if a[j] > 0]
        neg = [(a, b) for a, b in rows if a[j] < 0]
        new = [(a, b) for a, b in rows if a[j] == 0]
        for (a1, b1), (a2, b2) in product(pos, neg):
            s, t = -a2[j], a1[j]
            new.append(([s * x + t * y for x, y in zip(a1, a2)], s * b1 + t * b2))
        seen, rows = set(), []
        for a, b in new:  # scale each row so that its largest |coefficient| is 1, and deduplicate
            mx = max((abs(x) for x in a), default=0)
            if mx:
                a, b = [x / mx for x in a], b / mx
            key = (tuple(a), b)
            if key not in seen:
                seen.add(key)
                rows.append((a, b))
    return all(b <= 0 for a, b in rows)  # all coefficients are now zero: 0 >= b


def improper(R, S):
    """Do cone(R) and cone(S) (R unimodular) meet outside cone(R & S)?"""
    out = [i for i, r in enumerate(R) if r not in S]
    if not out:
        return False
    adjR, dR = adjugate([[r[i] for r in R] for i in range(4)]), bareiss([[r[i] for r in R] for i in range(4)])
    M = [[Fraction(c, dR) for c in matvec(adjR, s)] for s in S]  # M[j] = R^-1 s_j
    lam = [[M[j][i] for j in range(4)] for i in range(4)]  # lam_i = sum_j M[j][i] mu_j
    rows = [([int(i == j) for i in range(4)], 0) for j in range(4)]
    rows += [(lam[i], 0) for i in range(4)]
    rows.append(([sum(lam[i][j] for i in out) for j in range(4)], 1))
    return feasible(rows)


def main():
    if len(sys.argv) != 3:
        die(__doc__)
    B = json.load(open(sys.argv[1]))['B']
    D = bareiss(B)
    adj = adjugate(B)
    inside = lambda x: all((0 <= c <= D) if D > 0 else (D <= c <= 0) for c in matvec(adj, x))
    vertices = {tuple(matvec(B, e)): e for e in product((0, 1), repeat=4)}
    box = [range(min(v[i] for v in vertices), max(v[i] for v in vertices) + 1) for i in range(4)]
    points = [x for x in product(*box) if inside(x)]
    fans = [json.loads(line) for line in open(sys.argv[2]) if line.strip()]
    if len(fans) != 16 or {tuple(f['vertex']) for f in fans} != set(vertices):
        die('the fans are not one for each of the 16 vertices')
    count = 0
    for f in fans:
        v = tuple(f['vertex'])
        e = vertices[v]
        gens = [[B[i][j] * (1 - 2 * e[j]) for i in range(4)] for j in range(4)]  # edge vectors at v
        adjG = adjugate([[g[i] for g in gens] for i in range(4)])
        pv = {tuple(a - b for a, b in zip(x, v)) for x in points} - {(0, 0, 0, 0)}
        cones = []
        for c in f['cones']:
            R = [tuple(a - b for a, b in zip(p, v)) for p in c]
            if len(R) != 4 or len(set(R)) != 4 or not set(R) <= pv:
                die(f'vertex {v}: rays of {c} are not 4 distinct lattice points of P - v')
            if bareiss([[r[i] for r in R] for i in range(4)]) not in (1, -1):
                die(f'vertex {v}: {c} is not unimodular')
            cones.append(R)
        if not cones or len({frozenset(R) for R in cones}) < len(cones):
            die(f'vertex {v}: empty fan or repeated cone')
        for R, S in combinations(cones, 2):
            if improper(R, S) or improper(S, R):
                die(f'vertex {v}: {R} and {S} intersect improperly')
        facets = {}
        for R in cones:
            for i in range(4):
                F = tuple(sorted(R[:i] + R[i + 1:]))
                side = bareiss([list(F[0]), list(F[1]), list(F[2]), list(R[i])]) > 0
                facets.setdefault(F, []).append(side)
        for F, sides in facets.items():
            onbd = any(all(matvec(adjG, r)[k] == 0 for r in F) for k in range(4))
            if not onbd and set(sides) != {True, False}:
                die(f'vertex {v}: interior facet {F} has a cone on one side only')
        count += len(cones)
        if v == (0, 0, 0, 0):
            nz = sorted(pv)
            sums = {tuple(a + b for a, b in zip(x, y)) for x in nz for y in nz}
            hilbert = [x for x in nz if x not in sums]
            used = {r for R in cones for r in R}
            reducible = [r for r in used if r in sums]
            if (len(cones), len(used), used == set(nz), len(hilbert), len(reducible)) != (56, 19, True, 8, 11):
                die(f'vertex 0: {len(cones)} cones, {len(used)} rays, Hilbert basis {len(hilbert)}, '
                    f'{len(reducible)} reducible rays')
            print(f'PASS: vertex 0: fan of 56 cones on all 19 nonzero lattice points of P; '
                  f'Hilbert basis of 8, 11 rays reducible')
    print(f'PASS: second fan checker: 16 vertices, {count} unimodular cones, proper and covering at each vertex')


if __name__ == '__main__':
    main()
