#!/usr/bin/env python3
"""Check the vertex fans of Proposition 1.5 (checker A).

Usage: check_fans.py B.json FANS.jsonl COMPAT
  FANS.jsonl: one line per vertex v of P = P(B), {"vertex": v, "cones": [[p1, p2, p3, p4], ...]},
  a cone being spanned by p1 - v, ..., p4 - v.
  COMPAT: the binary of compat.cpp (pairwise proper intersection of 4-simplices by circuits).

Checks, with exact integer and rational arithmetic and without the search's code:
  1. the lattice points of P, recomputed from B; the lines are the 16 vertices of P, once each;
  2. every cone has its four points among the lattice points of P other than v, with
     |det(p1 - v, ..., p4 - v)| = 1, and the cones at v are distinct;
  3. the cones at v pairwise intersect properly: the simplices conv(0, p1 - v, ..., p4 - v) do,
     which COMPAT decides (two cones meet in a common face exactly when these simplices do);
  4. they cover the vertex cone C_v = cone(g_1, ..., g_4), g_j = +-b_j the edge vectors of P at v:
     with h(x) the sum of the coordinates of x in the basis g, the cones cut the section
     {h = 1} of C_v in simplices of 3-volume proportional to 1/(h(p1-v)...h(p4-v)), and the
     section itself has 3-volume proportional to |det B|, with the same constant. Equal sums mean
     that the closed simplices, with disjoint interiors by 3, fill the section, so the cones fill C_v;
  5. at v = 0: the fan has 56 cones and its rays are all 19 nonzero lattice points of P; the
     Hilbert basis of C_0 has 8 elements and 11 of the rays are reducible (an element of the
     Hilbert basis lies in P, and x in P is reducible exactly when x - y lies in C_0 for a lattice
     point y of P other than 0 and x).
Exit 0 and print PASS lines, or exit 1.
"""
import sys, json, itertools, subprocess
from fractions import Fraction


def fail(m):
    print('FAIL:', m)
    sys.exit(1)


def det(M):
    n = len(M)
    if n == 1:
        return M[0][0]
    return sum((-1) ** j * M[0][j] * det([r[:j] + r[j + 1:] for r in M[1:]]) for j in range(n) if M[0][j])


def coords(G, x):
    """Coordinates of x in the basis given by the columns of G (Cramer's rule)."""
    n, D = len(G), det(G)
    return [Fraction(det([[x[i] if j == k else G[i][j] for j in range(n)] for i in range(n)]), D)
            for k in range(n)]


def main():
    if len(sys.argv) != 4:
        fail(__doc__)
    B = json.load(open(sys.argv[1]))['B']
    fans = [json.loads(l) for l in open(sys.argv[2]) if l.strip()]
    compat = sys.argv[3]
    n = 4
    DB = abs(det(B))
    cols = [[B[i][j] for i in range(n)] for j in range(n)]
    corners = [[sum(c[i] for c, s in zip(cols, S) if s) for i in range(n)] for S in itertools.product((0, 1), repeat=n)]
    lo = [min(c[i] for c in corners) for i in range(n)]
    hi = [max(c[i] for c in corners) for i in range(n)]
    lattice = [x for x in itertools.product(*[range(lo[i], hi[i] + 1) for i in range(n)])
               if all(0 <= t <= 1 for t in coords(B, x))]
    inP = set(lattice)
    if sorted(tuple(f['vertex']) for f in fans) != sorted(map(tuple, corners)):
        fail('the lines are not the 16 vertices of P, once each')
    total = 0
    for f in fans:
        v = tuple(f['vertex'])
        S = next(S for S in itertools.product((0, 1), repeat=n) if corners[int(''.join(map(str, S)), 2)] == list(v))
        G = [[B[i][j] * (-1 if S[j] else 1) for j in range(n)] for i in range(n)]
        h = lambda x: sum(coords(G, x))
        cones = []
        for c in f['cones']:
            c = [tuple(p) for p in c]
            if len(c) != n or any(p not in inP or p == v for p in c):
                fail(f'vertex {v}: a cone ray is not a lattice point of P other than v')
            R = [tuple(a - b for a, b in zip(p, v)) for p in c]
            if abs(det([list(r) for r in R])) != 1:
                fail(f'vertex {v}: cone {c} is not unimodular')
            cones.append(R)
        if not cones or len({frozenset(R) for R in cones}) != len(cones):
            fail(f'vertex {v}: no cones, or a repeated cone')
        pts = sorted({(0,) * n} | {r for R in cones for r in R})
        idx = {p: i for i, p in enumerate(pts)}
        inp = '%d\n' % len(pts) + ''.join(' '.join(map(str, p)) + '\n' for p in pts)
        inp += '%d\n' % len(cones) + ''.join('%d ' % idx[(0,) * n] + ' '.join(str(idx[r]) for r in R) + '\n' for R in cones)
        r = subprocess.run([compat], input=inp, capture_output=True, text=True)
        if r.returncode != 0 or r.stdout.strip():
            fail(f'vertex {v}: two cones intersect improperly')
        vol = sum(Fraction(1, 1) / (h(R[0]) * h(R[1]) * h(R[2]) * h(R[3])) for R in cones)
        if vol != DB:
            fail(f'vertex {v}: the section volumes add up to {vol}, not {DB}')
        total += len(cones)
        if v == (0,) * n:
            rays = {r for R in cones for r in R}
            nonzero = [x for x in lattice if any(x)]
            if len(cones) != 56 or rays != set(nonzero) or len(rays) != 19:
                fail('vertex 0: expected 56 cones with all 19 nonzero lattice points of P as rays')
            red = {x for x in nonzero
                   if any(y != x and all(t >= 0 for t in coords(B, [a - b for a, b in zip(x, y)])) for y in nonzero)}
            hb = [x for x in nonzero if x not in red]
            if len(hb) != 8 or len(rays & red) != 11:
                fail(f'vertex 0: Hilbert basis of {len(hb)} elements, {len(rays & red)} reducible rays')
            print('PASS: vertex 0: 56 unimodular cones fill the vertex cone; rays: the 19 nonzero lattice '
                  'points of P, 11 of them outside the Hilbert basis (8 elements: %s)' % hb)
    print(f'PASS: {len(fans)} vertices of P, {total} unimodular cones: at each vertex the cones '
          'pairwise intersect properly and fill the vertex cone')


if __name__ == '__main__':
    main()
