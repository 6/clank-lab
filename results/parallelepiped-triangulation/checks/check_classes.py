#!/usr/bin/env python3
"""Check a classification file data/classes/n4_D<D>.jsonl.

Usage: check_classes.py FILE.jsonl COMPAT
  COMPAT: the binary of compat.cpp (pairwise proper intersection of
  4-simplices by the circuit criterion).

Checks, with exact integer arithmetic:
  1. completeness: every 4x4 integer matrix in row-operation Hermite normal form
     with determinant D (every lattice parallelepiped of determinant D is
     unimodularly equivalent to the one such matrix's columns span) becomes, after
     some permutation and sign change of its columns, row-equivalent to the matrix
     B of some line (equal Hermite normal forms);
  2. each TRIANGULATION line lists 24*D simplices whose vertices are lattice points
     of P(B) = B[0,1]^4, each with |det| = 1, pairwise intersecting properly (no
     improper pair reported by COMPAT): interiors are then disjoint, so the union
     has volume vol(P) and, being closed and inside P, equals P;
  3. lists the UNSAT lines, to be checked by check_prune.py.
Exit 0 and print PASS, or exit 1.
"""
import sys, json, itertools, subprocess


def fail(m):
    print('FAIL:', m)
    sys.exit(1)


def det(M):
    n = len(M)
    if n == 1:
        return M[0][0]
    return sum((-1) ** j * M[0][j] * det([r[:j] + r[j + 1:] for r in M[1:]]) for j in range(n) if M[0][j])


def hnf(B):
    A = [r[:] for r in B]
    n = len(A)
    for j in range(n):
        while any(A[r][j] for r in range(j + 1, n)):
            p = min((r for r in range(j, n) if A[r][j]), key=lambda r: abs(A[r][j]))
            A[j], A[p] = A[p], A[j]
            for r in range(j + 1, n):
                q = A[r][j] // A[j][j]
                A[r] = [a - q * b for a, b in zip(A[r], A[j])]
        if A[j][j] < 0:
            A[j] = [-a for a in A[j]]
        for r in range(j):
            q = A[r][j] // A[j][j]
            A[r] = [a - q * b for a, b in zip(A[r], A[j])]
    return tuple(map(tuple, A))


def orbit(B):
    n = len(B)
    return {hnf([[B[i][p[j]] * s[j] for j in range(n)] for i in range(n)])
            for p in itertools.permutations(range(n)) for s in itertools.product((1, -1), repeat=n)}


def main():
    lines = [json.loads(l) for l in open(sys.argv[1])]
    compat = sys.argv[2]
    D = lines[0]['det']
    n = 4
    reps = {}
    for L in lines:
        B = L['B']
        if L['det'] != D or abs(det(B)) != D:
            fail('wrong determinant')
        for H in orbit(B):
            if H in reps:
                fail('two lines are equivalent')
            reps[H] = L
    # 1. completeness over all HNFs of determinant D
    cnt = 0
    for h in itertools.product(range(1, D + 1), repeat=n):
        if h[0] * h[1] * h[2] * h[3] != D:
            continue
        cells = [(i, j) for j in range(n) for i in range(j)]
        for vals in itertools.product(*[range(h[j]) for i, j in cells]):
            B = [[h[i] if i == j else 0 for j in range(n)] for i in range(n)]
            for (i, j), v in zip(cells, vals):
                B[i][j] = v
            cnt += 1
            if hnf(B) not in reps:
                fail('HNF %s is in no class' % B)
    # 2. triangulations
    nt = nu = 0
    for L in lines:
        B = L['B']
        if L['status'] == 'UNSAT':
            nu += 1
            print('UNSAT class (check with check_prune.py):', json.dumps(B))
            continue
        if L['status'] != 'TRIANGULATION':
            fail('unknown status')
        S = [[tuple(p) for p in s] for s in L['triangulation']]
        if len(S) != 24 * D or len({frozenset(s) for s in S}) != len(S):
            fail('wrong number of simplices for %s' % B)
        pts = sorted({p for s in S for p in s})
        for p in pts:  # t = B^{-1} p in [0,1]^4 via Cramer's rule
            for k in range(n):
                num = det([[p[i] if j == k else B[i][j] for j in range(n)] for i in range(n)])
                if not (0 <= num * D <= D * D if det(B) > 0 else 0 >= num * D >= -D * D):
                    fail('vertex %s outside P(%s)' % (p, B))
        for s in S:
            if abs(det([[s[k][i] - s[0][i] for i in range(n)] for k in range(1, n + 1)])) != 1:
                fail('non-unimodular simplex')
        idx = {p: i for i, p in enumerate(pts)}
        inp = '%d\n' % len(pts) + ''.join(' '.join(map(str, p)) + '\n' for p in pts)
        inp += '%d\n' % len(S) + ''.join(' '.join(str(idx[p]) for p in s) + '\n' for s in S)
        r = subprocess.run([compat], input=inp, capture_output=True, text=True)
        if r.returncode != 0 or r.stdout.strip():
            fail('improper pair in the triangulation of %s' % B)
        nt += 1
    print('PASS: det %d: %d HNFs in %d classes; %d triangulations verified; %d UNSAT classes'
          % (D, cnt, len(lines), nt, nu))


if __name__ == '__main__':
    main()
