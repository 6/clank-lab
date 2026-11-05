#!/usr/bin/env python3
"""Encode "the lattice parallelepiped P = B[0,1]^d has a unimodular triangulation"
as CNF, using only conditions every unimodular triangulation satisfies.

Usage: enc.py B.json out.cnf [--meta out.json] [--varmap out.json] [--points K] [--seed S]
(--points 0 omits the (G) clauses.)
B.json: {"B": [[...],...]} with the generators as COLUMNS of B (d x d integers).

Variables: one per unimodular lattice simplex S contained in P (vertices are
lattice points of P; normalized volume |det| = 1).

Clauses (all necessary for any unimodular triangulation T of P):
  (L) every lattice point of P is a vertex of some chosen simplex
      (a lattice point lies in a unimodular simplex only as a vertex);
  (A) for every (d-1)-simplex F and each side of its hyperplane, at most one
      chosen simplex has F as a facet with apex on that side (two would share
      interior points);
  (M) if F is not contained in the boundary of P, its relative interior lies
      in int P, so a chosen simplex with facet F forces a chosen simplex with
      facet F on the other side;
  (G) for K generic sample points g of int P (random rationals, rejected if on
      any hyperplane spanned by a facet of a candidate simplex): at least one
      and at most one chosen simplex contains g (cover; disjoint interiors).
"""
import sys, json, itertools, random
from fractions import Fraction


def det_int(M):
    # exact integer determinant via fraction-free Bareiss
    M = [list(map(int, r)) for r in M]
    n = len(M)
    sign, prev = 1, 1
    for k in range(n - 1):
        if M[k][k] == 0:
            for i in range(k + 1, n):
                if M[i][k] != 0:
                    M[k], M[i] = M[i], M[k]
                    sign = -sign
                    break
            else:
                return 0
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                M[i][j] = (M[i][j] * M[k][k] - M[i][k] * M[k][j]) // prev
        prev = M[k][k]
    return sign * M[n - 1][n - 1]


def solve_frac(M, rhs):
    n = len(M)
    A = [[Fraction(M[i][j]) for j in range(n)] + [Fraction(rhs[i])] for i in range(n)]
    for c in range(n):
        p = next((r for r in range(c, n) if A[r][c] != 0), None)
        if p is None:
            return None
        A[c], A[p] = A[p], A[c]
        for r in range(n):
            if r != c and A[r][c] != 0:
                f = A[r][c] / A[c][c]
                A[r] = [A[r][j] - f * A[c][j] for j in range(n + 1)]
    return [A[i][n] / A[i][i] for i in range(n)]


def adjugate(B):
    d = len(B)
    A = [[0] * d for _ in range(d)]
    for i in range(d):
        for j in range(d):
            minor = [[B[r][c] for c in range(d) if c != j] for r in range(d) if r != i]
            A[j][i] = (-1) ** (i + j) * det_int(minor) if d > 1 else 1
    return A


def lattice_points(B):
    d = len(B)
    D = det_int(B)
    A = adjugate(B)  # B^{-1} = A / D
    s = 1 if D > 0 else -1
    corners = [[sum(B[i][j] * e[j] for j in range(d)) for i in range(d)]
               for e in itertools.product([0, 1], repeat=d)]
    lo = [min(c[i] for c in corners) for i in range(d)]
    hi = [max(c[i] for c in corners) for i in range(d)]
    pts, ys = [], []
    for x in itertools.product(*[range(lo[i], hi[i] + 1) for i in range(d)]):
        y = [s * sum(A[i][j] * x[j] for j in range(d)) for i in range(d)]
        if all(0 <= v <= abs(D) for v in y):
            pts.append(list(x))
            ys.append(y)
    return pts, ys, abs(D)


def main():
    args = sys.argv[1:]
    bfile, out = args[0], args[1]
    meta_out = None
    K, seed = 64, 1
    if '--meta' in args:
        meta_out = args[args.index('--meta') + 1]
    if '--points' in args:
        K = int(args[args.index('--points') + 1])
    if '--seed' in args:
        seed = int(args[args.index('--seed') + 1])
    B = json.load(open(bfile))['B']
    d = len(B)
    pts, ys, D = lattice_points(B)
    n = len(pts)
    # unimodular simplices: (d+1)-subsets with |det| = 1 (exact integer arithmetic)
    simp = []
    for c in itertools.combinations(range(n), d + 1):
        M = [[pts[c[k]][i] - pts[c[0]][i] for i in range(d)] for k in range(1, d + 1)]
        if abs(det_int(M)) == 1:
            simp.append(c)
    N = len(simp)
    var = {s: i + 1 for i, s in enumerate(simp)}
    clauses = []
    # (L) lattice point coverage
    inc = [[] for _ in range(n)]
    for s in simp:
        for v in s:
            inc[v].append(var[s])
    for v in range(n):
        clauses.append(inc[v][:] if inc[v] else [])
    # facets
    def on_boundary(F):
        for i in range(d):
            if all(ys[v][i] == 0 for v in F) or all(ys[v][i] == D for v in F):
                return True
        return False
    sides = {}
    hyper = {}
    for s in simp:
        for k in range(d + 1):
            F = tuple(v for j, v in enumerate(s) if j != k)
            apex = s[k]
            if F not in hyper:
                # integer normal: cofactors of the (d-1) x d edge matrix
                E = [[pts[F[r]][i] - pts[F[0]][i] for i in range(d)] for r in range(1, d)]
                nrm = []
                for i in range(d):
                    minor = [[row[c] for c in range(d) if c != i] for row in E]
                    nrm.append((-1) ** i * det_int(minor))
                off = sum(nrm[i] * pts[F[0]][i] for i in range(d))
                hyper[F] = (nrm, off)
            nrm, off = hyper[F]
            val = sum(nrm[i] * pts[apex][i] for i in range(d)) - off
            assert val != 0
            sides.setdefault(F, ([], []))[0 if val > 0 else 1].append(var[s])
    nA = nM = 0
    for F, (pos, neg) in sides.items():
        for grp in (pos, neg):
            for a, b in itertools.combinations(grp, 2):
                clauses.append([-a, -b]); nA += 1
        if not on_boundary(F):
            for s in pos:
                clauses.append([-s] + neg); nM += 1
            for s in neg:
                clauses.append([-s] + pos); nM += 1
    # (G) generic sample points, exact rational containment
    rng = random.Random(seed)
    Bm = B
    def to_x(lam):
        return [sum(Fraction(Bm[i][j]) * lam[j] for j in range(d)) for i in range(d)]
    hyps = list(hyper.values())
    samples = []
    tries = 0
    while len(samples) < K and tries < 100 * K:
        tries += 1
        lam = [Fraction(rng.randrange(1, 10**6), 10**6 + rng.randrange(1, 97)) for _ in range(d)]
        g = to_x(lam)
        if any(sum(nrm[i] * g[i] for i in range(d)) == off for nrm, off in hyps):
            continue
        samples.append(g)
    nG = 0
    if samples:
        import numpy as np
        P = np.array(pts, dtype=np.int64)
        Pf = P.astype(np.float64)
        S_arr = np.array(simp, dtype=np.int64)
        V0 = Pf[S_arr[:, 0]]
        Mt = np.transpose(Pf[S_arr[:, 1:]] - V0[:, None, :], (0, 2, 1))  # N x d x d (columns = edges)
        Minv = np.linalg.inv(Mt)
    for g in samples:
        gf = np.array([float(t) for t in g])
        lam = np.einsum('nij,nj->ni', Minv, gf[None, :] - V0)
        lam0 = 1 - lam.sum(axis=1)
        cand = np.nonzero((lam.min(axis=1) > -1e-6) & (lam0 > -1e-6))[0]
        inside = []
        for idx in cand:  # exact recheck
            s = simp[idx]
            Mx = [[pts[s[k]][i] - pts[s[0]][i] for k in range(1, d + 1)] for i in range(d)]
            rhs = [g[i] - pts[s[0]][i] for i in range(d)]
            sol = solve_frac(Mx, rhs)
            ok = sol is not None and all(c > 0 for c in sol)
            tot = sum(sol) if ok else Fraction(2)
            if ok and tot < 1:
                inside.append(var[simp[idx]])
        clauses.append(inside[:])
        for a, b in itertools.combinations(inside, 2):
            clauses.append([-a, -b])
        nG += 1
    with open(out, 'w') as f:
        f.write(f"p cnf {N} {len(clauses)}\n")
        for c in clauses:
            f.write(' '.join(map(str, c)) + ' 0\n')
    meta = {"d": d, "B": B, "det": D, "lattice_points": n, "unimodular_simplices": N,
            "facets": len(sides), "amo_clauses": nA, "match_clauses": nM,
            "samples": nG, "clauses": len(clauses), "simplices": simp, "points": pts}
    if meta_out:
        json.dump(meta, open(meta_out, 'w'))
    if '--varmap' in args:
        json.dump({"B": B, "simplices": [[pts[v] for v in s] for s in simp]},
                  open(args[args.index('--varmap') + 1], 'w'))
    print(json.dumps({k: meta[k] for k in meta if k not in ("simplices", "points")}))


if __name__ == '__main__':
    main()
