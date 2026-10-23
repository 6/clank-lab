#!/usr/bin/env python3
"""Exact spectral projections: the strongly cospectral class of vertex 0 of Cay(Z_2^d, S),
computed from the definition (E_theta e_0 = +-E_theta e_g for every
eigenvalue theta) with exact integer arithmetic, equals
K(S) = {g : a.g = b.g whenever lambda_a = lambda_b}.

Spectrum: candidate integers theta in [-n, n] (eigenvalues of a cubelike graph
are integers there by R1's character basis, but here they are found without
it): mult(theta) = 2^d - rank(A - theta I), rank computed exactly by
fraction-free elimination; we require sum of multiplicities = 2^d, so all
eigenvalues are found. E_theta is proportional to
P_theta(A) = prod_{theta' != theta} (A - theta' I), so the test is
P_theta(A) e_g = +- P_theta(A) e_0 (exact integers).

This module uses only the Python standard library.
"""

def rank_exact(M):
    M = [row[:] for row in M]; r = 0; n = len(M); m = len(M[0]); prev = 1
    for c in range(m):
        p = next((i for i in range(r, n) if M[i][c] != 0), None)
        if p is None: continue
        M[r], M[p] = M[p], M[r]
        for i in range(r + 1, n):
            M[i] = [(M[r][c] * M[i][j] - M[i][c] * M[r][j]) // prev for j in range(m)]
        prev = M[r][c]; r += 1
        if r == n: break
    return r

def sc_class_direct(d, S):
    N = 1 << d; Sset = set(S); n = len(S)
    A = [[1 if (x ^ y) in Sset else 0 for y in range(N)] for x in range(N)]
    spec = {}
    for t in range(-n, n + 1):
        M = [[A[i][j] - (t if i == j else 0) for j in range(N)] for i in range(N)]
        k = N - rank_exact(M)
        if k: spec[t] = k
    assert sum(spec.values()) == N, "spectrum incomplete"
    def apply(v, t):  # (A - tI) v
        return [sum(v[y] for y in range(N) if A[x][y]) - t * v[x] for x in range(N)]
    cls = set(range(N))
    for th in spec:
        cols = {}
        for g in list(cls):
            v = [1 if x == g else 0 for x in range(N)]
            for t2 in spec:
                if t2 != th: v = apply(v, t2)
            cols[g] = v
        v0 = cols[0]
        cls = {g for g in cls if cols[g] == v0 or cols[g] == [-z for z in v0]}
    return cls, spec

def K_char(d, S):
    N = 1 << d
    lam = [sum(1 - 2 * (bin(a & s).count("1") & 1) for s in S) for a in range(N)]
    return {g for g in range(N)
            if all((bin(a & g).count("1") & 1) == (bin(b & g).count("1") & 1)
                   for a in range(N) for b in range(N) if lam[a] == lam[b])}
