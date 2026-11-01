"""A small exact LP solver (two-phase simplex, Bland's rule, Fractions).

maximise c.x subject to A_eq x = b_eq, A_ub x <= b_ub, with x free
(free variables are split as x = xp - xn). Returns (status, value, x):
status 'optimal', 'infeasible' or 'unbounded'.
"""
from fractions import Fraction


def _simplex(T, basis, ncols):
    """Tableau T (list of rows, last column rhs, last row objective -c),
    maximisation; Bland's rule. Returns 'optimal' or 'unbounded'."""
    m = len(T) - 1
    while True:
        obj = T[-1]
        enter = None
        for j in range(ncols):
            if obj[j] < 0:
                enter = j
                break
        if enter is None:
            return 'optimal'
        leave = None
        best = None
        for i in range(m):
            a = T[i][enter]
            if a > 0:
                r = T[i][-1] / a
                if best is None or r < best or (r == best and basis[i] < basis[leave]):
                    best = r
                    leave = i
        if leave is None:
            return 'unbounded'
        piv = T[leave][enter]
        row = [v / piv for v in T[leave]]
        T[leave] = row
        for i in range(len(T)):
            if i != leave and T[i][enter] != 0:
                f = T[i][enter]
                Ti = T[i]
                T[i] = [Ti[k] - f * row[k] for k in range(len(row))]
        basis[leave] = enter


def solve(c, A_eq, b_eq, A_ub, b_ub, nfree):
    """x has nfree free variables; all given as Fractions/ints."""
    F = Fraction
    n = nfree
    # variables: xp (n), xn (n), slacks for ub (len(A_ub)), artificials
    rows = []
    rhs = []
    nub = len(A_ub)
    for r, b in zip(A_eq, b_eq):
        rows.append([F(v) for v in r] + [-F(v) for v in r] + [F(0)] * nub)
        rhs.append(F(b))
    for k, (r, b) in enumerate(zip(A_ub, b_ub)):
        sl = [F(0)] * nub
        sl[k] = F(1)
        rows.append([F(v) for v in r] + [-F(v) for v in r] + sl)
        rhs.append(F(b))
    m = len(rows)
    nv = 2 * n + nub
    # make rhs >= 0
    for i in range(m):
        if rhs[i] < 0:
            rows[i] = [-v for v in rows[i]]
            rhs[i] = -rhs[i]
    # phase 1: artificials for every row
    T = []
    for i in range(m):
        art = [F(0)] * m
        art[i] = F(1)
        T.append(rows[i] + art + [rhs[i]])
    basis = [nv + i for i in range(m)]
    # objective: maximise -sum(art) -> row = -(-1 * ...) ; obj row = sum of rows negated for art basis
    obj = [F(0)] * (nv + m + 1)
    for i in range(m):
        for k in range(nv + m + 1):
            obj[k] -= T[i][k]
    for i in range(m):
        obj[nv + i] += 1  # artificial columns had -1*1 subtracted; reduced cost 0
    T.append(obj)
    st = _simplex(T, basis, nv + m)
    if T[-1][-1] != 0:
        return 'infeasible', None, None
    # drive artificials out of basis where possible
    for i in range(m):
        if basis[i] >= nv:
            for j in range(nv):
                if T[i][j] != 0:
                    piv = T[i][j]
                    row = [v / piv for v in T[i]]
                    T[i] = row
                    for k in range(len(T)):
                        if k != i and T[k][j] != 0:
                            f = T[k][j]
                            T[k] = [T[k][q] - f * row[q] for q in range(len(row))]
                    basis[i] = j
                    break
    # remove artificial columns
    T2 = []
    b2 = []
    for i in range(m):
        if basis[i] < nv:
            T2.append(T[i][:nv] + [T[i][-1]])
            b2.append(basis[i])
    cc = [F(v) for v in c] + [-F(v) for v in c] + [F(0)] * nub
    obj = [-v for v in cc] + [F(0)]
    for i, bi in enumerate(b2):
        if obj[bi] != 0:
            f = obj[bi]
            obj = [obj[k] - f * T2[i][k] for k in range(nv + 1)]
    T2.append(obj)
    st = _simplex(T2, b2, nv)
    if st == 'unbounded':
        return 'unbounded', None, None
    x = [F(0)] * nv
    for i, bi in enumerate(b2):
        x[bi] = T2[i][-1]
    xs = [x[k] - x[n + k] for k in range(n)]
    return 'optimal', T2[-1][-1], xs
