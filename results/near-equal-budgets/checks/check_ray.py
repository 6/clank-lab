#!/usr/bin/env python3
"""Checker 2 (independent of the certificates): exact primal LPs along the ray of budgets e + delta*d.

For each allocation X (every good to one agent) and the closed CE system
    p >= 0, delta >= 0,  p(X_i) <= 1 + delta*d_i,  p(Y) >= 1 + delta*d_i  for every bundle Y
    that agent i strictly prefers to X_i (all such bundles, additive values),
its feasible deltas form a closed interval (a convex set).  This program computes, with an exact
rational two-phase simplex (Bland's rule), lo_X = min delta, and hi_X = max delta when lo_X = 0.
It passes iff every allocation is infeasible, or has lo_X > 0, or has lo_X = hi_X = 0; it prints
R = min lo_X over the allocations with lo_X > 0.  Then for 0 < delta < R the closed system, hence
the CE system (prices > 0, strict inequalities), is infeasible for every allocation.
Usage: check_ray.py instance.json   (exit status 0 iff the check passes)
"""
import json, sys, itertools
from fractions import Fraction

INF = None


def simplex_max(c, A, b):
    """max c.x s.t. A x <= b, x >= 0, exact.  Returns ('infeasible'|'unbounded'|'optimal', value)."""
    nr, nv = len(A), len(c)
    # variables: x (nv), slack s (nr), artificial a (one per row with b < 0)
    neg = [i for i in range(nr) if b[i] < 0]
    na = len(neg)
    ncol = nv + nr + na
    T = []
    basis = []
    for i in range(nr):
        sign = -1 if b[i] < 0 else 1
        row = [Fraction(sign * A[i][j]) for j in range(nv)]
        row += [Fraction(sign if k == i else 0) for k in range(nr)]
        row += [Fraction(1 if (i in neg and neg.index(i) == k) else 0) for k in range(na)]
        row.append(Fraction(sign * b[i]))
        T.append(row)
        basis.append(nv + nr + neg.index(i) if i in neg else nv + i)

    def pivot(r, col):
        pr = T[r]; pv = pr[col]
        T[r] = [x / pv for x in pr]
        for i in range(nr):
            if i != r and T[i][col] != 0:
                f = T[i][col]
                T[i] = [x - f * y for x, y in zip(T[i], T[r])]
        basis[r] = col

    def run(obj, allowed):
        # obj: coefficients to maximise over columns; reduced costs computed from basis
        while True:
            red = [obj[j] - sum(obj[basis[i]] * T[i][j] for i in range(nr)) for j in range(ncol)]
            col = next((j for j in range(ncol) if allowed[j] and red[j] > 0), None)
            if col is None:
                return "optimal"
            rows = [(T[i][-1] / T[i][col], basis[i], i) for i in range(nr) if T[i][col] > 0]
            if not rows:
                return "unbounded"
            r = min(rows)[2]
            pivot(r, col)

    if na:
        obj1 = [Fraction(0)] * (nv + nr) + [Fraction(-1)] * na
        run(obj1, [True] * ncol)
        if sum(T[i][-1] for i in range(nr) if basis[i] >= nv + nr) != 0:
            return "infeasible", None
        for i in range(nr):  # drive remaining artificials out of the basis
            if basis[i] >= nv + nr:
                col = next((j for j in range(nv + nr) if T[i][j] != 0), None)
                if col is not None:
                    pivot(i, col)
    obj2 = [Fraction(x) for x in c] + [Fraction(0)] * (nr + na)
    allowed = [True] * (nv + nr) + [False] * na
    status = run(obj2, allowed)
    if status == "unbounded":
        return "unbounded", None
    x = [Fraction(0)] * ncol
    for i in range(nr):
        x[basis[i]] = T[i][-1]
    return "optimal", sum(obj2[j] * x[j] for j in range(ncol))


def main(path):
    inst = json.load(open(path))
    V, d = inst["values"], [Fraction(x) for x in inst["direction"]]
    n, m = len(V), len(V[0])
    value = lambda i, S: sum(V[i][g] for g in range(m) if S >> g & 1)
    R = None
    counts = {"infeasible": 0, "positive_lo": 0, "only_zero": 0}
    for own in itertools.product(range(n), repeat=m):
        X = [sum(1 << g for g in range(m) if own[g] == i) for i in range(n)]
        A, b = [], []
        for i in range(n):
            A.append([1 if X[i] >> g & 1 else 0 for g in range(m)] + [-d[i]]); b.append(1)
            for Y in range(1, 1 << m):
                if value(i, Y) > value(i, X[i]):
                    A.append([-1 if Y >> g & 1 else 0 for g in range(m)] + [d[i]]); b.append(-1)
        st, v = simplex_max([0] * m + [-1], A, b)  # max -delta = -lo
        if st == "infeasible":
            counts["infeasible"] += 1
            continue
        lo = -v
        if lo > 0:
            counts["positive_lo"] += 1
            R = lo if R is None or lo < R else R
            continue
        st, hi = simplex_max([0] * m + [1], A, b)
        if st != "optimal" or hi != 0:
            print(f"FAIL: allocation {own} feasible for delta in [0, {hi if st == 'optimal' else 'inf'}]")
            return 1
        counts["only_zero"] += 1
    print(f"OK: {n ** m} allocations; {counts}; R={'infinity' if R is None else R}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
