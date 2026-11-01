"""Exact (rational) versions of the angle and length margin LPs."""
from fractions import Fraction as F

from exact_lp import solve


def angle_margin(rows, n, pattern):
    """Exact max margin t (capped at 1) of the angle system; see angles.py."""
    nv = n + 1
    A_eq = [[1] * n + [0]]
    b_eq = [(n - 2) * 180]
    A_ub = []
    b_ub = []
    for kind, coef, const in rows:
        if kind == 'E':
            if sum(coef) == 0:
                if const != 360:
                    return F(-1)
                continue
            A_eq.append(list(coef) + [0])
            b_eq.append(360 - const)
        else:
            A_ub.append(list(coef) + [1])
            b_ub.append(360 - const)
    for i in range(n):
        r = [0] * nv; r[i] = -1; r[n] = 1; A_ub.append(r); b_ub.append(0)
        r = [0] * nv; r[i] = 1; r[n] = 1; A_ub.append(r); b_ub.append(360)
        r = [0] * nv
        if pattern[i]:
            r[i] = -1; r[n] = 1; A_ub.append(r); b_ub.append(-180)
        else:
            r[i] = 1; r[n] = 1; A_ub.append(r); b_ub.append(180)
    r = [0] * nv; r[n] = 1; A_ub.append(r); b_ub.append(1)
    c = [0] * n + [1]
    st, val, x = solve(c, A_eq, b_eq, A_ub, b_ub, nv)
    if st == 'infeasible':
        return F(-1)
    return val


def length_margin(n, nseg, lrows):
    nv = n + nseg + 1
    A_eq = [[1] * n + [0] * nseg + [0]]
    b_eq = [1]
    for elab, sl in lrows:
        r = [0] * nv
        r[elab] -= 1
        for s in sl:
            r[n + s] += 1
        A_eq.append(r)
        b_eq.append(0)
    A_ub = []
    b_ub = []
    for i in range(n + nseg):
        r = [0] * nv; r[i] = -1; r[-1] = 1; A_ub.append(r); b_ub.append(0)
    r = [0] * nv; r[-1] = 1; A_ub.append(r); b_ub.append(1)
    c = [0] * (nv - 1) + [1]
    st, val, x = solve(c, A_eq, b_eq, A_ub, b_ub, nv)
    if st == 'infeasible':
        return F(-1)
    return val
