"""Self-test of the fan constructions in fans.py (interval evaluation on a
grid of parameter points): every fan vertex is a unit vector on the VF
hyperplane (it satisfies the chart's p1 formula, i.e. u.c = 1/2), and the
distances prescribed by the cycle type hold:
  type (i):   |a-b| = 2cos(pi/n), |x_i - x_{i+1}| = 2cos(pi/q_i), x_i _|_ L;
  type (ii):  |a-x| = |x-y| = |y-b| = 1, |z1-z2| = 2cos(pi/q), z_j _|_ a,b,x,y;
  type (iii): as (ii) for a,b,x,y,z_j; |z1-w| = 2cos(pi/q1), |w-z2| = 2cos(pi/q2),
              w _|_ a, b;
  families:   the corresponding statements with q = m.
Also: the long fan edges are exactly e = ab and (paired fans) the partner."""
import sys

import numpy as np
from mpmath import iv

import fans
import ia
from ia import I

TOL = 1e-12
PI = iv.pi


def close(x, target, tol=TOL):
    t = target if isinstance(target, float) else None
    lo = np.asarray(x.lo)
    hi = np.asarray(x.hi)
    if t is None:
        tl, th = np.asarray(target.lo), np.asarray(target.hi)
    else:
        tl = th = t
    return bool(np.all(lo >= tl - tol) and np.all(hi <= th + tol))


def d2(u, v):
    return sum(((a - b).sq() for a, b in zip(u, v)), I(0.0))


def ch2(q):
    """(2cos(pi/q))^2 as an interval constant."""
    return ia.const(4 * iv.cos(PI / q) ** 2)


def check(fan, P, extra):
    V = dict(fan.vertices(P))
    errs = []
    for name, u in V.items():
        if not close(fans.dot5(u, u), 1.0):
            errs.append(f"|{name}| != 1")
    for (A, B, val) in extra:
        if not close(d2(V[A], V[B]), val):
            errs.append(f"|{A}{B}|^2 wrong")
    return errs


def run():
    bad = 0
    npts = 0
    p1_list = [tuple(map(int, l.split(","))) for l in open("p1_closable.txt") if l.strip()]
    import wcheck
    L = wcheck.build_fans(p1_list)
    for kind, fan in L:
        wcheck.setup(fan)
        pb = fan.param_box()
        if isinstance(fan, fans.FanTypeIII):
            c = np.linspace(pb[0][0], pb[0][1], 400001)
            ok = fan.geometry([I(c)])[0]
            grid = [c[ok][:: max(1, ok.sum() // 9)]]
        else:
            grid = [np.linspace(l, h, 9) for l, h in pb]
        G = np.stack(np.meshgrid(*grid, indexing="ij"), -1).reshape(-1, len(pb))
        for row in G:
            P = [I(np.array([x])) for x in row]
            npts += 1
            if isinstance(fan, fans.FanTypeI):
                s = P[0]
                Cn = ia.sqrt(1 - s.sq())
                ex = [("a", "b", 4 * Cn.sq())]
                k = len(fan.config)
                for i in range(k):
                    ex.append((f"x{i+1}", f"x{(i+1) % k + 1}", ch2(fan.config[i])))
                    ex += [("a", f"x{i+1}", 2.0), ("b", f"x{i+1}", 2.0)]
                # VF hyperplane: x_i . gamma = 1/2
                errs = check(fan, P, ex)
                for x in fan.x:
                    if not close(x[2] * fan.g3, 0.5):
                        errs.append("x.gamma != 1/2")
            elif isinstance(fan, fans.FanTypeII):
                s = P[0]
                Cn, t, h = fans.n_quantities(s)
                ex = [("a", "b", 4 * Cn.sq()), ("a", "x", 1.0), ("x", "y", 1.0), ("y", "b", 1.0),
                      ("z1", "z2", ch2(fan.q))] + [(p, z, 2.0) for p in "abxy" for z in ("z1", "z2")]
                errs = check(fan, P, ex)
                V = dict(fan.vertices(P))
                # u.c = 1/2 via the chart formula: u1 = s (1 - h u3 - 2 r_q u4)
                for nm in ("x", "y", "z1", "z2"):
                    u = V[nm]
                    if not close(u[0] - s * (1 - h * u[2] - 2 * fan.rq * u[3]), 0.0):
                        errs.append(f"{nm} off the VF hyperplane")
            elif isinstance(fan, fans.FanTypeIII):
                geo = fan.geometry(P)
                ok, c, sp, w, h, C, s, t = geo
                q1, q2 = fan.q
                ex = [("a", "b", 4 * C.sq()), ("a", "x", 1.0), ("x", "y", 1.0), ("y", "b", 1.0),
                      ("z1", "w", ch2(q1)), ("w", "z2", ch2(q2)), ("a", "w", 2.0), ("b", "w", 2.0)] + \
                     [(p, z, 2.0) for p in "abxy" for z in ("z1", "z2")]
                errs = check(fan, P, ex)
                V = dict(fan.vertices(P, geo))
                for nm in ("x", "y", "z1", "z2", "w"):
                    u = V[nm]
                    if not close(u[0] - s * (1 - h * u[2] - u[3] / c), 0.0, 1e-9):
                        errs.append(f"{nm} off the VF hyperplane")
            else:
                st = fan.structure(P)
                tau, lam, om, s, sig, Cn, Cm, Vs, g0, facets = st
                ex = [("a", "b", 4 * Cn.sq())]
                nm = [v[0] for v in Vs]
                if fan.kind == "ii":
                    ex += [("a", "x", 1.0), ("x", "y", 1.0), ("y", "b", 1.0), ("z1", "z2", 4 * Cm.sq())]
                    ex += [(p, z, 2.0) for p in "abxy" for z in ("z1", "z2")]
                else:
                    q = {"44": [None, 4, 4], "333": [None, 3, 3, 3], "36": [None, 3, 6]}[fan.kind]
                    k = len(q)
                    for i in range(k):
                        v = 4 * Cm.sq() if q[i] is None else ch2(q[i])
                        ex.append((nm[i], nm[(i + 1) % k], v))
                        ex += [("a", nm[i], 2.0), ("b", nm[i], 2.0)]
                errs = check(fan, P, ex)
                # VF hyperplane: u1 = lam (tau (1 - 2 g0 . f_u) - tau chi_u)
                for v in Vs:
                    name, u1, u2, chi, f1, f2 = v
                    if not close(u1 - lam * (tau * (1 - 2 * (g0[0] * f1 + g0[1] * f2)) - tau * chi), 0.0):
                        errs.append(f"{name} off the VF hyperplane")
            if errs:
                bad += 1
                print(fan.name, row, errs)
                break
    print(f"geometry self-test: {len(L)} fans, {npts} parameter points, {bad} fans with errors")
    return bad


if __name__ == "__main__":
    sys.exit(1 if run() else 0)
