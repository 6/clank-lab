"""Vectorised interval branch-and-bound for the (W) tests.

A test is a pair (objective, threshold): it is CERTIFIED when every box of
(parameters x chart) is either infeasible (rad < 0, some facet function < 0,
or p.u > 1/2 for some fan vertex u, all certified) or satisfies
objective > threshold (certified).  Boxes are bisected along the coordinate
with the largest width relative to the initial box.
"""
import time
import numpy as np

import fans
from ia import I, const, sqrt

KAP = const(fans.KAPPA)        # outward enclosure of cos(2pi/17)
SUMTHR = float(const(2 - 2 * fans.KAPPA).hi)   # >= 2 - 2 kappa
BET = const(fans.BETA)         # outward enclosure of sin(pi/17)


def classify(fan, lo, hi, sign, objective):
    """lo, hi: (N, D) arrays. Returns (status array: 0 undecided, 1 infeasible,
    2 proved; objective interval)."""
    npar = fan.nparam
    P = [I(lo[:, j], hi[:, j]) for j in range(npar)]
    F = [I(lo[:, j], hi[:, j]) for j in range(npar, lo.shape[1])]
    g = fan.evaluate(P, F, sign)
    infeas = g.rad.hi < 0
    for fv in g.facets:
        infeas |= fv.hi < 0
    for name, u in g.verts:
        if fans.CORRUPT != "nodist":
            infeas |= fans.dot5(g.p, u).lo > 0.5
    obj, thr = objective(fan, P, g)
    proved = obj.lo > thr
    st = np.zeros(len(lo), dtype=np.int8)
    st[proved] = 2
    st[infeas] = 1
    return st, obj


def obj_vertex(name):
    def f(fan, P, g):
        u = dict(g.verts)[name]
        return fans.dot5(g.p, u), -KAP.lo   # need p.u > -kappa; -KAP.lo >= -kappa
    f.label = f"vertex {name}"
    return f


def obj_udir():
    def f(fan, P, g):
        u = fan.udir(P)
        # need p.u > beta |u|
        n = sqrt(u[0].sq() + u[1].sq() + u[2].sq() + u[3].sq() + u[4].sq())
        return fans.dot5(g.p, u), (BET * n).hi
    f.label = "pair (direction test)"
    return f


def point_check(fan, x, sign, objective):
    """rigorous check at points x (N, D): True where the point is certainly
    feasible and certainly violates the claim (objective < threshold)."""
    npar = fan.nparam
    P = [I(x[:, j]) for j in range(npar)]
    F = [I(x[:, j]) for j in range(npar, x.shape[1])]
    g = fan.evaluate(P, F, sign)
    feas = g.rad.lo >= 0
    for fv in g.facets:
        feas &= fv.lo >= 0
    for name, u in g.verts:
        if fans.CORRUPT != "nodist":
            feas &= fans.dot5(g.p, u).hi <= 0.5
    obj, thr = objective(fan, P, g)
    return feas & (obj.hi < thr), obj, g, np.broadcast_to(thr, obj.hi.shape)


def run(fan, objective, sign, max_boxes=200_000_000, chunk=200_000, min_rel=2.0 ** -30,
        pbox=None, fbox=None):
    t0 = time.process_time()
    pb = pbox if pbox is not None else fan.param_box()
    fb = fbox if fbox is not None else fan.free_box()
    box0 = np.array(pb + fb, dtype=np.float64)
    scale = box0[:, 1] - box0[:, 0]
    scale[scale < 1e-9] = np.inf     # point parameters (e.g. n fixed) are never split
    stack = [(box0[None, :, 0].copy(), box0[None, :, 1].copy())]
    evaluated = 0
    unresolved = []
    maxdepth_boxes = 0
    while stack:
        l, h = stack.pop()
        st, obj = classify(fan, l, h, sign, objective)
        evaluated += len(l)
        und = st == 0
        if not und.any():
            continue
        l, h = l[und], h[und]
        mid = 0.5 * (l + h)
        bad, pobj, g, pthr = point_check(fan, mid, sign, objective)
        if bad.any():
            i = int(np.argmax(bad))
            cpu = time.process_time() - t0
            return {"ok": False, "boxes": evaluated, "cpu": cpu, "unresolved": 0, "pending": 0,
                    "witness": {"params+chart": mid[i].tolist(), "sign": sign,
                                "objective_upper": float(pobj.hi[i]), "threshold": float(pthr[i]),
                                "p": [float(np.broadcast_to(c.mid, (len(mid),))[i]) for c in g.p],
                                "rigorous": True}}
        rel = (h - l) / scale
        d = rel.argmax(axis=1)
        small = rel[np.arange(len(l)), d] < min_rel
        if small.any():
            unresolved.append((l[small], h[small]))
            l, h, d = l[~small], h[~small], d[~small]
            if sum(len(x[0]) for x in unresolved) > 1000:
                break
        if len(l) == 0:
            continue
        idx = np.arange(len(l))
        m = 0.5 * (l[idx, d] + h[idx, d])
        h1 = h.copy()
        h1[idx, d] = m
        l2 = l.copy()
        l2[idx, d] = m
        L = np.concatenate([l, l2])
        H = np.concatenate([h1, h])
        for k in range(0, len(L), chunk):
            stack.append((L[k:k + chunk], H[k:k + chunk]))
        if evaluated > max_boxes:
            break
    cpu = time.process_time() - t0
    nunres = sum(len(x[0]) for x in unresolved)
    pending = sum(len(x[0]) for x in stack)
    ok = nunres == 0 and pending == 0
    res = {"ok": ok, "boxes": evaluated, "cpu": cpu, "unresolved": nunres, "pending": pending}
    if not ok:
        U = unresolved + stack
        res["witness"] = witness(fan, objective, sign, np.concatenate([u[0] for u in U]),
                                 np.concatenate([u[1] for u in U]))
    return res


def witness(fan, objective, sign, lo, hi, nsamp=20000):
    """float search for a feasible point violating the claim in the given
    boxes (exploration aid for a FAILED report)."""
    if lo is None:
        return None
    rng = np.random.default_rng(0)
    idx = rng.integers(0, len(lo), nsamp)
    x = lo[idx] + (hi[idx] - lo[idx]) * rng.random((nsamp, lo.shape[1]))
    x = np.vstack([x, 0.5 * (lo + hi)])
    st_obj = []
    npar = fan.nparam
    P = [I(x[:, j]) for j in range(npar)]
    F = [I(x[:, j]) for j in range(npar, x.shape[1])]
    g = fan.evaluate(P, F, sign)
    tol = 1e-9
    feas = g.rad.mid >= -tol
    viol = np.zeros(len(x))
    for fv in g.facets:
        feas &= fv.mid >= -tol
    for name, u in g.verts:
        feas &= fans.dot5(g.p, u).mid <= 0.5 + tol
    obj, thr = objective(fan, P, g)
    bad = feas & (obj.mid <= thr)
    if bad.any():
        i = np.argmin(np.where(bad, obj.mid, np.inf))
        return {"params+chart": x[i].tolist(), "objective": float(obj.mid[i]), "threshold": float(thr),
                "p": [float(np.ravel(c.mid)[i] if np.ndim(c.mid) else c.mid) for c in g.p]}
    return {"note": "no float violation found in unresolved boxes", "min_obj_feasible":
            float(np.where(feas, obj.mid, np.inf).min())}


# --------------------------------------------------------------------------
def run_pair(fan, signs, max_boxes=400_000_000, chunk=100_000, min_rel=2.0 ** -26, pbox=None):
    """dual-tree branch-and-bound for the pair condition: certify
    p.p' > -kappa for all p, p' in S (same parameters), p on branch signs[0],
    p' on branch signs[1].  Boxes are (params, chart of p, chart of p')."""
    t0 = time.process_time()
    pb = pbox if pbox is not None else fan.param_box()
    fb = fan.free_box()
    npar = len(pb)
    box0 = np.array(pb + fb + fb, dtype=np.float64)
    scale = box0[:, 1] - box0[:, 0]
    scale[scale < 1e-9] = np.inf     # point parameters (e.g. n fixed) are never split
    D = box0.shape[0]
    stack = [(box0[None, :, 0].copy(), box0[None, :, 1].copy())]
    evaluated = 0
    unresolved = []
    thr = -KAP.lo
    s1, s2 = signs

    def feasible_and_p(l, h, off, sign):
        P = [I(l[:, j], h[:, j]) for j in range(npar)]
        F = [I(l[:, j], h[:, j]) for j in range(off, off + 3)]
        g = fan.evaluate(P, F, sign)
        inf = g.rad.hi < 0
        for fv in g.facets:
            inf |= fv.hi < 0
        for _, u in g.verts:
            if fans.CORRUPT != "nodist":
                inf |= fans.dot5(g.p, u).lo > 0.5
        return inf, g

    def certainly_feasible(g):
        ok = g.rad.lo >= 0
        for fv in g.facets:
            ok &= fv.lo >= 0
        for _, u in g.verts:
            if fans.CORRUPT != "nodist":
                ok &= fans.dot5(g.p, u).hi <= 0.5
        return ok

    while stack:
        l, h = stack.pop()
        inf1, g1 = feasible_and_p(l, h, npar, s1)
        inf2, g2 = feasible_and_p(l, h, npar + 3, s2)
        d = fans.dot5(g1.p, g2.p)
        # second bound: |p + p'|^2 = 2 + 2 p.p' <= 2 - 2 kappa for a long pair
        q = (g1.p[0] + g2.p[0]).sq()
        for a, b in zip(g1.p[1:], g2.p[1:]):
            q = q + (a + b).sq()
        evaluated += len(l)
        und = ~(inf1 | inf2) & ~(d.lo > thr) & ~(q.lo > SUMTHR)
        if not und.any():
            continue
        l, h = l[und], h[und]
        mid = 0.5 * (l + h)
        f1, m1 = feasible_and_p(mid, mid, npar, s1)
        f2, second_midpoint = feasible_and_p(mid, mid, npar + 3, s2)
        dm = fans.dot5(m1.p, second_midpoint.p)
        bad = certainly_feasible(m1) & certainly_feasible(second_midpoint) & (np.broadcast_to(dm.hi, (len(mid),)) < thr)
        if bad.any():
            i = int(np.argmax(bad))
            pv = [float(np.broadcast_to(c.mid, (len(mid),))[i]) for c in m1.p]
            qv = [float(np.broadcast_to(c.mid, (len(mid),))[i]) for c in second_midpoint.p]
            return {"ok": False, "boxes": evaluated, "cpu": time.process_time() - t0, "unresolved": 0,
                    "pending": 0, "witness": {"params": mid[i, :npar].tolist(), "p": pv, "p'": qv,
                                              "p.p'_upper": float(np.broadcast_to(dm.hi, (len(mid),))[i]),
                                              "threshold": float(thr), "rigorous": True}}
        rel = (h - l) / scale
        k = rel.argmax(axis=1)
        small = rel[np.arange(len(l)), k] < min_rel
        if small.any():
            unresolved.append((l[small], h[small]))
            l, h, k = l[~small], h[~small], k[~small]
            if sum(len(x[0]) for x in unresolved) > 1000:
                break
        if len(l) == 0:
            continue
        idx = np.arange(len(l))
        m = 0.5 * (l[idx, k] + h[idx, k])
        h1 = h.copy()
        h1[idx, k] = m
        l2 = l.copy()
        l2[idx, k] = m
        L = np.concatenate([l, l2])
        H = np.concatenate([h1, h])
        for j in range(0, len(L), chunk):
            stack.append((L[j:j + chunk], H[j:j + chunk]))
        if evaluated > max_boxes:
            break
    nunres = sum(len(x[0]) for x in unresolved)
    pending = sum(len(x[0]) for x in stack)
    return {"ok": nunres == 0 and pending == 0, "boxes": evaluated, "cpu": time.process_time() - t0,
            "unresolved": nunres, "pending": pending}
