"""Witness search for a failing pair test (float optimisation with scipy),
followed by a rigorous interval check of the point found: both points
certainly lie in S and p.p' < -cos(2pi/17) certainly."""
import numpy as np
from scipy.optimize import minimize

import bnb
import fans
from ia import I


def _geo(fan, P, xi, sg):
    g = fan.evaluate([I(np.array([x])) for x in P], [I(np.array([x])) for x in xi], sg)
    p = np.array([float(np.ravel(q.mid)[0]) for q in g.p])
    cons = [float(np.ravel(g.rad.mid)[0])] + [float(np.ravel(fv.mid)[0]) for fv in g.facets] + \
           [0.5 - float(np.ravel(fans.dot5(g.p, u).mid)[0]) for _, u in g.verts]
    return p, np.array(cons)


def certify_point(fan, P, xi, xi2, s1, s2):
    """rigorous: True if both points are certainly in S and certainly
    p.p' < -kappa."""
    def ev(x, sg):
        g = fan.evaluate([I(np.array([v])) for v in P], [I(np.array([v])) for v in x], sg)
        ok = bool(np.all(g.rad.lo >= 0))
        for fv in g.facets:
            ok &= bool(np.all(fv.lo >= 0))
        for _, u in g.verts:
            ok &= bool(np.all(fans.dot5(g.p, u).hi <= 0.5))
        return ok, g
    ok1, g1 = ev(xi, s1)
    ok2, g2 = ev(xi2, s2)
    d = fans.dot5(g1.p, g2.p)
    return ok1 and ok2 and bool(np.all(d.hi < -bnb.KAP.hi)), float(np.ravel(d.hi)[0])


def pair_witness(fan, pbox=None, starts=(0.0, 0.5, 1.0), nsamp=300000, seed=0):
    import wcheck
    pb = pbox if pbox is not None else fan.param_box()
    fb = fan.free_box()
    npar = len(pb)
    best = None
    rng = np.random.default_rng(seed)
    for frac in starts:
        P0 = [lo + frac * (hi - lo) for lo, hi in pb]
        # sample both branches with their signs
        cand = []
        for sg in (1, -1):
            F = [I(rng.uniform(lo, hi, nsamp)) for lo, hi in fb]
            g = fan.evaluate([I(np.full(nsamp, x)) for x in P0], F, sg)
            ok = g.rad.lo >= 0
            for fv in g.facets:
                ok &= fv.lo >= 0
            for _, u in g.verts:
                ok &= fans.dot5(g.p, u).hi <= 0.5
            p = np.stack([np.broadcast_to(c.mid, (nsamp,)) for c in g.p], 1)[ok]
            x = np.stack([f.mid for f in F], 1)[ok]
            cand.append((p[:3000], x[:3000], sg))
        for (pa, xa, sa) in cand:
            for (pb_, xb, sb) in cand:
                if len(pa) == 0 or len(pb_) == 0:
                    continue
                G = pa @ pb_.T
                for t in range(3):
                    i, j = np.unravel_index(np.argsort(G, axis=None)[t * 7], G.shape)
                    x0 = np.concatenate([P0, xa[i], xb[j]])

                    def fun(x):
                        return _geo(fan, x[:npar], x[npar:npar + 3], sa)[0] @ _geo(fan, x[:npar], x[npar + 3:], sb)[0]

                    def con(x, margin=1e-9):
                        return np.concatenate([_geo(fan, x[:npar], x[npar:npar + 3], sa)[1],
                                               _geo(fan, x[:npar], x[npar + 3:], sb)[1]]) - margin
                    bounds = list(pb) + list(fb) + list(fb)
                    r = minimize(fun, x0, method="SLSQP", constraints=[{"type": "ineq", "fun": con}],
                                 bounds=bounds, options={"maxiter": 400, "ftol": 1e-14})
                    if con(r.x).min() < -1e-12:
                        continue
                    if best is None or r.fun < best[0]:
                        best = (float(r.fun), r.x.copy(), sa, sb)
    if best is None:
        return None
    val, x, sa, sb = best
    ok, dhi = certify_point(fan, x[:npar], x[npar:npar + 3], x[npar + 3:], sa, sb)
    return {"params": x[:npar].tolist(), "xi": x[npar:npar + 3].tolist(), "xi'": x[npar + 3:].tolist(),
            "signs": [sa, sb], "p.p'_float": val, "p.p'_upper": dhi, "rigorous": ok}
