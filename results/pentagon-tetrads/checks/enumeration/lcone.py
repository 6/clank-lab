"""Exact projected length cone of a labelled placement.

Variables z = (l_0..l_{n-1}, x_segments) >= 0 with the length rows
(-l_label + sum of segments = 0). The feasible lengths are the projection to
l of the cone {z >= 0 : A z = 0}; tilings need z > 0 componentwise, i.e. l in
the relative interior of the projection when a strictly positive z exists.
Rays are computed exactly (sympy rationals) by vertex enumeration of the
cone in nullspace coordinates.
"""
import itertools

import sympy as sp


def length_matrix(n, nseg, lrows):
    M = sp.zeros(len(lrows), n + nseg)
    for i, (el, sl) in enumerate(lrows):
        M[i, el] -= 1
        for s in sl:
            M[i, n + s] += 1
    return M


def cone_rays(M):
    """Extreme rays of {z >= 0 : M z = 0} (pointed: inside the orthant)."""
    N = M.nullspace()
    if not N:
        return []
    B = sp.Matrix.hstack(*N)  # z = B c
    m, k = B.shape
    rays = []
    seen = set()
    for S in itertools.combinations(range(m), k - 1):
        sub = B.extract(list(S), list(range(k)))
        ns = sub.nullspace()
        if len(ns) != 1:
            continue
        c = ns[0]
        for sgn in (1, -1):
            z = B * (sgn * c)
            if all(v >= 0 for v in z) and any(v != 0 for v in z):
                # normalise
                g = [v for v in z if v != 0][0]
                zz = tuple(sp.nsimplify(v / abs(g)) for v in z)
                den = sp.ilcm(*[sp.fraction(v)[1] for v in zz])
                zz = tuple(int(v * den) for v in zz)
                gg = sp.igcd(*[v for v in zz if v != 0])
                zz = tuple(v // gg for v in zz)
                if zz not in seen:
                    seen.add(zz)
                    rays.append(zz)
    # keep only extreme ones: support-minimal
    ext = []
    for r in rays:
        sup = {i for i, v in enumerate(r) if v}
        if not any({i for i, v in enumerate(q) if v} < sup for q in rays):
            ext.append(r)
    return ext


def projected_rays(n, nseg, lrows):
    M = length_matrix(n, nseg, lrows)
    rays = cone_rays(M)
    proj = []
    for r in rays:
        p = tuple(r[:n])
        if any(p):
            g = sp.igcd(*[v for v in p if v])
            p = tuple(v // g for v in p)
            if p not in proj:
                proj.append(p)
    # remove projected rays that are positive combinations of others (redundant)
    out = []
    for i, p in enumerate(proj):
        others = [q for j, q in enumerate(proj) if j != i]
        if others and _in_cone(p, others):
            continue
        out.append(p)
    return out, rays


def _in_cone(p, gens):
    from scipy.optimize import linprog
    import numpy as np
    A = np.array(gens, float).T
    res = linprog(np.zeros(len(gens)), A_eq=A, b_eq=np.array(p, float), bounds=[(0, None)] * len(gens),
                  method='highs')
    return res.status == 0
