"""Rigorous vertex stars of the 4-D facets (arb balls), for the certified stage 2.

star(name) -> dict(R, v0, nbrs, cells): every facet centred at its circumcentre (the
origin), v0 a vertex, nbrs its neighbours (unit edges), cells the cells at v0 as
(cell type, tuple of neighbour indices in cyclic order around v0 within the cell).
Coordinates come from rigorous sources only: Wythoff local data (cert_wythoff), the
vertex-configuration data of uniform polyhedra (cert_poly3) for prisms and antiprism
prisms, closed forms for duoprisms, exact Q(sqrt 5) points (cert_facets4.q5_600cell) for
the snub 24-cell and the grand antiprism.  Combinatorics (which neighbours span which cell,
cell types, cyclic order) are read from the float construction after matching points.
"""
import itertools, math
import numpy as np
from flint import arb, ctx
import cert_poly3 as cp
import cert_wythoff as cw
from cert_stage1 import cell_configs
ctx.prec = 200
PI = arb.pi()
CONF = cell_configs(40)

def fl(v):
    return np.array([float(x.mid()) for x in v])

def prism_name(q):
    return 'cube' if q == 4 else 'P%d' % q

def cyclic(v0f, pts_f, idx):
    """Order neighbour indices idx cyclically around v0 (their points lie on a circle in a plane
    for a 3-D cell's vertex figure)."""
    P = np.array([pts_f[i] for i in idx])
    c = P.mean(axis=0)
    U, S, Vt = np.linalg.svd(P - c)
    Q = (P - c) @ Vt[:2].T
    ang = np.arctan2(Q[:, 1], Q[:, 0])
    return tuple((idx[i] for i in np.argsort(ang)))

def _finish(R, v0, nbrs, Vf, nbf, match):
    from facets4d_all import cells_of
    from known4d import cell_name
    from geom import Polytope
    nf = [fl(p) for p in nbrs]
    cells = []
    for cc in cells_of(Vf):
        if 0 not in cc:
            continue
        idx = [match[w] for w in nbf if w in cc]
        cells.append((cell_name(Polytope(Vf[sorted(cc)])), cyclic(fl(v0), nf, idx)))
    return dict(R=R, v0=v0, nbrs=nbrs, cells=cells)

def _match(nbrs, Vf, nbf):
    match = {}
    for w in nbf:
        j = min(range(len(nbrs)), key=lambda j: np.linalg.norm(fl(nbrs[j]) - Vf[w]))
        if not np.linalg.norm(fl(nbrs[j]) - Vf[w]) < 1e-08:
            raise AssertionError()
        match[w] = j
    if not len(set(match.values())) == len(nbf) == len(nbrs):
        raise AssertionError()
    return match

def wythoff_star(group, rings):
    from geom import coxeter_matrix, wythoff
    Vf = wythoff([group], rings)
    v0, nbrs, R = cw.local_data([coxeter_matrix(group).tolist()], rings)
    if not np.linalg.norm(fl(v0) - Vf[0]) < 1e-08:
        raise AssertionError()
    nbf = [w for w in range(len(Vf)) if abs(np.linalg.norm(Vf[w] - Vf[0]) - 1) < 1e-06]
    return _finish(R, v0, nbrs, Vf, nbf, _match(nbrs, Vf, nbf))

def polyhedron_star(cell):
    """Vertex star of a uniform polyhedron from its vertex configuration, centred at the origin:
    returns (R, v (3-vector), neighbours in cyclic order, faces [(q, (i, i+1))])."""
    conf = CONF[cell]
    d = cp.data(conf)
    rho, R = (d['rho'], d['R'])
    h = (1 - rho * rho).sqrt()
    z = (h * h - rho * rho) / (2 * h)
    angs, t = ([], arb(0))
    for q in conf:
        angs.append(t)
        t = t + 2 * ((PI / q).cos() / rho).asin()
    X = [[rho * a.cos(), rho * a.sin(), -z] for a in angs]
    v = [arb(0), arb(0), h - z]
    k = len(conf)
    faces = [(conf[i], (i, (i + 1) % k)) for i in range(k)]
    return (R, v, X, faces)

def prism_star(cell):
    """Prism over uniform polyhedron `cell` (also antiprism prisms: cell = 'oct' or 'A<n>')."""
    Rq, v, X, faces = polyhedron_star(cell)
    half = arb(1) / 2
    v0 = v + [half]
    nbrs = [x + [half] for x in X] + [v + [-half]]
    k = len(X)
    cells = [(cell, tuple(range(k)))]
    for q, (i, j) in faces:
        cells.append((prism_name(q), (i, j, k)))
    return dict(R=(Rq * Rq + half * half).sqrt(), v0=v0, nbrs=nbrs, cells=cells)

def duoprism_star(p, q):
    rp, rq = (1 / (2 * (PI / p).sin()), 1 / (2 * (PI / q).sin()))
    z = arb(0)
    v0 = [rp, z, rq, z]
    ap, aq = (2 * PI / p, 2 * PI / q)
    nbrs = [[rp * ap.cos(), rp * ap.sin(), rq, z], [rp * ap.cos(), -rp * ap.sin(), rq, z], [rp, z, rq * aq.cos(), rq * aq.sin()], [rp, z, rq * aq.cos(), -rq * aq.sin()]]
    cells = [(prism_name(p), (0, 2, 1)), (prism_name(p), (0, 3, 1)), (prism_name(q), (2, 0, 3)), (prism_name(q), (2, 1, 3))]
    return dict(R=(rp * rp + rq * rq).sqrt(), v0=v0, nbrs=nbrs, cells=cells)

def q5_star(name):
    import cert_facets4 as cf
    pts = cf.q5_600cell()
    F = np.array([fl(v) for v in pts])
    if name == 'sadi':
        keep = [i for i, v in enumerate(F) if not np.sum(np.abs(v) > 1e-09) in (1, 4)]
    else:
        keep = cf.grand_antiprism_from(F)
    sub = [pts[i] for i in keep]
    Vf = F[keep]
    nbf = [w for w in range(len(Vf)) if abs(np.linalg.norm(Vf[w] - Vf[0]) - 1) < 1e-06]
    nbrs = [sub[w] for w in nbf]
    v0 = sub[0]
    R = sum((x * x for x in v0), arb(0)).sqrt()
    return _finish(R, v0, nbrs, Vf, nbf, {w: i for i, w in enumerate(nbf)})

def star(name):
    if name[:2] in ('A4', 'B4', 'D4', 'F4', 'H4') and name[2:].isdigit():
        return wythoff_star(name[:2], tuple((int(c) for c in name[2:])))
    if name.startswith('pr-'):
        return prism_star(name[3:])
    if name.startswith('antiprism-prism-'):
        n = int(name.split('-')[-1])
        return prism_star('oct' if n == 3 else 'A%d' % n)
    if name.startswith('duoprism-'):
        p, q = map(int, name.split('-')[1:])
        return duoprism_star(p, q)
    if name in ('sadi', 'gap'):
        return q5_star(name)
    raise ValueError(name)

def check_star(S):
    """Sanity: unit edges, all points on the sphere of radius R, cells nonempty."""
    sq = lambda a, b: sum(((x - y) * (x - y) for x, y in zip(a, b)), arb(0))
    for p in S['nbrs']:
        if not sq(p, S['v0']).overlaps(arb(1)):
            raise AssertionError('edge length')
        if not sq(p, [arb(0)] * 4).overlaps(S['R'] * S['R']):
            raise AssertionError('off sphere')
    if not sq(S['v0'], [arb(0)] * 4).overlaps(S['R'] * S['R']):
        raise AssertionError()
    return True
if __name__ == '__main__':
    import json, sys
    pmax = int(sys.argv[1])
    F = json.load(open('cert_facets4_p%d.json' % pmax))
    for f in F:
        S = star(f['name'])
        check_star(S)
        print(f['name'], len(S['nbrs']), sorted((c for c, _ in S['cells'])))
