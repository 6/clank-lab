"""Facet library for the 5-D enumeration: every known convex uniform 4-polytope
(Wythoffians, snub 24-cell, grand antiprism, polyhedral prisms, antiprism prisms
and duoprisms up to PMAX) with circumradius, vertex-figure signature, and its
polygon orbits (p, cellA, cellB, alpha), cells named in the cells3d vocabulary.
usage: facets4d_all.py PMAX [GROUPS]  -> facets4d_pPMAX.json"""
import sys, json, math
import numpy as np
from geom import Polytope, affine_basis
from known4d import known_list, cell_name
from scipy.spatial import ConvexHull


def cells_of(V):
    c, B = affine_basis(V)
    X = (V - c) @ B.T
    H = ConvexHull(X)
    cells = {}
    for eq in H.equations:
        on = tuple(sorted(np.where(np.abs(X @ eq[:-1] + eq[-1]) < 1e-7)[0].tolist()))
        cells[on] = True
    return [frozenset(cc) for cc in cells]


def polygon_orbits(V):
    cells = cells_of(V)
    names = {cc: cell_name(Polytope(V[sorted(cc)])) for cc in cells}
    byv = {}
    for cc in cells:
        for v in cc:
            byv.setdefault(v, []).append(cc)
    orbits = {}
    seen = set()
    for a in cells:
        for v in a:
            for b in byv[v]:
                if b == a or (b, a) in seen:
                    continue
                s = a & b
                if len(s) < 3:
                    continue
                Ps = V[sorted(s)]
                c0, Bs = affine_basis(Ps)
                if Bs.shape[0] != 2:
                    continue
                seen.add((a, b))
                fc = Ps.mean(axis=0)
                dirs = []
                for cc in (a, b):
                    w = V[sorted(cc)].mean(axis=0) - fc
                    for bb in Bs:
                        w = w - np.dot(w, bb) * bb
                    dirs.append(w / np.linalg.norm(w))
                alpha = math.acos(max(-1, min(1, float(np.dot(dirs[0], dirs[1])))))
                na, nb = sorted([names[a], names[b]])
                key = (len(s), na, nb, round(alpha, 9))
                orbits[key] = orbits.get(key, 0) + 1
    return [list(k) + [v] for k, v in sorted(orbits.items())]


if __name__ == '__main__':
    pmax = int(sys.argv[1])
    groups = sys.argv[2].split(',') if len(sys.argv) > 2 else ('A4', 'B4', 'D4', 'F4', 'H4')
    out = []
    for name, V in known_list(pmax, groups):
        V = np.array(V)
        R = float(np.linalg.norm(V[0] - V.mean(axis=0)))
        out.append(dict(name=name, R=R, nV=len(V), orbits=polygon_orbits(V)))
        print(name, len(V), round(R, 6), len(out[-1]['orbits']), file=sys.stderr, flush=True)
    json.dump(out, open('facets4d_p%d.json' % pmax, 'w'))
