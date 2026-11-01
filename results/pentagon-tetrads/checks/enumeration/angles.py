"""Angle screen: for every labelled placement, decide whether the prototile's
angles can satisfy the linear angle conditions (numerical screen; exact
certificates are produced separately for the record).

Conditions on the prototile angles a_0..a_{n-1} (degrees):
  sum a_i = (n-2)*180, 0 < a_i < 360, a_i != 180;
  interior map vertex: sum of its tile sector angles = 360
      (a corner contributes a_label, a straight sector 180);
  boundary map vertex (has a non-tile sector): sum of tile sector angles < 360;
  bend on an edge between two tiles: a_x + a_y = 360.
"""
import itertools
import json
import sys
import time

import numpy as np
from scipy.optimize import linprog

from placements import MapData, placements, corner_sequence, dihedral, label_of


def build_rows(md, cs, bends, labs, n):
    """labs: per tile, a labeling. Returns sorted tuple of rows:
    (kind, coeffs, const) with kind 'E' (= 360) or 'L' (< 360)."""
    lab_at = {}
    for t in range(4):
        seq = corner_sequence(md, cs, bends, t)
        for k, pos in enumerate(seq):
            lab_at[(t, pos)] = label_of(labs[t], k, n)
    rows = []
    for v, secs in enumerate(md.vertex_sectors):
        coef = [0] * n
        const = 0
        for d in secs:
            t = md.tail[d]
            if t >= 4:
                continue
            if cs[d] == 'C':
                coef[lab_at[(t, ('V', d))]] += 1
            else:
                const += 180
        rows.append(('E' if md.vertex_interior[v] else 'L', tuple(coef), const))
    for e, (a, b) in enumerate(md.edges):
        if a < 4 and b < 4:
            for j in range(bends[e]):
                coef = [0] * n
                coef[lab_at[(a, ('B', e, j))]] += 1
                coef[lab_at[(b, ('B', e, j))]] += 1
                rows.append(('E', tuple(coef), 0))
    return tuple(sorted(set(rows)))


def sign_patterns(n):
    """Reflex patterns: tuple of booleans, at most n-3 reflex (sum bound)."""
    out = []
    for r in range(0, n - 2):
        for S in itertools.combinations(range(n), r):
            out.append(tuple(i in S for i in range(n)))
    return out


def lp_feasible(rows, n, pattern):
    """Max margin t; returns (t, alpha)."""
    # variables: a_0..a_{n-1}, t ; maximize t
    nv = n + 1
    A_eq = [[1] * n + [0]]
    b_eq = [(n - 2) * 180]
    A_ub = []
    b_ub = []
    for kind, coef, const in rows:
        if kind == 'E':
            if sum(coef) == 0:
                if const != 360:
                    return -1, None
                continue
            A_eq.append(list(coef) + [0])
            b_eq.append(360 - const)
        else:
            A_ub.append(list(coef) + [1])
            b_ub.append(360 - const)
    for i in range(n):
        r = [0] * nv
        r[i] = -1
        r[n] = 1
        A_ub.append(r)
        b_ub.append(0)  # a_i >= t
        r = [0] * nv
        r[i] = 1
        r[n] = 1
        A_ub.append(r)
        b_ub.append(360)  # a_i <= 360 - t
        r = [0] * nv
        if pattern[i]:
            r[i] = -1
            r[n] = 1
            A_ub.append(r)
            b_ub.append(-180)  # a_i >= 180 + t
        else:
            r[i] = 1
            r[n] = 1
            A_ub.append(r)
            b_ub.append(180)  # a_i <= 180 - t
    c = [0] * n + [-1]
    bounds = [(None, None)] * n + [(None, 1)]
    res = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=bounds, method='highs')
    if res.status != 0:
        return -1, None
    return -res.fun, res.x[:n]


def screen(map_lines, n, out, tol=1e-7):
    cache = {}
    pats = sign_patterns(n)
    nsurv = 0
    nlab = 0
    t0 = time.time()
    labs_all = dihedral(n)
    for mi, line in enumerate(map_lines):
        md = MapData(json.loads(line))
        for pi, (cs, bends) in enumerate(placements(md, n)):
            for l1, l2, l3 in itertools.product(labs_all, repeat=3):
                labs = [(True, 0), l1, l2, l3]
                rows = build_rows(md, cs, bends, labs, n)
                nlab += 1
                r = cache.get(rows)
                if r is None:
                    r = []
                    for p in pats:
                        tm, x = lp_feasible(rows, n, p)
                        if tm > tol:
                            r.append((p, [round(float(v), 6) for v in x], tm))
                    cache[rows] = r
                if r:
                    nsurv += 1
                    out.write(json.dumps({'map': mi, 'placement': pi, 'cs': {str(k): v for k, v in cs.items()},
                                          'bends': bends, 'labs': labs,
                                          'feasible': [[list(p), x, tm] for p, x, tm in r]}) + '\n')
        print(f'map {mi}: labelled {nlab}, distinct systems {len(cache)}, survivors {nsurv}, {time.time()-t0:.0f}s',
              file=sys.stderr, flush=True)
    return nlab, len(cache), nsurv


if __name__ == '__main__':
    maps_file, n, outf = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    lines = open(maps_file).read().splitlines()
    with open(outf, 'w') as out:
        print(screen(lines, n, out), file=sys.stderr)
