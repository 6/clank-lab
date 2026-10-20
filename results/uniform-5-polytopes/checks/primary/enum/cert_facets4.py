"""Certified facet data for the 5-D stage 1 (arb balls).

For every convex uniform 4-polytope type (Wythoffians of A4/B4/D4/F4/H4,
snub 24-cell, grand antiprism, polyhedral prisms, antiprism prisms and
duoprisms up to PMAX): circumradius and its polygon orbits
(p, cellA, cellB, alpha) with alpha the dihedral angle between the two
cells at the polygon.

Combinatorics at the vertex (which neighbours span which polygon and
which cell, and the cell types) is taken from the floating-point
construction; every number is recomputed rigorously:
- Wythoffians: arb coordinates of v0 and its neighbours (cert_wythoff);
- prisms, antiprism prisms, duoprisms: closed forms from the rigorous
  polyhedron data (cert_poly3): alpha = pi/2 at polygons shared with a
  base, a base dihedral angle at prism squares, interior polygon angles
  in duoprisms;
- snub 24-cell and grand antiprism: exact Q(sqrt 5) coordinates of the
  600-cell, evaluated in arb.
"""
import itertools, math, sys, json
from facet_cell_order import LOCAL_CELL_ORDER
import numpy as np
from flint import arb, ctx
import cert_poly3 as cp
import cert_wythoff as cw
from cert_stage1 import cell_configs
from geom import coxeter_matrix, wythoff, affine_basis, Polytope
from known4d import cell_name
from facets4d_all import cells_of
ctx.prec = 200
PI = arb.pi()

def asub(a, b):
    return [x - y for x, y in zip(a, b)]

def adot(a, b):
    return sum((x * y for x, y in zip(a, b)), arb(0))

def gram_schmidt(vs):
    out = []
    for v in vs:
        w = list(v)
        for u in out:
            c = adot(w, u)
            w = [x - c * y for x, y in zip(w, u)]
        nrm = adot(w, w).sqrt()
        out.append([x / nrm for x in w])
    return out

def dihedral(v0, poly_nbrs, cellA_nbrs, cellB_nbrs):
    """Angle between cells A, B at the polygon spanned by v0 and poly_nbrs (arb points)."""
    B = gram_schmidt([asub(p, v0) for p in poly_nbrs[:2]])

    def inward(cell_nbrs):
        k = len(cell_nbrs)
        c = [sum((p[i] for p in cell_nbrs), arb(0)) / k for i in range(len(v0))]
        w = asub(c, v0)
        for u in B:
            cc = adot(w, u)
            w = [x - cc * y for x, y in zip(w, u)]
        n = adot(w, w).sqrt()
        return [x / n for x in w]
    a, b = (inward(cellA_nbrs), inward(cellB_nbrs))
    return adot(a, b).acos()

def float_local(Vf, name):
    """Combinatorics at vertex 0 from a float vertex array: neighbours, polygons and cells at v0
    (as neighbour index sets) with cell types."""
    nb = [w for w in range(len(Vf)) if abs(np.linalg.norm(Vf[w] - Vf[0]) - 1) < 1e-06]
    cells = [cc for cc in cells_of(Vf) if 0 in cc]
    order = LOCAL_CELL_ORDER[name]
    expected = [frozenset(cc) for cc in order]
    if len(cells) != len(expected) or set(cells) != set(expected):
        raise ArithmeticError('local facet incidence changed: ' + name)
    cells = expected
    cinfo = []
    for cc in cells:
        cinfo.append((cell_name(Polytope(Vf[sorted(cc)])), frozenset((w for w in nb if w in cc)), cc))
    polys = []
    for (na, sa, ca), (nb_, sb, cb) in itertools.combinations(cinfo, 2):
        s = ca & cb
        if len(s) >= 3 and Polytope(Vf[sorted(s)]).dim == 2:
            polys.append((len(s), frozenset((w for w in nb if w in s)), na, sa, nb_, sb))
    return (nb, polys)

def wythoff_data(group, rings):
    Vf = wythoff([group], rings)
    nb, polys = float_local(Vf, group + ''.join(map(str, rings)))
    v0a, nba, R = cw.local_data([coxeter_matrix(group).tolist()], rings)
    amap = {}
    for w in nb:
        best = min(range(len(nba)), key=lambda j: sum(((float(x.mid()) - y) ** 2 for x, y in zip(nba[j], Vf[w]))))
        d = math.sqrt(sum(((float(x.mid()) - y) ** 2 for x, y in zip(nba[best], Vf[w]))))
        if not d < 1e-06:
            raise AssertionError((group, rings, d))
        amap[w] = nba[best]
    if not np.linalg.norm(Vf[0] - np.array([float(x.mid()) for x in v0a])) < 1e-06:
        raise AssertionError()
    orbits = []
    for p, ps, na, sa, nb_, sb in polys:
        al = dihedral(v0a, [amap[w] for w in sorted(ps)], [amap[w] for w in sa], [amap[w] for w in sb])
        a, b = sorted([na, nb_])
        orbits.append((p, a, b, al))
    return (R, merge(orbits))

def merge(orbits):
    out = []
    for p, a, b, al in orbits:
        if not any((o[0] == p and o[1] == a and (o[2] == b) and o[3].overlaps(al) for o in out)):
            out.append((p, a, b, al))
    return out
POLY_CONF = cell_configs(128)

def prism_data(cell):
    """Prism over uniform polyhedron `cell`: R and polygon orbits, closed form."""
    d = cp.data(POLY_CONF[cell])
    R = (d['R'] ** 2 + arb(1) / 4).sqrt()
    orbits = []
    half = PI / 2
    for q in sorted(set(POLY_CONF[cell])):
        orbits.append((q, *sorted([cell, prism_name(q)]), half))
    for qa, qb, al in d['edges']:
        orbits.append((4, *sorted([prism_name(qa), prism_name(qb)]), al))
    return (R, merge(orbits))

def prism_name(q):
    return 'cube' if q == 4 else 'P%d' % q

def duoprism_data(p, q):
    rp, rq = (1 / (2 * (PI / p).sin()), 1 / (2 * (PI / q).sin()))
    R = (rp * rp + rq * rq).sqrt()
    orbits = [(p, prism_name(p), prism_name(p), PI * (1 - arb(2) / q)), (q, prism_name(q), prism_name(q), PI * (1 - arb(2) / p)), (4, *sorted([prism_name(p), prism_name(q)]), PI / 2)]
    return (R, merge(orbits))

def q5_600cell():
    """600-cell with unit edges: exact coordinates (as arb) and float copies."""
    phi = (1 + arb(5).sqrt()) / 2
    half = arb(1) / 2
    pts = []
    for i in range(4):
        for s in (1, -1):
            v = [arb(0)] * 4
            v[i] = arb(s)
            pts.append(v)
    for signs in itertools.product((1, -1), repeat=4):
        pts.append([half * s for s in signs])
    base = [phi / 2, half, 1 / (2 * phi), arb(0)]
    evens = [p for p in itertools.permutations(range(4)) if sum((1 for i in range(4) for j in range(i + 1, 4) if p[i] > p[j])) % 2 == 0]
    for perm in evens:
        for signs in itertools.product((1, -1), repeat=3):
            v = [arb(0)] * 4
            sv = list(signs) + [1]
            for k in range(4):
                v[perm[k]] = base[k] * sv[k]
            pts.append(v)
    uniq = {}
    for v in pts:
        uniq[tuple((round(float(x.mid()), 9) for x in v))] = v
    pts = list(uniq.values())
    if not len(pts) == 120:
        raise AssertionError()
    pts = [[x * phi for x in v] for v in pts]
    return pts

def q5_data(name):
    pts = q5_600cell()
    F = np.array([[float(x.mid()) for x in v] for v in pts])
    if name == 'sadi':
        keep = [i for i, v in enumerate(F) if not np.sum(np.abs(v) > 1e-09) in (1, 4)]
    else:
        from known4d import grand_antiprism
        G = grand_antiprism_from(F)
        keep = G
    sub = [pts[i] for i in keep]
    Fs = F[keep]
    nb, polys = float_local(Fs, name)
    v0 = sub[0]
    orbits = []
    for p, ps, na, sa, nb_, sb in polys:
        al = dihedral(v0, [sub[w] for w in sorted(ps)], [sub[w] for w in sa], [sub[w] for w in sb])
        a, b = sorted([na, nb_])
        orbits.append((p, a, b, al))
    R = adot(v0, v0).sqrt()
    return (R, merge(orbits))

def grand_antiprism_from(F):
    n = len(F)
    Un = F / np.linalg.norm(F[0])
    planes = []
    seen = set()
    for i in range(n):
        for j in range(i + 1, n):
            if abs(np.dot(Un[i], Un[j]) - math.cos(math.pi / 5)) < 1e-09:
                a = Un[i]
                b = Un[j] - np.dot(Un[j], a) * a
                b /= np.linalg.norm(b)
                inplane = tuple((k for k in range(n) if np.linalg.norm(Un[k] - np.dot(Un[k], a) * a - np.dot(Un[k], b) * b) < 1e-09))
                if len(inplane) == 10 and inplane not in seen:
                    seen.add(inplane)
                    planes.append((inplane, a, b))
    for (k1, a1, b1), (k2, a2, b2) in itertools.combinations(planes, 2):
        if max((abs(np.dot(x, y)) for x in (a1, b1) for y in (a2, b2))) < 1e-09:
            return [k for k in range(n) if k not in k1 and k not in k2]
    raise RuntimeError

def antiprism_prism_data(n):
    name = 'oct' if n == 3 else 'A%d' % n
    return prism_data(name)

def merge_congruent(out, pmax, groups):
    """Keep one name per congruence class of facet (the first generated).  The same polytope
    arises under several names (A4 diagram reversal, B4/D4/F4 coincidences, tesseract =
    duoprism-4-4 = prism over cube, octahedral prism = antiprism-prism-3, ...); keeping all of
    them multiplies the vertex-figure search by every mix of names.  Two names are merged when
    their vertex counts, circumradii, polygon-orbit data (p, cells, angle) and vertex stars
    (sorted distances among a vertex and its neighbours) agree."""
    from known4d import known_list
    V = dict(known_list(pmax, groups))

    def key(name, R, orbs):
        X = np.array(V[name], dtype=float)
        nb = [w for w in range(len(X)) if abs(np.linalg.norm(X[w] - X[0]) - 1) < 1e-06]
        S = X[[0] + nb]
        dist = sorted((round(float(np.linalg.norm(a - b)), 8) for a, b in itertools.combinations(S, 2)))
        orb = sorted(((p, tuple(sorted((a, b))), round(float(al.mid()), 9)) for p, a, b, al in orbs))
        return (len(X), round(float(R.mid()), 9), tuple(orb), tuple(dist))
    canon, aliases, keep = ({}, {}, [])
    for n, R, orbs in out:
        k = key(n, R, orbs)
        if k in canon:
            aliases.setdefault(canon[k], []).append(n)
        else:
            canon[k] = n
            keep.append((n, R, orbs))
    return (keep, aliases)
if __name__ == '__main__':
    pmax = int(sys.argv[1])
    groups = sys.argv[2].split(',') if len(sys.argv) > 2 else ['A4', 'B4', 'D4', 'F4', 'H4']
    out = []
    for g in groups:
        for rings in itertools.product([0, 1], repeat=4):
            if any(rings):
                R, orbs = wythoff_data(g, rings)
                out.append(('%s%s' % (g, ''.join(map(str, rings))), R, orbs))
                print(out[-1][0], R.str(12), len(orbs), file=sys.stderr, flush=True)
    for cell in POLY_CONF:
        if cell[0] in 'PA':
            continue
        R, orbs = prism_data(cell)
        out.append(('pr-' + cell, R, orbs))
    if 'H4' in groups:
        for nm in ('sadi', 'gap'):
            R, orbs = q5_data(nm)
            out.append((nm, R, orbs))
    for n in range(3, pmax + 1):
        R, orbs = antiprism_prism_data(n)
        out.append(('antiprism-prism-%d' % n, R, orbs))
        for m in range(n, pmax + 1):
            R, orbs = duoprism_data(n, m)
            out.append(('duoprism-%d-%d' % (n, m), R, orbs))
    out, aliases = merge_congruent(out, pmax, groups)
    print(len(out), 'facet types after merging congruent names;', sum((len(v) for v in aliases.values())), 'aliases', file=sys.stderr, flush=True)
    ser = [dict(name=n, aliases=aliases.get(n, []), R=[R.mid().str(40), R.rad().str(5)], orbits=[[p, a, b, al.mid().str(40), al.rad().str(5)] for p, a, b, al in orbs]) for n, R, orbs in out]
    json.dump(ser, open('cert_facets4_p%d.json' % pmax, 'w'), indent=0)
