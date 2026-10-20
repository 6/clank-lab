"""Local authoritative constructions, without a full floating-point hull.

All proposals are checked by cert_ridges before being used. Construction
uniformity is the explicit R2 hypothesis, not a conclusion of this module.
"""
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
from types import SimpleNamespace
import itertools
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'enum'))
import numpy as np
from scipy.spatial import ConvexHull
from flint import arb, ctx
import cert_star as cs
import cert_ridges as cr
import cert_wythoff as cw
import cert_poly3 as cp
import cert_facets4 as cf
from geom import coxeter_matrix

ctx.prec = 200


def exact_wythoff_star(name):
    """Unringed parabolic orbit, with rational Q(sqrt d) keys, not rounding.

    Coordinates y_i=<x,alpha_i>. A seed has y_i=ring_i/2.
    The unit neighbours are the unringed orbit of ringed reflections.
    This is the standard local Wythoff theorem used by cert_wythoff.
    """
    m = coxeter_matrix(name[:2]).tolist()
    rings = tuple(map(int, name[2:]))
    d = 5 if any(5 in r for r in m) else 2 if any(4 in r for r in m) else 1
    tc = [[cr.two_cos(m[i][j], d) if i != j else None for j in range(4)] for i in range(4)]
    def refl(y, j):
        return tuple(-y[i] if i == j else y[i] + tc[j][i] * y[j] for i in range(4))
    v = tuple(cr.QF(Fraction(r, 2), 0, d) for r in rings)
    key = lambda y: tuple(c.key() for c in y)
    seen = {}
    for j in range(4):
        if rings[j]:
            y = refl(v, j)
            seen[key(y)] = y
    todo = list(seen.values())
    for y in todo:
        for j in range(4):
            if not rings[j]:
                w = refl(y, j)
                if key(w) not in seen:
                    seen[key(w)] = w
                    todo.append(w)
    N = cw.block_normals([m])
    v0 = cw.solve(N, [c.to_arb() for c in v])
    nbrs = [cw.solve(N, [c.to_arb() for c in y]) for y in seen.values()]
    return dict(v0=v0, nbrs=nbrs, R=cw.dot(v0, v0).sqrt())


def frame(S):
    c = [(1 - 1 / (2 * S['R'] ** 2)) * x for x in S['v0']]
    Y = [cf.asub(p, c) for p in S['nbrs']]
    # A numerical choice only proposes a frame. Interval Gram-Schmidt must
    # certify its rank; failure aborts rather than discarding a candidate.
    for tr in itertools.combinations(Y, 3):
        E = cf.gram_schmidt(tr)
        if all(x.is_finite() for row in E for x in row):
            return [[cf.adot(y, e) for e in E] for y in Y]
    raise ArithmeticError('no certified VF frame')


def exact_q5_star(name):
    """Exact subset and complete distance-one list in Q(sqrt 5).

    Snub 24-cell: delete the coordinate 24-cell. Grand antiprism: delete
    the decagon in an edge plane and the decagon in its orthogonal plane.
    Uniformity of these convex hulls remains R2; no float subset or
    approximate distance-one test defines their vertices here.
    """
    q = lambda a, b=0: cr.QF(a, b, 5)
    phi, half, zero = q(Fraction(1, 2), Fraction(1, 2)), q(Fraction(1, 2)), q(0)
    V = []
    for i in range(4):
        for s in (1, -1):
            v = [zero] * 4
            v[i] = q(s)
            V.append(v)
    for signs in itertools.product((1, -1), repeat=4):
        V.append([half * s for s in signs])
    base = [phi * Fraction(1, 2), half, phi.inv() * Fraction(1, 2), zero]
    for perm in itertools.permutations(range(4)):
        if sum(perm[i] > perm[j] for i in range(4) for j in range(i + 1, 4)) % 2:
            continue
        for signs in itertools.product((1, -1), repeat=3):
            v = [zero] * 4
            for k in range(4):
                v[perm[k]] = base[k] * (signs[k] if k < 3 else 1)
            V.append(v)
    V = [[c * phi for c in v] for v in V]
    key = lambda v: tuple(c.key() for c in v)
    if len(V) != 120 or len({key(v) for v in V}) != 120:
        raise ArithmeticError('600-cell coordinate identities')
    dot = lambda a, b: sum((x * y for x, y in zip(a, b)), q(0))
    sub = lambda a, b: [x - y for x, y in zip(a, b)]
    if name == 'sadi':
        E = V[24:]
    else:
        a = V[0]
        b = next(v for v in V if (dot(sub(a, v), sub(a, v)) - 1).is_zero())
        plane, orth, E = [], [], []
        for v in V:
            if cr.rank([a, b, v]) == 2:
                plane.append(v)
            elif dot(a, v).is_zero() and dot(b, v).is_zero():
                orth.append(v)
            else:
                E.append(v)
        if len(plane) != 10 or len(orth) != 10 or len(E) != 100:
            raise ArithmeticError('orthogonal decagon deletion')
    base = E[0]
    radius2 = dot(base, base)
    nbrs = []
    for v in E:
        if not (dot(v, v) - radius2).is_zero():
            raise ArithmeticError('noncospherical subset')
        d2 = dot(sub(base, v), sub(base, v))
        if (d2 - 1).is_zero():
            nbrs.append(v)
        elif not d2.is_zero() and not d2.to_arb() > 1:
            raise ArithmeticError('subunit or undecided non-neighbour')
    asarb = lambda v: [c.to_arb() for c in v]
    return dict(v0=asarb(base), nbrs=[asarb(v) for v in nbrs], R=radius2.to_arb().sqrt())


def propose_cells(X):
    F = np.array([[float(x.mid()) for x in p] for p in X])
    H = ConvexHull(F)
    faces = set()
    for eq in H.equations:
        faces.add(tuple(int(i) for i in np.where(np.abs(F @ eq[:3] + eq[3]) < 1e-7)[0]))
    out = []
    for face in sorted(faces):
        cyc = cs.cyclic(None, F, list(face))
        conf = [cr.chord_q(cr.model_d2(X[a], X[b])) for a, b in zip(cyc, cyc[1:] + cyc[:1])]
        labels = cr.CONF_NAME[cr.canon_conf(conf)]
        if len(labels) != 1:
            raise ArithmeticError('ambiguous cell label')
        out.append((labels[0], cyc))
    return out


@lru_cache(None)
def local(name):
    if name[:2] in ('A4', 'B4', 'D4', 'F4', 'H4'):
        S = exact_wythoff_star(name)
    elif name in ('sadi', 'gap'):
        S = exact_q5_star(name)
    else:
        S = cs.star(name)
    X = frame(S)
    ridges = propose_cells(X) if 'cells' not in S else S['cells']
    return S, SimpleNamespace(name=name, X=X, ridges=ridges)


@lru_cache(None)
def cell_radius(label):
    return cp.data(cs.CONF[label])['R']


def angle(R, p, a, b):
    """Exact geometric formula under R2; all numerical values are Arb balls."""
    rho2 = (1 / (2 * (arb.pi() / p).sin())) ** 2
    den = R ** 2 - rho2
    if not den > 0:
        raise ArithmeticError('polygon radius not below facet radius')
    out = arb(0)
    for lab in (a, b):
        d2 = cell_radius(lab) ** 2 - rho2
        h2 = R ** 2 - cell_radius(lab) ** 2
        if not (d2 > 0 and h2 > 0):
            raise ArithmeticError('cell/polygon radius nesting undecided')
        out += (d2 / den).sqrt().acos()
    if not (out > 0 and out < arb.pi()):
        raise ArithmeticError('dihedral not strictly convex')
    return out


def serialize(x):
    return [x.mid().str(40), x.rad().str(5)]


def read_ball(pair):
    # Use exactly the S1 consumer, then check containment of every exported
    # value. No rounded serialization is silently treated as an enclosure.
    # Importing S1 sets global Arb precision to 160. Reproduce its parser
    # at that precision, then restore the construction's 200-bit context.
    saved = ctx.prec
    try:
        from cert_stage1_5d import ball
        ctx.prec = 160
        return ball(*pair)
    finally:
        ctx.prec = saved
