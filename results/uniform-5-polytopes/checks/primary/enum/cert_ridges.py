"""Certified ridge lists of the facet models (referee-g2g3, GAP-A5; STAGE3_EXACT.md).

A facet model K (cert_vf.Model) carries its vertex figure X_K (the neighbours of K[0], arb 3-vectors)
and a ridge list: which point sets of X_K are 2-faces (vertex figures of the cells of K at K[0]), their
cyclic order and their cell labels.  cert_star reads that list from a float construction.  Here it is
certified on X_K itself, ridge by ridge:

1. Face.  The plane through three consecutive points of the ridge (exact plane through exact points,
   enclosed in balls) has every other point of X_K certified strictly on one side.  The ridge's other
   points lie on that plane exactly: by exact arithmetic in Q, Q(sqrt 2) or Q(sqrt 5) (Wythoffians:
   the neighbours of v0 recomputed exactly in the coordinates y_i = <x, alpha_i>; snub 24-cell and
   grand antiprism: the exact 600-cell), or by construction (the polyhedron ridge of a prism: its
   points have 4th coordinate exactly 1/2, as v0 has, so they lie on the circle cut from the 3-flat
   x_4 = 1/2 by the unit sphere about v0 and the circumsphere).  So the ridge is exactly the vertex
   set of a 2-face of conv X_K.
2. Cyclic order.  For each consecutive pair (a, b), every other point of the ridge is certified
   strictly on the same side of the line ab inside the ridge plane.  So consecutive pairs are the
   sides of the ridge polygon: the cyclic order is the polygon's, and every side is an edge of X_K.
3. Closure.  Every edge (side) lies in exactly two listed ridges.  The listed ridges are 2-faces of
   the 3-polytope conv X_K; crossing any side of a listed ridge leads to a listed ridge, and the
   face graph of a 3-polytope is connected, so the list contains every 2-face.
4. Label.  A side ab of the ridge of cell C is the vertex figure of a polygon {q} of K at K[0], and
   |a - b| = 2 cos(pi/q).  q is pinned by 4cos^2(pi/(q-1)) < |a-b|^2 < 4cos^2(pi/(q+1)) (certified;
   4cos^2(pi/q) increases with q).  The sequence of q around the ridge is C's vertex configuration,
   which determines the convex uniform polyhedron C; it must match exactly one entry of
   cert_stage1.cell_configs (up to rotation and reflection), and that entry is the label.

certify(model) returns the ridge list built from these facts; cert_vf.Model keeps its list only if it
is equal (labels and cyclic orders), so stage 2 and cert_qfollow's walk use certified lists only.

usage: cert_ridges.py PMAX            all library types of cert_facets4_pPMAX.json, one JSON line each
       cert_ridges.py --summary OUT.jsonl
       cert_ridges.py --corrupt KIND  a deliberately wrong ridge list must be rejected
"""
import itertools, json, sys, time
from fractions import Fraction as Fr
from flint import arb, ctx
import cert_star as cs
import cert_wythoff as cw
ctx.prec = 200
QUARTER = arb(1) / 4

class RidgeError(Exception):
    pass

class QF:
    """a + b sqrt(d) with rational a, b (d = 2 or 5, or any d when b = 0)."""
    __slots__ = ('a', 'b', 'd')

    def __init__(self, a, b=0, d=1):
        self.a, self.b, self.d = (Fr(a), Fr(b), d)

    def _c(self, o):
        if isinstance(o, QF):
            if o.b and self.b and (o.d != self.d):
                raise ValueError('mixed fields')
            return o
        return QF(o, 0, self.d)

    def _dd(self, o):
        return self.d if self.b else o.d

    def __add__(self, o):
        o = self._c(o)
        return QF(self.a + o.a, self.b + o.b, self._dd(o))
    __radd__ = __add__

    def __neg__(self):
        return QF(-self.a, -self.b, self.d)

    def __sub__(self, o):
        return self + -self._c(o)

    def __mul__(self, o):
        o = self._c(o)
        d = self._dd(o)
        return QF(self.a * o.a + d * self.b * o.b, self.a * o.b + self.b * o.a, d)
    __rmul__ = __mul__

    def inv(self):
        n = self.a * self.a - self.d * self.b * self.b
        if n == 0:
            raise ZeroDivisionError
        return QF(self.a / n, -self.b / n, self.d)

    def is_zero(self):
        return self.a == 0 and self.b == 0

    def key(self):
        return (self.a, self.b)

    def to_arb(self):
        x = arb(self.a.numerator) / self.a.denominator
        if self.b:
            x += arb(self.b.numerator) / self.b.denominator * arb(self.d).sqrt()
        return x

def two_cos(m, d):
    """2 cos(pi/m) exactly, for the Coxeter labels of A4/B4/D4/F4/H4."""
    if m == 2:
        return QF(0, 0, d)
    if m == 3:
        return QF(1, 0, d)
    if m == 4:
        if not d == 2:
            raise AssertionError()
        return QF(0, 1, 2)
    if m == 5:
        if not d == 5:
            raise AssertionError()
        return QF(Fr(1, 2), Fr(1, 2), 5)
    raise ValueError(m)

def rank(rows):
    """Exact rank of a list of QF vectors (Gaussian elimination)."""
    M = [list(r) for r in rows]
    rk, ncol = (0, len(M[0]) if M else 0)
    for c in range(ncol):
        piv = next((r for r in range(rk, len(M)) if not M[r][c].is_zero()), None)
        if piv is None:
            continue
        M[rk], M[piv] = (M[piv], M[rk])
        iv = M[rk][c].inv()
        for r in range(len(M)):
            if r != rk and (not M[r][c].is_zero()):
                f = M[r][c] * iv
                M[r] = [x - f * y for x, y in zip(M[r], M[rk])]
        rk += 1
    return rk

def wythoff_exact(name, S):
    """Exact neighbours of v0 in the coordinates y_i = <x, alpha_i> (alpha_i the unit mirror normals of
    cert_wythoff), index-aligned with S['nbrs'] (matched by the separation lemma in K)."""
    from geom import coxeter_matrix
    group, rings = (name[:2], tuple((int(c) for c in name[2:])))
    m = coxeter_matrix(group).tolist()
    n = len(m)
    d = 5 if any((5 in r for r in m)) else 2 if any((4 in r for r in m)) else 1
    tc = [[two_cos(m[i][j], d) if i != j else None for j in range(n)] for i in range(n)]

    def refl(y, j):
        return tuple((-y[i] if i == j else y[i] + tc[j][i] * y[j] for i in range(n)))
    v0 = tuple((QF(Fr(1, 2) if r else 0, 0, d) for r in rings))
    key = lambda y: tuple((c.key() for c in y))
    seeds = [refl(v0, i) for i in range(n) if rings[i]]
    seen = {key(s): s for s in seeds}
    fr = list(seeds)
    while fr:
        nf = []
        for y in fr:
            for j in range(n):
                if not rings[j]:
                    w = refl(y, j)
                    if key(w) not in seen:
                        seen[key(w)] = w
                        nf.append(w)
        fr = nf
    N = cw.block_normals([m])
    ex = list(seen.values())
    xs = [cw.solve(N, [c.to_arb() for c in y]) for y in ex]
    return match(S['nbrs'], ex, xs)

def q5_exact(S):
    """Exact 600-cell (unit edges) in Q(sqrt 5), as cert_facets4.q5_600cell; matched to S['nbrs']."""
    phi = QF(Fr(1, 2), Fr(1, 2), 5)
    half = QF(Fr(1, 2), 0, 5)
    z = QF(0, 0, 5)
    pts = []
    for i in range(4):
        for s in (1, -1):
            v = [z] * 4
            v[i] = QF(s, 0, 5)
            pts.append(v)
    for signs in itertools.product((1, -1), repeat=4):
        pts.append([half * s for s in signs])
    base = [phi * Fr(1, 2), half, phi.inv() * Fr(1, 2), z]
    evens = [p for p in itertools.permutations(range(4)) if sum((1 for i in range(4) for j in range(i + 1, 4) if p[i] > p[j])) % 2 == 0]
    for perm in evens:
        for signs in itertools.product((1, -1), repeat=3):
            v = [z] * 4
            sv = list(signs) + [1]
            for k in range(4):
                v[perm[k]] = base[k] * sv[k]
            pts.append(v)
    uniq = {}
    for v in pts:
        uniq[tuple((c.key() for c in v))] = [c * phi for c in v]
    ex = list(uniq.values())
    if not len(ex) == 120:
        raise AssertionError()
    return match(S['nbrs'], ex, [[c.to_arb() for c in v] for v in ex])

def match(nbrs, ex, xs):
    """ex[j] exact (any linear coordinates), xs[j] its enclosure in the model frame.  Both nbrs[i] and
    xs[j] enclose vertices of one exact polytope (unit edges), so squared distance < 1/4 means equal."""
    out = []
    for p in nbrs:
        hit = [j for j, x in enumerate(xs) if sum(((a - b) * (a - b) for a, b in zip(p, x)), arb(0)) < QUARTER]
        if len(hit) != 1:
            raise RidgeError('exact point match: %d hits' % len(hit))
        if not all((sum(((a - b) * (a - b) for a, b in zip(p, xs[j])), arb(0)) > QUARTER for j in range(len(xs)) if j != hit[0])):
            raise RidgeError('exact point match undecided')
        out.append(ex[hit[0]])
    if len(set((id(e) for e in out))) != len(out):
        raise RidgeError('exact point match not injective')
    return out

def exact_points(name, S):
    if name[:2] in ('A4', 'B4', 'D4', 'F4', 'H4') and name[2:].isdigit():
        return wythoff_exact(name, S)
    if name in ('sadi', 'gap'):
        return q5_exact(S)
    return None

def coplanar_by_construction(name, S, idx):
    """Prism over a polyhedron: the polyhedron ridge's points and v0 have 4th coordinate exactly 1/2
    (a radius-0 ball), so the points lie on the circle cut from the 3-flat x_4 = 1/2 by the unit
    sphere about v0 and the circumsphere (distinct centres v0 and (0, 0, 0, 1/2))."""
    if not (name.startswith('pr-') or name.startswith('antiprism-prism-')):
        return False
    pts = [S['nbrs'][i] for i in idx] + [S['v0']]
    if not all((p[3].rad() == 0 and p[3].mid() == arb(1) / 2 for p in pts)):
        return False
    return sum((x * x for x in S['v0'][:3]), arb(0)) > 0

def cross(u, v):
    return [u[1] * v[2] - u[2] * v[1], u[2] * v[0] - u[0] * v[2], u[0] * v[1] - u[1] * v[0]]

def dot(a, b):
    return sum((x * y for x, y in zip(a, b)), arb(0))

def sub(a, b):
    return [x - y for x, y in zip(a, b)]

def canon_conf(seq):
    k = len(seq)
    rots = [tuple((seq[(s + t) % k] for t in range(k))) for s in range(k)]
    return min(rots + [tuple(reversed(r)) for r in rots])
CONF_NAME = {}
for _nm, _cf in cs.CONF.items():
    CONF_NAME.setdefault(canon_conf(_cf), []).append(_nm)
if not all((len(v) == 1 for v in CONF_NAME.values())):
    raise AssertionError('two cells with one vertex configuration')

def chord_q(c2, qmax=200):
    """The q with |a-b|^2 = 4cos^2(pi/q), certified: 4cos^2(pi/(q-1)) < c2 < 4cos^2(pi/(q+1))."""
    import math
    f = float(c2.mid())
    if not 0 < f < 4:
        raise RidgeError('chord out of range')
    q = round(math.pi / math.acos(math.sqrt(f) / 2))
    four_cos2 = lambda p: 4 * (arb.pi() / p).cos() ** 2
    if not (3 <= q <= qmax and c2 > four_cos2(q - 1) and (c2 < four_cos2(q + 1)) and c2.overlaps(four_cos2(q))):
        raise RidgeError('chord not pinned to one polygon')
    return q

def certify(model, ridges=None, S=None):
    """Certify the ridge list `ridges` (default: the model's) on the model's exact VF.  Returns
    (certified list [(label from chords, cyclic tuple)], stats); raises RidgeError on any failure."""
    name, X = (model.name, model.X)
    S = cs.star(name) if S is None else S
    ridges = list(model.ridges if ridges is None else ridges)
    k = len(X)
    ex = None
    stats = dict(name=name, points=k, ridges=len(ridges), exact_coplanar=0, by_construction=0, triangles=0)
    out, sides = ([], {})
    margin = None
    for lab, cyc in ridges:
        cyc = tuple(cyc)
        m = len(cyc)
        if m < 3 or len(set(cyc)) != m:
            raise RidgeError('%s: degenerate ridge %s' % (name, cyc))
        P = [X[i] for i in cyc]
        nrm = cross(sub(P[1], P[0]), sub(P[2], P[0]))
        if not dot(nrm, nrm) > 0:
            raise RidgeError('%s: ridge plane undecided' % name)
        h = dot(nrm, P[0])
        vals = [dot(nrm, X[j]) - h for j in range(k) if j not in cyc]
        if all((v < 0 for v in vals)):
            sg = 1
        elif all((v > 0 for v in vals)):
            sg = -1
        else:
            raise RidgeError('%s: ridge %s %s is not certified a face' % (name, lab, cyc))
        nn = dot(nrm, nrm).sqrt()
        mg = min((float((-sg * v / nn).lower()) for v in vals))
        margin = mg if margin is None else min(margin, mg)
        if m == 3:
            stats['triangles'] += 1
        elif coplanar_by_construction(name, S, cyc):
            stats['by_construction'] += 1
        else:
            if ex is None:
                ex = exact_points(name, S)
                if ex is None:
                    raise RidgeError('%s: no exact coordinates for a %d-point ridge' % (name, m))
            if rank([[a - b for a, b in zip(ex[i], ex[cyc[0]])] for i in cyc[1:]]) != 2:
                raise RidgeError('%s: ridge %s %s not exactly coplanar' % (name, lab, cyc))
            stats['exact_coplanar'] += 1
        sgn = None
        for t in range(m):
            a, b = (P[t], P[(t + 1) % m])
            u = cross(nrm, sub(b, a))
            for s in range(m):
                if s in (t, (t + 1) % m):
                    continue
                v = dot(u, sub(P[s], a))
                cur = 1 if v > 0 else -1 if v < 0 else None
                if cur is None or (sgn is not None and cur != sgn):
                    raise RidgeError('%s: ridge %s %s: cyclic order not certified' % (name, lab, cyc))
                sgn = cur
            e = frozenset((cyc[t], cyc[(t + 1) % m]))
            sides[e] = sides.get(e, 0) + 1
        conf = [chord_q(model_d2(X[cyc[t]], X[cyc[(t + 1) % m]])) for t in range(m)]
        cand = CONF_NAME.get(canon_conf(conf))
        if not cand:
            raise RidgeError('%s: ridge %s: vertex configuration %s is no uniform polyhedron' % (name, cyc, conf))
        out.append((cand[0], cyc))
    if len(set((frozenset(c) for _, c in ridges))) != len(ridges):
        raise RidgeError('%s: repeated ridge' % name)
    bad = [sorted(e) for e, n in sides.items() if n != 2]
    if bad:
        raise RidgeError('%s: VF-edges not in exactly two ridges: %s' % (name, bad[:4]))
    if set().union(*[set(c) for _, c in ridges]) != set(range(k)):
        raise RidgeError('%s: VF point in no ridge' % name)
    stats.update(edges=len(sides), min_margin=margin)
    return (out, stats)

def model_d2(a, b):
    d = sub(a, b)
    return dot(d, d)
_DONE = {}

def check_model(model, S=None):
    """The model's ridge list equals the certified one (labels and cyclic orders); returns stats.
    Cached per process by (name, list): the certificate depends on nothing else."""
    key = (model.name, tuple(((lab, tuple(c)) for lab, c in model.ridges)))
    if key not in _DONE:
        t = time.time()
        _DONE[key] = _check(model, S)
        _DONE[key]['cert_seconds'] = round(time.time() - t, 2)
    return _DONE[key]

def _check(model, S):
    cert, stats = certify(model, S=S)
    if cert != [(lab, tuple(c)) for lab, c in model.ridges]:
        diff = [(a, b) for a, b in zip(model.ridges, cert) if (a[0], tuple(a[1])) != b]
        raise RidgeError('%s: ridge labels differ from the certified ones: %s' % (model.name, diff[:3]))
    return stats

def corruptions():
    """Each wrong list must be rejected.  Returns [(kind, rejected?, message)]."""
    import cert_vf as cv
    res = []
    m = cv.Model('B41000')
    rid = list(m.ridges)
    lab, c = rid[0]
    res.append(('wrong-label', [('cube' if lab == 'tet' else 'tet', c)] + rid[1:]))
    res.append(('dropped-ridge', rid[1:]))
    second_model = cv.Model('B40100')
    r2 = list(second_model.ridges)
    lab2, c2 = next(((l, c) for l, c in r2 if len(c) == 4))
    res2 = [('swapped-order', [(lab2, (c2[0], c2[2], c2[1], c2[3]))] + [x for x in r2 if x[1] != c2])]
    sq = [x for x in r2 if len(x[1]) == 4]
    a = sq[0][1]
    split = [(lab2, (a[0], a[1], a[2])), (lab2, (a[0], a[2], a[3]))] + [x for x in r2 if x[1] != a]
    res2.append(('split-ridge', split))
    ex = exact_points('B40100', cs.star('B40100'))
    a = sq[0][1]
    j = next((j for j in range(len(second_model.X)) if j not in a))
    res2.append(('non-coplanar', [(lab2, (a[0], a[1], a[2], j))] + [x for x in r2 if x[1] != a]))
    out = [('exact-rank', rank([[x - y for x, y in zip(ex[i], ex[a[0]])] for i in (a[1], a[2], j)]) == 3, 'rank of three points of a square ridge and a fourth VF point: must be 3')]
    for kind, lst in res:
        out.append((kind,) + _rejects(m, lst))
    for kind, lst in res2:
        out.append((kind,) + _rejects(second_model, lst))
    return out

def _rejects(model, lst):
    try:
        cert, _ = certify(model, lst)
    except RidgeError as e:
        return (True, str(e))
    if cert != [(l, tuple(c)) for l, c in lst]:
        return (True, 'label differs from the certified one')
    return (False, 'accepted')

def summary(paths):
    L = [json.loads(l) for p in paths for l in open(p)]
    ok = [x for x in L if x['status'] == 'certified']
    print('facet types', len(L), 'ridge lists certified', len(ok), 'failed', [(x['name'], x['why']) for x in L if x not in ok])
    tot = lambda k: sum((x[k] for x in ok))
    print('ridges', tot('ridges'), ': triangles', tot('triangles'), ', exactly coplanar (exact arithmetic)', tot('exact_coplanar'), ', coplanar by construction (prisms)', tot('by_construction'), '; VF-edges', tot('edges'), '(each in exactly two ridges)')
    print('min distance of a VF point outside a ridge from its plane: %.3f' % min((x['min_margin'] for x in ok)))

def main(argv):
    import cert_vf as cv
    if argv[0] == '--summary':
        summary(argv[1:])
        return
    if argv[0] == '--corrupt':
        bad = 0
        for kind, rej, msg in corruptions():
            print(kind, 'rejected' if rej else 'ACCEPTED', '::', msg)
            bad += not rej
        sys.exit(1 if bad else 0)
    pmax = int(argv[0])
    F = json.load(open('cert_facets4_p%d.json' % pmax))
    for f in F:
        t = time.time()
        try:
            st = dict(cv.Model(f['name']).ridge_stats, status='certified')
        except RidgeError as e:
            st = dict(name=f['name'], status='failed', why=str(e))
        st['seconds'] = round(time.time() - t, 2)
        print(json.dumps(st), flush=True)
if __name__ == '__main__':
    main(sys.argv[1:])
