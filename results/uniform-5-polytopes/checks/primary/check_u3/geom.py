"""Vertex sets of the uniform polytopes used by the stage-3 checker, built
from their definitions (Wythoff construction, products, alternation),
as mpmath.iv enclosures, centred at the origin, unit edges.

Distinct vertices of a convex polytope inscribed in a sphere with unit edges
are at distance >= 1, so two computed vertices whose enclosures are closer
than 1/2 are the same vertex: the orbit deduplication below is exact.
"""
import math
from functools import lru_cache
from mpmath import iv
from ivla import ZERO, ONE, HALF, dot, norm2, vsub, vadd, vscale, cholesky, dist2, vmid, solve

def key(v, scale=100000.0):
    return tuple((int(round(float(x.mid) * scale)) for x in v))

class PointSet:
    """Vertex set with exact deduplication (separation lemma)."""

    def __init__(self, dim):
        self.dim = dim
        self.pts = []
        self.grid = {}

    def find(self, v):
        m = vmid(v)
        c = tuple((int(math.floor(x * 4)) for x in m))
        import itertools
        for d in itertools.product((-2, -1, 0, 1, 2), repeat=self.dim):
            cc = tuple((a + b for a, b in zip(c, d)))
            for i in self.grid.get(cc, ()):
                d2 = dist2(self.pts[i], v)
                if d2.b < 0.25:
                    return i
                if d2.a < 0.25:
                    raise ArithmeticError('undecided vertex identity')
        return -1

    def add(self, v):
        i = self.find(v)
        if i >= 0:
            return (i, False)
        m = vmid(v)
        c = tuple((int(math.floor(x * 4)) for x in m))
        self.pts.append(v)
        self.grid.setdefault(c, []).append(len(self.pts) - 1)
        return (len(self.pts) - 1, True)

def coxeter_matrix(n, edges):
    m = [[2] * n for _ in range(n)]
    for i in range(n):
        m[i][i] = 1
    for a, b, k in edges:
        m[a][b] = m[b][a] = k
    return m
DIAGRAMS = {'A3': (3, [(0, 1, 3), (1, 2, 3)]), 'B3': (3, [(0, 1, 3), (1, 2, 4)]), 'H3': (3, [(0, 1, 5), (1, 2, 3)]), 'A4': (4, [(0, 1, 3), (1, 2, 3), (2, 3, 3)]), 'B4': (4, [(0, 1, 3), (1, 2, 3), (2, 3, 4)]), 'D4': (4, [(1, 0, 3), (1, 2, 3), (1, 3, 3)]), 'F4': (4, [(0, 1, 3), (1, 2, 4), (2, 3, 3)]), 'H4': (4, [(0, 1, 5), (1, 2, 3), (2, 3, 3)]), 'A5': (5, [(0, 1, 3), (1, 2, 3), (2, 3, 3), (3, 4, 3)]), 'B5': (5, [(0, 1, 3), (1, 2, 3), (2, 3, 3), (3, 4, 4)]), 'D5': (5, [(0, 1, 3), (1, 2, 3), (2, 3, 3), (2, 4, 3)])}

@lru_cache(None)
def roots(diag):
    n, edges = DIAGRAMS[diag]
    m = coxeter_matrix(n, edges)
    G = [[ONE if i == j else -iv.cos(iv.pi / m[i][j]) for j in range(n)] for i in range(n)]
    return cholesky(G)

def reflect(y, a):
    c = 2 * dot(y, a)
    return [yi - c * ai for yi, ai in zip(y, a)]

def wythoff(diag, rings):
    return wythoff_perm(diag, tuple(rings))[0]

@lru_cache(None)
def wythoff_perm(diag, rings):
    """vertex set of the Wythoff polytope and, for every simple reflection
    r_k, its permutation of the vertices (perms[k][i] = index of r_k(v_i)).
    The vertex set is the orbit of x under the reflection group, so every r_k
    is an exact symmetry; each image is identified by the separation lemma
    (PointSet.find), so the permutations are exact."""
    al = roots(diag)
    n = len(al)
    b = [HALF if r else ZERO for r in rings]
    x = solve(al, [[bi] for bi in b])
    x = [r[0] for r in x]
    ps = PointSet(n)
    ps.add(x)
    img = {}
    frontier = [0]
    while frontier:
        nf = []
        for i in frontier:
            for k, a in enumerate(al):
                y = reflect(ps.pts[i], a)
                j, new = ps.add(y)
                img[k, i] = j
                if new:
                    nf.append(j)
        frontier = nf
    perms = [[img[k, i] for i in range(len(ps.pts))] for k in range(n)]
    return (ps.pts, perms)

def polygon(p, start=0):
    rho = 1 / (2 * iv.sin(iv.pi / p))
    return [[rho * iv.cos(2 * iv.pi * k / p), rho * iv.sin(2 * iv.pi * k / p)] for k in range(p)]

def product(A, B):
    return [a + b for a in A for b in B]
SEG = [[-HALF], [HALF]]

def antiprism(n):
    rho = 1 / (2 * iv.sin(iv.pi / n))
    h2 = 1 - 2 * rho * rho * (1 - iv.cos(iv.pi / n))
    h = iv.sqrt(h2)
    V = []
    for k in range(n):
        V.append([rho * iv.cos(2 * iv.pi * k / n), rho * iv.sin(2 * iv.pi * k / n), h / 2])
        V.append([rho * iv.cos(2 * iv.pi * k / n + iv.pi / n), rho * iv.sin(2 * iv.pi * k / n + iv.pi / n), -h / 2])
    return V

def prism3(n):
    return [p + [s] for p in polygon(n) for s in (-HALF, HALF)]

def _rotmat_from_reflections(al, i, j):
    """matrix of r_i r_j (apply r_j first)"""
    n = len(al)
    cols = []
    for k in range(n):
        e = [ONE if t == k else ZERO for t in range(n)]
        cols.append(reflect(reflect(e, al[j]), al[i]))
    return [[cols[c][r] for c in range(n)] for r in range(n)]

def _matvec(M, v):
    return [dot(r, v) for r in M]

def snub(diag):
    return snub_perm(diag)[0]

@lru_cache(None)
def snub_perm(diag):
    """(vertices, [perm of A, perm of B]).  Snub polyhedron of the rotation group of B3 / H3: the orbit of a point p
    with |p - a p| = |p - b p| = |p - c p| (a = r0 r1, b = r1 r2, c = r0 r2),
    the root certified by a Krawczyk step, then scaled to unit edge."""
    from mpmath import mp, mpf, matrix, lu_solve
    al = roots(diag)
    A = _rotmat_from_reflections(al, 0, 1)
    B = _rotmat_from_reflections(al, 1, 2)
    C = _rotmat_from_reflections(al, 0, 2)

    def Mq(M):
        n = 3
        D = [[(ONE if r == c else ZERO) - M[r][c] for c in range(n)] for r in range(n)]
        return [[sum((D[k][r] * D[k][c] for k in range(n)), ZERO) for c in range(n)] for r in range(n)]
    MA, MB, MC = (Mq(A), Mq(B), Mq(C))
    Q1 = [[MA[r][c] - MB[r][c] for c in range(3)] for r in range(3)]
    Q2 = [[MA[r][c] - MC[r][c] for c in range(3)] for r in range(3)]

    def F(p):
        return [dot(p, _matvec(Q1, p)), dot(p, _matvec(Q2, p)), norm2(p) - 1]

    def J(p):
        return [[2 * x for x in _matvec(Q1, p)], [2 * x for x in _matvec(Q2, p)], [2 * x for x in p]]
    x = solve(al, [[HALF] for _ in range(3)])
    p = [r[0] for r in x]
    nrm = iv.sqrt(norm2(p))
    p = [iv.mpf(float((c / nrm).mid)) for c in p]
    for _ in range(80):
        f = F(p)
        Jm = J(p)
        try:
            d = solve(Jm, [[c] for c in f])
        except ZeroDivisionError:
            break
        p = [iv.mpf(pc.mid) - iv.mpf(dc[0].mid) for pc, dc in zip(p, d)]
    eps = iv.mpf('1e-30')
    X = [iv.mpf([c.mid - eps.b, c.mid + eps.b]) for c in p]
    xm = [iv.mpf(c.mid) for c in p]
    Jm = J(xm)
    Y = [[iv.mpf(e.mid) for e in row] for row in _inv_mid(Jm)]
    fx = F(xm)
    JX = J(X)
    YJ = [[sum((Y[r][k] * JX[k][c] for k in range(3)), ZERO) for c in range(3)] for r in range(3)]
    Kx = []
    for r in range(3):
        s = xm[r] - sum((Y[r][k] * fx[k] for k in range(3)), ZERO)
        for c in range(3):
            s += ((ONE if r == c else ZERO) - YJ[r][c]) * (X[c] - xm[c])
        Kx.append(s)
    for kx, xx in zip(Kx, X):
        if not (kx.a > xx.a and kx.b < xx.b):
            raise ArithmeticError('snub root not certified')
    e = iv.sqrt(dist2(Kx, _matvec(A, Kx)))
    p = [c / e for c in Kx]
    ps = PointSet(3)
    ps.add(p)
    fr = [0]
    gens = [A, B]
    img = {}
    while fr:
        nf = []
        for i in fr:
            for k, G in enumerate(gens):
                j, new = ps.add(_matvec(G, ps.pts[i]))
                img[k, i] = j
                if new:
                    nf.append(j)
        fr = nf
    perms = [[img[k, i] for i in range(len(ps.pts))] for k in range(2)]
    return (ps.pts, perms)

def _inv_mid(M):
    from ivla import inverse
    Mm = [[iv.mpf(e.mid) for e in row] for row in M]
    return inverse(Mm)

@lru_cache(None)
def cell600():
    phi = (1 + iv.sqrt(5)) / 2
    V = []
    import itertools
    for i in range(4):
        for s in (-1, 1):
            v = [ZERO] * 4
            v[i] = iv.mpf(s)
            V.append(v)
    for signs in itertools.product((-1, 1), repeat=4):
        V.append([HALF * s for s in signs])
    base = [phi / 2, HALF, 1 / (2 * phi), ZERO]
    evens = [p for p in itertools.permutations(range(4)) if _parity(p) == 0]
    for p in evens:
        for signs in itertools.product((-1, 1), repeat=3):
            v = [ZERO] * 4
            for k in range(3):
                v[p[k]] = base[k] * signs[k]
            V.append(v)
    if not len(V) == 120:
        raise AssertionError()
    return [[c * phi for c in v] for v in V]

def _parity(p):
    p = list(p)
    s = 0
    for i in range(len(p)):
        for j in range(i + 1, len(p)):
            if p[i] > p[j]:
                s ^= 1
    return s

def sadi():
    V = cell600()
    return V[24:]

def gap():
    V = cell600()
    a = V[0]
    b = next((v for v in V if abs(float(dist2(a, v).mid) - 1) < 1e-09))
    from ivla import gram_schmidt
    u1, u2 = gram_schmidt([a, b])
    keep = []
    ring1 = ring2 = 0
    for v in V:
        p1, p2 = (dot(v, u1), dot(v, u2))
        r2 = norm2(v)
        inplane = abs(float((r2 - p1 * p1 - p2 * p2).mid)) < 1e-20
        orth = abs(float(p1.mid)) < 1e-20 and abs(float(p2.mid)) < 1e-20
        if inplane:
            ring1 += 1
        elif orth:
            ring2 += 1
        else:
            keep.append(v)
    if not (ring1 == 10 and ring2 == 10 and (len(keep) == 100)):
        raise AssertionError((ring1, ring2, len(keep)))
    return keep
POLY3_WYTHOFF = {}

@lru_cache(None)
def polyhedron(label):
    """vertex set of a cell label"""
    tab = poly3_table()
    if label in tab:
        return tab[label]
    if label[0] == 'P':
        return prism3(int(label[1:]))
    if label[0] == 'A':
        return antiprism(int(label[1:]))
    raise KeyError(label)

@lru_cache(None)
def poly3_table():
    """Platonic and Archimedean solids by label (vertex set)."""
    return {lab: V for lab, (V, src) in poly3_sources().items()}

def _disjoint(x, y):
    return x.b < y.a or y.b < x.a

@lru_cache(None)
def poly3_sources():
    """label -> (vertex set, construction).  Every Wythoff construction of
    A3, B3, H3 and the two snubs is a Platonic or Archimedean solid; a
    Wythoff construction gets label L when its circumradius^2 enclosure meets
    the exact value of L (an interval formula) and is certified apart from
    the value of every other label with the same vertex count (so its true
    radius can only be L's).  The snubs are labelled by construction (snub of
    the rotation group of B3 = snic, of H3 = snid); their radii are
    certified apart from the other labels with 24 and 60 vertices.  When two
    constructions give one label the last one is used (as before)."""
    import itertools
    want = dict(_want3())
    out = {}
    snubs = {'snic': ('B3', 24), 'snid': ('H3', 60)}
    for lab, (d, n) in snubs.items():
        V = snub(d)
        if not len(V) == n:
            raise AssertionError()
        want[lab] = (n, norm2(V[0]))
    for d in ('A3', 'B3', 'H3'):
        for rings in itertools.product((0, 1), repeat=3):
            if not any(rings):
                continue
            V = wythoff(d, rings)
            r2 = norm2(V[0])
            meet = [l for l, (k, w) in want.items() if k == len(V) and (not _disjoint(w, r2))]
            if not len(meet) == 1:
                raise AssertionError((d, rings, meet))
            out[meet[0]] = (V, ('wythoff', d, rings))
    for lab, (d, n) in snubs.items():
        V = snub(d)
        others = [l for l, (k, w) in want.items() if k == n and l != lab and (not _disjoint(w, norm2(V[0])))]
        if not not others:
            raise AssertionError((lab, others))
        out[lab] = (V, ('snub', d))
    missing = set(want) - set(out)
    if not not missing:
        raise AssertionError(missing)
    return out

@lru_cache(None)
def label3(diag, rings):
    """label of the Wythoff polyhedron (diag, rings), by the same certified
    elimination as poly3_sources"""
    V = wythoff(diag, tuple(rings))
    r2 = norm2(V[0])
    meet = [l for l, (k, w) in _want3().items() if k == len(V) and (not _disjoint(w, r2))]
    if not len(meet) == 1:
        raise AssertionError((diag, rings, meet))
    return meet[0]

@lru_cache(None)
def _want3():
    s5 = iv.sqrt(5)
    s2 = iv.sqrt(2)
    return {'tet': (4, iv.mpf(6) / 16), 'oct': (6, HALF), 'cube': (8, iv.mpf(3) / 4), 'ico': (12, (5 + s5) / 8), 'doe': (20, 3 * (3 + s5) / 8), 'tut': (12, iv.mpf(22) / 16), 'co': (12, ONE), 'tic': (24, (7 + 4 * s2) / 4), 'toe': (24, iv.mpf(10) / 4), 'sirco': (24, (5 + 2 * s2) / 4), 'girco': (48, (13 + 6 * s2) / 4), 'id': (30, ((1 + s5) / 2) ** 2), 'tid': (60, (58 + 18 * s5) / 16), 'ti': (60, (74 + 30 * s5) / 16), 'srid': (60, (11 + 4 * s5) / 4), 'grid': (120, (31 + 12 * s5) / 4)}

@lru_cache(None)
def polytope4(name):
    if name[:2] in ('A4', 'B4', 'D4', 'F4', 'H4') and len(name) == 6:
        return wythoff(name[:2], tuple((int(c) for c in name[2:])))
    if name.startswith('pr-'):
        return product(polyhedron(name[3:]), SEG)
    if name.startswith('antiprism-prism-'):
        return product(antiprism(int(name.split('-')[-1])), SEG)
    if name.startswith('duoprism-'):
        p, q = name.split('-')[1:]
        return product(polygon(int(p)), polygon(int(q)))
    if name == 'sadi':
        return sadi()
    if name == 'gap':
        return gap()
    raise KeyError(name)

@lru_cache(None)
def polytope5(name):
    if name[:2] in ('A5', 'B5', 'D5') and len(name) == 7:
        return wythoff(name[:2], tuple((int(c) for c in name[2:])))
    if name.startswith('prism-'):
        return product(polytope4(name[6:]), SEG)
    if name.startswith('{'):
        p = int(name[1:name.index('}')])
        X = name[name.index('x') + 1:]
        return product(polygon(p), polyhedron(X))
    raise KeyError(name)

def _fund_point(diag, rings):
    al = roots(diag)
    b = [HALF if r else ZERO for r in rings]
    x = solve(al, [[bi] for bi in b])
    return [r[0] for r in x]

def rho(p):
    return 1 / (2 * iv.sin(iv.pi / p))

def circumradius2_3(label):
    return norm2(polyhedron(label)[0])

def circumradius2_4(name):
    if name[:2] in ('A4', 'B4', 'D4', 'F4', 'H4') and len(name) == 6:
        return norm2(_fund_point(name[:2], tuple((int(c) for c in name[2:]))))
    if name.startswith('pr-'):
        return circumradius2_3(name[3:]) + HALF * HALF
    if name.startswith('antiprism-prism-'):
        return norm2(antiprism(int(name.split('-')[-1]))[0]) + HALF * HALF
    if name.startswith('duoprism-'):
        p, q = name.split('-')[1:]
        return rho(int(p)) ** 2 + rho(int(q)) ** 2
    if name in ('sadi', 'gap'):
        return norm2(cell600()[0])
    raise KeyError(name)

def circumradius2_5(name):
    if name[:2] in ('A5', 'B5', 'D5') and len(name) == 7:
        return norm2(_fund_point(name[:2], tuple((int(c) for c in name[2:]))))
    if name.startswith('prism-'):
        return circumradius2_4(name[6:]) + HALF * HALF
    if name.startswith('{'):
        p = int(name[1:name.index('}')])
        X = name[name.index('x') + 1:]
        return rho(p) ** 2 + circumradius2_3(X)
    raise KeyError(name)
