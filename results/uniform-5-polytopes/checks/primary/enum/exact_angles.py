"""Exact dihedral angles of the 4-D facets at their polygons, and exact proofs that
the angle sums of the stage-1 cycles left ambiguous by the arb computation equal 2*pi.

Why: a polygon neighbourhood of a convex 5-polytope has angle sum < 2*pi (the
link of a 2-face is a convex spherical polygon in an open hemisphere), so a
cycle with sum exactly 2*pi cannot occur.  cert_stage1_5d keeps every cycle
whose arb sum ball contains 2*pi (it cannot decide them numerically); these
are the Euclidean-honeycomb neighbourhoods.  Here each such cycle's sum is
shown to be exactly 2*pi: cos(alpha) is computed exactly for each facet angle,
and exp(i * sum) = 1 is checked in exact algebraic arithmetic (sympy
minimal polynomials); with the arb sum in (pi, 3*pi) this gives sum = 2*pi.

Exact values: cos(alpha)^2 lies in the quadratic field Q(sqrt d) of the
facet's Coxeter group (d = 1, 2 or 5); it is computed in the root basis of
the reflection group (vectors as coefficients, inner product by the Gram
matrix), so no square roots are taken before the final one.
The proof path is now exact_inputs: replayed exact constructions, certified
incident labels and the positive-branch word-radius formula. The older
coordinate/float incidence routines below are diagnostic only, and neither
flat_cycles nor boundary_cycles calls them.
Prisms and duoprisms: closed forms (right angles; polygon angles; polyhedron
edge angles from the rank-3 Wythoff data).  Snub 24-cell, grand antiprism:
exact Q(sqrt 5) coordinates.  Antiprism prisms: exact sympy coordinates.
"""
import itertools, math, sys, json
from fractions import Fraction as Fr
import numpy as np
import sympy as sp

class QD:
    """a + b sqrt(d), a, b rational (d squarefree; d = 1 means b = 0)."""
    __slots__ = ('a', 'b', 'd')

    def __init__(self, a, b=0, d=1):
        self.a, self.b, self.d = (Fr(a), Fr(b), d)
        if d == 1:
            self.a, self.b = (self.a + self.b, Fr(0))

    def _c(self, o):
        return o if isinstance(o, QD) else QD(o, 0, self.d)

    def _dd(self, o):
        if self.d == o.d or o.b == 0:
            return self.d
        if self.b == 0:
            return o.d
        raise ValueError('field mismatch')

    def __add__(self, o):
        o = self._c(o)
        d = self._dd(o)
        return QD(self.a + o.a, self.b + o.b, d)
    __radd__ = __add__

    def __neg__(self):
        return QD(-self.a, -self.b, self.d)

    def __sub__(self, o):
        return self + -self._c(o)

    def __rsub__(self, o):
        return self._c(o) - self

    def __mul__(self, o):
        o = self._c(o)
        d = self._dd(o)
        return QD(self.a * o.a + self.b * o.b * d, self.a * o.b + self.b * o.a, d)
    __rmul__ = __mul__

    def inv(self):
        n = self.a * self.a - self.b * self.b * self.d
        if not n != 0:
            raise AssertionError()
        return QD(self.a / n, -self.b / n, self.d)

    def __truediv__(self, o):
        return self * self._c(o).inv()

    def __rtruediv__(self, o):
        return self._c(o) * self.inv()

    def is_zero(self):
        return self.a == 0 and self.b == 0

    def sign(self):
        """Exact sign of a + b sqrt(d)."""
        if self.is_zero():
            return 0
        sa, sb = ((self.a > 0) - (self.a < 0), (self.b > 0) - (self.b < 0))
        if sb == 0:
            return sa
        if sa == 0 or sa == sb:
            return sb
        return sa if self.a * self.a > self.b * self.b * self.d else sb

    def __float__(self):
        return float(self.a) + float(self.b) * math.sqrt(self.d)

    def sym(self):
        return sp.Rational(self.a.numerator, self.a.denominator) + sp.Rational(self.b.numerator, self.b.denominator) * sp.sqrt(self.d)

    def __repr__(self):
        return '(%s + %s*sqrt%d)' % (self.a, self.b, self.d) if self.b else str(self.a)

def cos_pi_over(m):
    """cos(pi/m) for m in {2,3,4,5,6} as QD."""
    return {2: QD(0), 3: QD(Fr(1, 2)), 4: QD(0, Fr(1, 2), 2), 5: QD(Fr(1, 4), Fr(1, 4), 5), 6: QD(0, Fr(1, 2), 3)}[m]

class Space:
    """Vectors as coefficient lists in a basis with Gram matrix G (entries QD)."""

    def __init__(self, G):
        self.G, self.n = (G, len(G))

    def ip(self, u, v):
        return sum((u[i] * self.G[i][j] * v[j] for i in range(self.n) for j in range(self.n) if not u[i].is_zero() and (not v[j].is_zero())), QD(0))

def solve(A, b):
    n = len(A)
    M = [list(A[i]) + [b[i]] for i in range(n)]
    for c in range(n):
        piv = next((r for r in range(c, n) if not M[r][c].is_zero()))
        M[c], M[piv] = (M[piv], M[c])
        for r in range(n):
            if r != c and (not M[r][c].is_zero()):
                f = M[r][c] / M[c][c]
                M[r] = [x - f * y for x, y in zip(M[r], M[c])]
    return [M[i][n] / M[i][i] for i in range(n)]

def wythoff_exact(cox, rings):
    """Exact local data: Space (root basis), v0 and neighbours (coefficient lists)."""
    n = len(cox)
    G = [[QD(1) if i == j else -cos_pi_over(cox[i][j]) for j in range(n)] for i in range(n)]
    S = Space(G)
    b = [QD(Fr(1, 2)) if r else QD(0) for r in rings]
    v0 = solve(G, b)

    def refl(v, i):
        c = 2 * sum((G[i][j] * v[j] for j in range(n)), QD(0))
        w = list(v)
        w[i] = w[i] - c
        return w
    seeds = [refl(v0, i) for i in range(n) if rings[i]]
    key = lambda v: tuple(((x.a, x.b, x.d if x.b else 1) for x in v))
    seen = {key(s): s for s in seeds}
    fr = list(seeds)
    while fr:
        nf = []
        for v in fr:
            for i in range(n):
                if not rings[i]:
                    w = refl(v, i)
                    if key(w) not in seen:
                        seen[key(w)] = w
                        nf.append(w)
        fr = nf
    return (S, v0, list(seen.values()))

def dihedral_exact(S, v0, ridge_nbrs, A_nbrs, B_nbrs):
    """(sign, cos^2) of the angle between faces A and B (given by v0's neighbours in them)
    at the ridge spanned by v0 and ridge_nbrs (1 or 2 neighbours)."""
    sub = lambda u, v: [x - y for x, y in zip(u, v)]
    U = [sub(p, v0) for p in ridge_nbrs]
    k = len(U)
    Gm = [[S.ip(U[i], U[j]) for j in range(k)] for i in range(k)]

    def inward(nbrs):
        m = len(nbrs)
        c = [sum((p[i] for p in nbrs), QD(0)) / m for i in range(S.n)]
        w = sub(c, v0)
        x = solve(Gm, [S.ip(w, u) for u in U])
        for xi, u in zip(x, U):
            w = [a - xi * b for a, b in zip(w, u)]
        return w
    a, b = (inward(A_nbrs), inward(B_nbrs))
    num = S.ip(a, b)
    return (num.sign(), num * num / (S.ip(a, a) * S.ip(b, b)))

def to_sym(sign, c2):
    return sign * sp.sqrt(c2.sym())

def wythoff_facet(group, rings):
    """Exact (p, cellA, cellB, cos alpha (sympy)) for every polygon orbit at v0."""
    from geom import coxeter_matrix, wythoff, normals_for
    import cert_facets4 as cf
    Vf = wythoff([group], rings)
    nb, polys = cf.float_local(Vf, group + ''.join(map(str, rings)))
    S, v0, nbe = wythoff_exact(coxeter_matrix(group).tolist(), rings)
    N = np.array(normals_for([group]), dtype=float)
    if not np.allclose(N @ N.T, [[float(x) for x in r] for r in S.G], atol=1e-12):
        raise AssertionError()
    cart = lambda v: np.array([float(x) for x in v]) @ N
    if not np.linalg.norm(cart(v0) - Vf[0]) < 1e-09:
        raise AssertionError()
    amap = {}
    for w in nb:
        j = min(range(len(nbe)), key=lambda j: np.linalg.norm(cart(nbe[j]) - Vf[w]))
        if not np.linalg.norm(cart(nbe[j]) - Vf[w]) < 1e-09:
            raise AssertionError()
        amap[w] = nbe[j]
    out = []
    for p, ps, na, sa, nb_, sb in polys:
        sg, c2 = dihedral_exact(S, v0, [amap[w] for w in sorted(ps)][:2], [amap[w] for w in sa], [amap[w] for w in sb])
        out.append((p, na, nb_, to_sym(sg, c2)))
    return out

def polyhedron_edges(cell):
    """Exact (qa, qb, cos alpha) for the edges at v0 of an Archimedean/Platonic polyhedron
    (rank-3 Wythoffian; snubs are not supported and raise)."""
    from cells3d import ARCH
    from geom import coxeter_matrix, wythoff, normals_for
    from scipy.spatial import ConvexHull
    g, r = ARCH[cell]
    if r == 'snub':
        raise NotImplementedError(cell)
    Vf = wythoff([g], r)
    H = ConvexHull(Vf)
    faces = {}
    for eq in H.equations:
        on = tuple(sorted(np.where(np.abs(Vf @ eq[:-1] + eq[-1]) < 1e-07)[0].tolist()))
        faces[on] = True
    nb = [w for w in range(len(Vf)) if abs(np.linalg.norm(Vf[w] - Vf[0]) - 1) < 1e-06]
    at0 = [set(f) for f in faces if 0 in f]
    S, v0, nbe = wythoff_exact(coxeter_matrix(g).tolist(), r)
    N = np.array(normals_for([g]), dtype=float)
    cart = lambda v: np.array([float(x) for x in v]) @ N
    amap = {w: min(nbe, key=lambda v: np.linalg.norm(cart(v) - Vf[w])) for w in nb}
    out = []
    for x in nb:
        fa, fb = [f for f in at0 if x in f]
        sg, c2 = dihedral_exact(S, v0, [amap[x]], [amap[w] for w in nb if w in fa], [amap[w] for w in nb if w in fb])
        out.append((len(fa), len(fb), to_sym(sg, c2)))
    return out

def antiprism_edges(n):
    """Exact (qa, qb, cos alpha) at the edges of the n-gonal antiprism (sympy)."""
    t = sp.pi / n
    r = 1 / (2 * sp.sin(t))
    h = sp.sqrt(1 - (2 * r * sp.sin(t / 2)) ** 2)
    top = [sp.Matrix([r * sp.cos(2 * k * t), r * sp.sin(2 * k * t), h / 2]) for k in range(n)]
    bot = [sp.Matrix([r * sp.cos(2 * k * t + t), r * sp.sin(2 * k * t + t), -h / 2]) for k in range(n)]
    cen_top = sp.Matrix([0, 0, h / 2])

    def ang(e0, e1, ca, cb):
        u = e1 - e0

        def inw(c):
            w = c - e0
            return w - w.dot(u) / u.dot(u) * u
        a, b = (inw(ca), inw(cb))
        return guarded_nsimplify(sp.simplify(a.dot(b) / sp.sqrt(a.dot(a) * b.dot(b))))
    c3a = (top[0] + top[1] + bot[0]) / 3
    a_3n = ang(top[0], top[1], cen_top, c3a)
    c3b = (top[0] + bot[0] + bot[n - 1]) / 3
    a_33 = ang(top[0], bot[0], c3a, c3b)
    return [(3, n, a_3n), (3, 3, a_33)]

def prism_name(q):
    return 'cube' if q == 4 else 'P%d' % q

def facet_angles(name):
    """Exact (p, cellA, cellB, cos alpha) for every polygon orbit of facet `name`."""
    if name[:2] in ('A4', 'B4', 'D4', 'F4', 'H4') and name[2:].isdigit():
        return wythoff_facet(name[:2], tuple((int(c) for c in name[2:])))
    if name.startswith('pr-'):
        cell = name[3:]
        from cert_stage1 import cell_configs
        conf = cell_configs(128)[cell]
        out = [(q, cell, prism_name(q), sp.Integer(0)) for q in sorted(set(conf))]
        if cell.startswith('A') and cell[1:].isdigit():
            edges = antiprism_edges(int(cell[1:]))
        elif cell.startswith('P') and cell[1:].isdigit():
            n = int(cell[1:])
            edges = [(4, n, sp.Integer(0)), (4, 4, sp.cos(sp.pi * (1 - sp.Rational(2, n))))]
        elif cell in ('snic', 'snid'):
            edges = []
        else:
            edges = polyhedron_edges(cell)
        out += [(4, prism_name(qa), prism_name(qb), c) for qa, qb, c in edges]
        return out
    if name.startswith('antiprism-prism-'):
        n = int(name.split('-')[-1])
        an = 'oct' if n == 3 else 'A%d' % n
        out = [(3, an, 'P3', sp.Integer(0)), (n, an, prism_name(n), sp.Integer(0))]
        out += [(4, prism_name(qa), prism_name(qb), c) for qa, qb, c in antiprism_edges(n)]
        return out
    if name.startswith('duoprism-'):
        p, q = map(int, name.split('-')[1:])
        return [(p, prism_name(p), prism_name(p), sp.cos(sp.pi * (1 - sp.Rational(2, q)))), (q, prism_name(q), prism_name(q), sp.cos(sp.pi * (1 - sp.Rational(2, p)))), (4, prism_name(p), prism_name(q), sp.Integer(0))]
    if name in ('sadi', 'gap'):
        return q5_facet(name)
    raise NotImplementedError(name)

def q5_facet(name):
    """Snub 24-cell / grand antiprism: exact Q(sqrt 5) Cartesian coordinates."""
    import cert_facets4 as cf
    half = QD(Fr(1, 2), 0, 5)
    phi = QD(Fr(1, 2), Fr(1, 2), 5)
    pts = []
    for i in range(4):
        for s in (1, -1):
            v = [QD(0, 0, 5)] * 4
            v[i] = QD(s, 0, 5)
            pts.append(v)
    for signs in itertools.product((1, -1), repeat=4):
        pts.append([half * s for s in signs])
    base = [phi / 2, half, 1 / (2 * phi), QD(0, 0, 5)]
    evens = [p for p in itertools.permutations(range(4)) if sum((1 for i in range(4) for j in range(i + 1, 4) if p[i] > p[j])) % 2 == 0]
    for perm in evens:
        for signs in itertools.product((1, -1), repeat=3):
            v = [QD(0, 0, 5)] * 4
            sv = list(signs) + [1]
            for k in range(4):
                v[perm[k]] = base[k] * sv[k]
            pts.append(v)
    uniq = {}
    for v in pts:
        uniq[tuple(((x.a, x.b, x.d if x.b else 1) for x in v))] = v
    pts = [[x * phi for x in v] for v in uniq.values()]
    if not len(pts) == 120:
        raise AssertionError()
    F = np.array([[float(x) for x in v] for v in pts])
    Fa = np.array([[float(x.mid()) for x in v] for v in cf.q5_600cell()])
    perm = [int(np.argmin(np.linalg.norm(F - a, axis=1))) for a in Fa]
    if not np.max(np.linalg.norm(F[perm] - Fa, axis=1)) < 1e-09:
        raise AssertionError()
    pts = [pts[i] for i in perm]
    F = F[perm]
    if name == 'sadi':
        keep = [i for i, v in enumerate(F) if not np.sum(np.abs(v) > 1e-09) in (1, 4)]
    else:
        keep = cf.grand_antiprism_from(F)
    sub = [pts[i] for i in keep]
    nb, polys = cf.float_local(F[keep], name)
    S = Space([[QD(1 if i == j else 0, 0, 5) for j in range(4)] for i in range(4)])
    out = []
    for p, ps, na, sa, nb_, sb in polys:
        sg, c2 = dihedral_exact(S, sub[0], [sub[w] for w in sorted(ps)][:2], [sub[w] for w in sa], [sub[w] for w in sb])
        out.append((p, na, nb_, to_sym(sg, c2)))
    return out

def _ball(mid, rad):
    from flint import arb
    m = arb(mid.strip('[').split(' ')[0])
    return m + arb(0, float(rad.strip('[').split(' ')[0]) * 2 + 1e-35)

def is_zero(expr):
    """Exact zero test of an algebraic sympy expression (minimal polynomial is x)."""
    X = sp.Symbol('X')
    return sp.minimal_polynomial(expr, X) == X

def guarded_nsimplify(original):
    """Numerical recognition proposes; only an exact residual accepts."""
    proposed = sp.nsimplify(original)
    if not is_zero(original - proposed):
        raise ArithmeticError('nsimplify proposal has nonzero exact residual')
    return proposed

def flat_cycles(pmax):
    """Certified construction/word operands only; see exact_inputs."""
    from exact_inputs import exclusion_lists
    cycles = json.load(open('cert_stage1_5d_p%d.json' % pmax))
    flat, _, failed, identities = exclusion_lists(cycles, pmax)
    return (flat, failed, identities)
_FA = {}

def facet_angles_cached(name):
    if name not in _FA:
        _FA[name] = facet_angles(name)
    return _FA[name]

def cell_R2(cell):
    """Squared radius authenticated to the replayed exact cell construction."""
    from exact_inputs import load_authenticated
    return load_authenticated().cell_radius2(cell)

def boundary_cycles(pmax):
    """Nonsingular Gram + exact zero coefficient; no float boundary matching."""
    from exact_inputs import exclusion_lists
    cycles = json.load(open('cert_stage1_5d_p%d.json' % pmax))
    _, boundary, failed, _ = exclusion_lists(cycles, pmax)
    if failed:
        raise ArithmeticError('unproved flat cycles')
    return (boundary, [])
if __name__ == '__main__':
    pmax = int(sys.argv[1])
    from exact_inputs import exclusion_lists, authenticate_exclusions
    cycles = json.load(open('cert_stage1_5d_p%d.json' % pmax))
    proved, bproved, failed, ident = exclusion_lists(cycles, pmax)
    flat = dict(pmax=pmax, flat=proved, failed=failed, identities=[[list(k[0]), str(k[1]), v] for k, v in ident.items()])
    boundary = dict(pmax=pmax, degenerate=bproved, unhandled=[])
    authenticate_exclusions(cycles, flat, boundary, pmax)
    print(len(proved), 'cycles proved flat (angle sum exactly 2 pi);', len(failed), 'failed;', len(ident), 'distinct identities', file=sys.stderr)
    print(len(bproved), '3-cycles excluded by nonsingular Gram and zero coefficient;', '0 unhandled', file=sys.stderr)
    json.dump(flat, open('exact_flat_p%d.json' % pmax, 'w'), indent=0)
    json.dump(boundary, open('exact_boundary_p%d.json' % pmax, 'w'), indent=0)
