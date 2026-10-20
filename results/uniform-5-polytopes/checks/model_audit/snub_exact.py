"""Exact rank-three rotation groups, in the simple-root coefficient basis.

No coordinate search, rounded point identification or separation lemma is used.
All equalities are rational arithmetic in Q(sqrt(d)), d=2 or 5.
"""
from dataclasses import dataclass
from fractions import Fraction as F


@dataclass(frozen=True)
class Q:
    d: int
    a: F = F(0)
    b: F = F(0)

    def __post_init__(self):
        object.__setattr__(self, 'a', F(self.a))
        object.__setattr__(self, 'b', F(self.b))

    def coerce(self, v):
        if isinstance(v, Q):
            if not (v.d == self.d):
                raise AssertionError()
            return v
        return Q(self.d, v)

    def __add__(self, v):
        v = self.coerce(v)
        return Q(self.d, self.a + v.a, self.b + v.b)

    __radd__ = __add__

    def __neg__(self):
        return Q(self.d, -self.a, -self.b)

    def __sub__(self, v):
        return self + -self.coerce(v)

    def __rsub__(self, v):
        return self.coerce(v) - self

    def __mul__(self, v):
        v = self.coerce(v)
        return Q(self.d, self.a*v.a + self.d*self.b*v.b,
                 self.a*v.b + self.b*v.a)

    __rmul__ = __mul__

    def __truediv__(self, v):
        v = self.coerce(v)
        den = v.a*v.a - self.d*v.b*v.b
        if not (den):
            raise AssertionError()
        return self * Q(self.d, v.a/den, -v.b/den)

    def __bool__(self):
        return bool(self.a or self.b)


def eye(d):
    return tuple(tuple(Q(d, int(i == j)) for j in range(3)) for i in range(3))


def tr(A):
    return tuple(zip(*A))


def mm(A, B):
    return tuple(tuple(sum(x*y for x, y in zip(a, b)) for b in tr(B)) for a in A)


def sub(A, B):
    return tuple(tuple(a-b for a, b in zip(r, s)) for r, s in zip(A, B))


def flatten(A):
    return [A[i][i] for i in range(3)] + [2*A[i][j] for i in range(3) for j in range(i+1, 3)]


def span_coeff(target, u, v):
    """Check a quadratic-form identity target=a*u+b*v, exactly."""
    t, u, v = map(flatten, (target, u, v))
    for i in range(6):
        for j in range(i):
            det = u[i]*v[j]-u[j]*v[i]
            if det:
                a = (t[i]*v[j]-t[j]*v[i])/det
                b = (u[i]*t[j]-u[j]*t[i])/det
                if all(t[k] == a*u[k]+b*v[k] for k in range(6)):
                    return a, b
                return None
    raise AssertionError('dependent defining equations')


class ExactGroup:
    def __init__(self, diag):
        if not (diag in ('B3', 'H3')):
            raise AssertionError()
        self.diag = diag
        d = self.d = 2 if diag == 'B3' else 5
        zero, one = Q(d), Q(d, 1)
        c01 = Q(d, F(1, 2)) if diag == 'B3' else Q(d, F(1, 4), F(1, 4))
        c12 = Q(d, 0, F(1, 2)) if diag == 'B3' else Q(d, F(1, 2))
        self.G = ((one, -c01, zero), (-c01, one, -c12), (zero, -c12, one))
        self.I = eye(d)
        R = []
        for k in range(3):
            R.append(tuple(tuple(self.I[i][j] - (2*self.G[k][j] if i == k else zero)
                                 for j in range(3)) for i in range(3)))
        self.A, self.B = mm(R[0], R[1]), mm(R[1], R[2])
        self.C = mm(self.A, self.B)
        for r in R:
            if not (mm(r, r) == self.I):
                raise AssertionError()
            if not (mm(mm(tr(r), self.G), r) == self.G):
                raise AssertionError()
        self.gens = (self.A, self.B)
        self.mats = [self.I]
        self.parent = [None]
        self.lookup = {self.I: 0}
        self.perms = [[], []]
        i = 0
        while i < len(self.mats):
            for k, g in enumerate(self.gens):
                h = mm(g, self.mats[i])
                if h not in self.lookup:
                    self.lookup[h] = len(self.mats)
                    self.mats.append(h)
                    self.parent.append((i, k))
                    if not (len(self.mats) <= 60):
                        raise AssertionError()
                self.perms[k].append(self.lookup[h])
            i += 1
        self.n = len(self.mats)
        if not (self.n == (24 if diag == 'B3' else 60)):
            raise AssertionError()
        for g in self.mats:
            if not (mm(mm(tr(g), self.G), g) == self.G):
                raise AssertionError()
        self.inverses = {}
        for i, parent in enumerate(self.parent):
            if parent is None:
                self.inverses[self.mats[i]] = self.I
            else:
                j, k = parent
                ig = self.I
                for _ in range((3, 4)[k] - 1 if diag == 'B3' else (5, 3)[k] - 1):
                    ig = mm(ig, self.gens[k])
                self.inverses[self.mats[i]] = mm(self.inverses[self.mats[j]], ig)
            if not (mm(self.inverses[self.mats[i]], self.mats[i]) == self.I):
                raise AssertionError()
        self.order = (3, 4) if diag == 'B3' else (5, 3)
        for g, m in zip(self.gens, self.order):
            power = self.I
            for j in range(1, m+1):
                power = mm(g, power)
                if not ((power == self.I) == (j == m)):
                    raise AssertionError()
            # Angle 2*pi/m, rather than the pentagram step 4*pi/5.
            trace = sum(g[j][j] for j in range(3))
            want = {3: zero, 4: one, 5: Q(d, F(1, 2), F(1, 2))}[m]
            if not (trace == want):
                raise AssertionError()
        self.D = [self.distance_form(g) for g in self.mats]
        self.edge = self.distance_form(self.A)
        self.Q1 = sub(self.edge, self.distance_form(self.B))
        self.Q2 = sub(self.edge, self.distance_form(self.C))
        self.seeds = [self.lookup[self.A], self.lookup[self.inverse(self.A)],
                      self.lookup[self.B], self.lookup[self.inverse(self.B)],
                      self.lookup[self.C]]
        if not (len(set(self.seeds)) == 5):
            raise AssertionError()
        self.identities = {}
        for i in self.seeds:
            coeff = span_coeff(sub(self.D[i], self.edge), self.Q1, self.Q2)
            if not (coeff is not None):
                raise AssertionError()
            self.identities[i] = coeff

    def inverse(self, g):
        return self.inverses[g]

    def distance_form(self, g):
        D = sub(self.I, g)
        return mm(mm(tr(D), self.G), D)

    def relative(self, i, j):
        return self.lookup[mm(self.inverse(self.mats[i]), self.mats[j])]

    def cyclic_orbit(self, generator):
        out = [0]
        j = self.perms[generator][0]
        while j:
            out.append(j)
            j = self.perms[generator][j]
        return out
