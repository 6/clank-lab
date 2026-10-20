"""Independent snub verifier: SymPy equalities and dyadic rational intervals.

Does not import the proposal generator, snub_exact, snub_interval or the
primary checker. No floating-point inequality is used. Existing geom.py
is run only to check the indexed output enclosures and permutations.
"""
import argparse
from collections import Counter
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import hashlib
import json
import sys
import sympy as s

BITS = 512
SCALE = 1 << BITS


class I:
    """Outward-rounded dyadic intervals using integer/Fraction arithmetic."""
    def __init__(self, lo=0, hi=None):
        lo, hi = F(lo), F(lo if hi is None else hi)
        if not (lo <= hi):
            raise AssertionError()
        self.lo = F((lo*SCALE).__floor__(), SCALE)
        self.hi = F((hi*SCALE).__ceil__(), SCALE)

    def __add__(a, b):
        b = b if isinstance(b, I) else I(b)
        return I(a.lo+b.lo, a.hi+b.hi)
    __radd__ = __add__
    def __neg__(a):
        return I(-a.hi, -a.lo)
    def __sub__(a, b):
        return a+-asI(b)
    def __rsub__(a, b):
        return asI(b)+-a
    def __mul__(a, b):
        b = asI(b)
        v = [a.lo*b.lo, a.lo*b.hi, a.hi*b.lo, a.hi*b.hi]
        return I(min(v), max(v))
    __rmul__ = __mul__
    def __truediv__(a, b):
        b = asI(b)
        if not (b.lo*b.hi > 0):
            raise AssertionError('interval division by zero')
        return a*I(1/b.hi, 1/b.lo)
    def sqrt(a):
        if not (a.lo >= 0):
            raise AssertionError()
        l = isqrt((a.lo*SCALE*SCALE).__floor__())
        h = isqrt((a.hi*SCALE*SCALE).__ceil__())+1
        return I(F(l, SCALE), F(h, SCALE))
    def absmax(a):
        return max(abs(a.lo), abs(a.hi))
    def mid(a):
        return (a.lo+a.hi)/2


def asI(x):
    return x if isinstance(x, I) else I(x)


def dot(a, b):
    return sum((x*y for x, y in zip(a, b)), I())


def mv(A, x):
    return [dot(r, x) for r in A]


def mt(A):
    return list(map(list, zip(*A)))


def mm(A, B):
    return [[dot(a, b) for b in mt(B)] for a in A]


def minus(a, b):
    return [x-y for x, y in zip(a, b)]


def exact(M):
    return M.applyfunc(s.expand) if isinstance(M, s.MatrixBase) else s.expand(M)


def get_group(diag):
    r = s.sqrt(2 if diag == 'B3' else 5)
    half = s.Rational(1, 2)
    c01, c12 = (half, r/2) if diag == 'B3' else ((1+r)/4, half)
    G = s.Matrix([[1, -c01, 0], [-c01, 1, -c12], [0, -c12, 1]])
    E = s.eye(3)
    ref = [E-2*E[:, j]*G[j, :] for j in range(3)]
    A, B = exact(ref[0]*ref[1]), exact(ref[1]*ref[2])
    mats, words, lookup = [E], [None], {tuple(E): 0}
    perms = [[], []]
    for M in mats:
        for k, g in enumerate((A, B)):
            H = exact(g*M)
            if tuple(H) not in lookup:
                lookup[tuple(H)] = len(mats)
                words.append([lookup[tuple(M)], k])
                mats.append(H)
                if not (len(mats) <= 60):
                    raise AssertionError()
            perms[k].append(lookup[tuple(H)])
    if not (len(mats) == (24 if diag == 'B3' else 60)):
        raise AssertionError()
    for M in mats:
        if not (exact(M.T*G*M) == G):
            raise AssertionError()
        if not (exact(M.det()) == 1):
            raise AssertionError()
    edge = exact((E-A).T*G*(E-A))
    Q1 = exact(edge-(E-B).T*G*(E-B))
    C = exact(A*B)
    Q2 = exact(edge-(E-C).T*G*(E-C))
    seeds = [lookup[tuple(M)] for M in (A, exact(A**(2 if diag == 'B3' else 4)), B, exact(B**(3 if diag == 'B3' else 2)), C)]
    def six(M):
        return [M[i, i] for i in range(3)]+[2*M[i, j] for i in range(3) for j in range(i+1, 3)]
    uv = s.Matrix([six(Q1), six(Q2)]).T
    DS = [exact((E-M).T*G*(E-M)) for M in mats]
    for j in seeds:
        t = s.Matrix(six(DS[j]-edge))
        solution, params = uv.gauss_jordan_solve(t)
        if not (not params and exact(uv*solution-t) == s.zeros(6, 1)):
            raise AssertionError()
    for M, n in zip((A, B), (3, 4) if diag == 'B3' else (5, 3)):
        if not (exact(M**n) == E):
            raise AssertionError()
        want = {3: s.Integer(0), 4: s.Integer(1), 5: (1+r)/2}[n]
        if not (s.expand(s.trace(M)-want) == 0):
            raise AssertionError()
    return r, G, mats, words, perms, edge, Q1, Q2, seeds, DS


def enclosed(expr, radical):
    expr = s.expand(expr)
    b = expr.coeff(radical)
    a = s.expand(expr-b*radical)
    if not (a.is_Rational and b.is_Rational):
        raise AssertionError()
    a, b = F(int(a.p), int(a.q)), F(int(b.p), int(b.q))
    d = int(radical**2)
    return I(a)+I(b)*I(d).sqrt()


def toI(M, radical):
    return [[enclosed(M[i, j], radical) for j in range(3)] for i in range(3)]


def cholesky(G):
    L = [[I() for _ in range(3)] for _ in range(3)]
    for i in range(3):
        for j in range(i+1):
            v = G[i][j]-sum((L[i][k]*L[j][k] for k in range(j)), I())
            L[i][j] = v.sqrt() if i == j else v/L[j][j]
    return L


def root(Q1, Q2, G, X):
    def f(x):
        return [dot(x, mv(Q1, x)), dot(x, mv(Q2, x)), dot(x, mv(G, x))-1]
    def jac(x):
        return [[2*y for y in mv(M, x)] for M in (Q1, Q2, G)]
    c = [I(x.mid()) for x in X]
    Jc = jac(c)
    M = s.Matrix([[s.Rational(v.mid().numerator, v.mid().denominator) for v in row] for row in Jc]).inv()
    Y = [[I(F(int(M[i, j].p), int(M[i, j].q))) for j in range(3)] for i in range(3)]
    YJ = mm(Y, jac(X))
    E = [[int(i == j)-YJ[i][j] for j in range(3)] for i in range(3)]
    fc = f(c)
    K = [c[i]-dot(Y[i], fc)+dot(E[i], minus(X, c)) for i in range(3)]
    if not (all(x.lo < k.lo and k.hi < x.hi for k, x in zip(K, X))):
        raise AssertionError('rational root existence')
    if not (all(sum(x.absmax() for x in row) < 1 for row in E)):
        raise AssertionError('rational root uniqueness')
    return K


def cross(a, b):
    return [a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2], a[0]*b[1]-a[1]*b[0]]


def dyadic(t):
    sign, man, exp, _ = t
    return F((-1)**sign*man)*F(2)**exp


def check(cert):
    here = Path(__file__).resolve().parents[1]
    if not (cert['schema'] == 1):
        raise AssertionError()
    for name in ('geom.py', 'ivla.py', 'tcert.py'):
        if not (hashlib.sha256((here/'check_u3'/name).read_bytes()).hexdigest() == cert['sources'][name]):
            raise AssertionError()
    sys.path.insert(0, str(here/'check_u3'))
    import geom
    import tcert
    result = {}
    for diag in ('B3', 'H3'):
        data = cert['models'][diag]
        r, G, mats, words, perms, edge, Q1, Q2, seeds, DS = get_group(diag)
        if not (data['parents'] == words and data['permutations'] == perms and data['seeds'] == seeds):
            raise AssertionError()
        Giv, Eiv = toI(G, r), toI(edge, r)
        X = [I(F(a), F(b)) for a, b in data['root_box']]
        K = root(toI(Q1, r), toI(Q2, r), Giv, X)
        K = root(toI(Q1, r), toI(Q2, r), Giv, K)
        e = dot(K, mv(Eiv, K)).sqrt()
        if not (e.lo > 0):
            raise AssertionError()
        coeff = [x/e for x in K]
        T = mt(cholesky(Giv))
        points = [mv(T, mv(toI(M, r), coeff)) for M in mats]
        # Direct CONTAINMENT proves each old interval coordinate encloses the
        # independently certified indexed model. Overlap is never accepted.
        oldpoints, oldperms = geom.snub_perm(diag)
        if not (oldperms == perms and len(oldpoints) == len(points)):
            raise AssertionError()
        for p, old in zip(points, oldpoints):
            for x, v in zip(p, old):
                if not (dyadic(v._mpi_[0]) <= x.lo <= x.hi <= dyadic(v._mpi_[1])):
                    raise AssertionError('coordinate containment')
        edge_at_X = dot(X, mv(Eiv, X))
        for i, D in enumerate(DS[1:], 1):
            if i not in seeds:
                gap = dot(X, mv(toI(D, r), X))-edge_at_X
                if not (gap.lo > 0):
                    raise AssertionError('rational non-neighbor separation')
        model = tcert.SnubModel(diag)
        if not (model.n == len(mats) and model.dim == 3 and model.stab_gens == []):
            raise AssertionError()
        if not ([p.tolist() for p in model.gens] == perms and model.seeds == seeds):
            raise AssertionError()
        actions = [list(range(len(mats)))]
        for i, k in words[1:]:
            actions.append([perms[k][v] for v in actions[i]])
        inverse = [[p.index(i) for i in range(len(mats))] for p in actions]
        planar = set()
        base_orbits = set()
        for p in perms:
            O = [0]
            while p[O[-1]]:
                O.append(p[O[-1]])
            base_orbits.add(frozenset(O))
            for a in actions:
                C = tuple(a[v] for v in O)
                for C in (C, C[::-1]):
                    planar.update(C[i:]+C[:i] for i in range(len(C)))
        if not (model.planar == base_orbits):
            raise AssertionError()
        seen, edges = set(), Counter()
        for C in data['faces']:
            if not (len(C) >= 3 and len(set(C)) == len(C)):
                raise AssertionError()
            if not (all(type(i) is int and 0 <= i < len(mats) for i in C)):
                raise AssertionError()
            S = frozenset(C)
            if not (S not in seen):
                raise AssertionError()
            seen.add(S)
            if not (len(C) == 3 or tuple(C) in planar):
                raise AssertionError('rational exact polygon orbit')
            for a, b in zip(C, C[1:]+C[:1]):
                if not (inverse[a][b] in seeds):
                    raise AssertionError('rational exact face edge')
                edges[tuple(sorted((a, b)))] += 1
            a, b, c = [points[i] for i in C[:3]]
            normal = cross(minus(b, a), minus(c, a))
            if not (dot(normal, normal).lo > 0):
                raise AssertionError()
            signs = [dot(normal, minus(v, a)) for i, v in enumerate(points) if i not in S]
            if not (signs and (all(x.lo > 0 for x in signs) or all(x.hi < 0 for x in signs))):
                raise AssertionError('rational strict support')
        if not (set(edges.values()) == {2}):
            raise AssertionError('rational complete boundary')
        counts = dict(Counter(map(len, data['faces'])))
        if not (counts == ({3: 32, 4: 6} if diag == 'B3' else {3: 80, 5: 12})):
            raise AssertionError()
        if not (set().union(*seen) == set(range(len(mats)))):
            raise AssertionError()
        result[diag] = [len(mats), len(edges), len(seen)]
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('certificate', nargs='?', type=Path, default=Path(__file__).with_name('snub_certificate.json'))
    args = parser.parse_args()
    print(json.dumps({'outcome': 'CERTIFIED', 'rational_models': check(json.loads(args.certificate.read_text()))}, sort_keys=True))
