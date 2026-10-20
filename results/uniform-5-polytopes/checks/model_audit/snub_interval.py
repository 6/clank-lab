"""Interval inequalities and the construction-word link for snub models.

Floating midpoints select preconditioners only. Every accepted predicate is
an outward-rounded interval inequality; all equalities use snub_exact.
"""
import sys
from fractions import Fraction
from pathlib import Path
from mpmath import iv

CHECK_U3 = Path(__file__).resolve().parents[1] / 'check_u3'
sys.path.insert(0, str(CHECK_U3))
import geom
from ivla import (ZERO, ONE, dot, matvec, matmul, transpose, cholesky, solve,
                  inverse, vsub, dist2)


def qiv(q):
    a = iv.mpf(q.a.numerator)/q.a.denominator
    b = iv.mpf(q.b.numerator)/q.b.denominator
    return a + b*iv.sqrt(q.d)


def miv(M):
    return [[qiv(x) for x in row] for row in M]


def quad(M, x):
    return dot(x, matvec(M, x))


def krawczyk(F, J, X):
    c = [iv.mpf(x.mid) for x in X]
    Y = inverse([[iv.mpf(x.mid) for x in row] for row in J(c)])
    Y = [[iv.mpf(x.mid) for x in row] for row in Y]
    f, JX = F(c), J(X)
    E = [[(ONE if i == j else ZERO)-sum((Y[i][k]*JX[k][j] for k in range(3)), ZERO)
          for j in range(3)] for i in range(3)]
    K = [c[i]-dot(Y[i], f)+sum((E[i][j]*(X[j]-c[j]) for j in range(3)), ZERO)
         for i in range(3)]
    if not (all(k.a > x.a and k.b < x.b for k, x in zip(K, X))):
        raise AssertionError('Krawczyk existence')
    if not (all(sum(max(abs(e.a), abs(e.b)) for e in row) < 1 for row in E)):
        raise AssertionError('contraction')
    return K


def inside(A, B):
    return all(a.a >= b.a and a.b <= b.b for a, b in zip(A, B))


def capture(diag):
    """Read the actual model's insertion history, not an approximate match.

    The trace does not alter the model or point-set methods. A return from
    add records every original vertex assignment/lookup, in call order.
    """
    saved, adds = {}, []
    snub_code = geom.snub_perm.__wrapped__.__code__
    add_code = geom.PointSet.add.__code__
    def trace(frame, event, arg):
        if event == 'return':
            if frame.f_code == snub_code:
                saved.update(frame.f_locals)
            elif frame.f_code == add_code:
                adds.append((frame.f_locals['v'], arg))
        return trace
    geom.snub_perm.cache_clear()
    old = sys.gettrace()
    sys.settrace(trace)
    try:
        V, perms = geom.snub_perm(diag)
    finally:
        sys.settrace(old)
    if not (saved and len(adds) == 1+2*len(V)):
        raise AssertionError()
    return V, perms, saved, adds


def construction(group, corruption='', root_box=None):
    V, perms, old, adds = capture(group.diag)
    G = miv(group.G)
    T = transpose(cholesky(G))  # Cartesian coordinates = T * root coefficients
    # Enclose the original Cartesian root box in a larger coefficient box.
    orig_coeff = [r[0] for r in solve(T, [[x] for x in old['X']])]
    eps = iv.mpf('1e-24')
    X = [iv.mpf([x.mid-eps.b, x.mid+eps.b]) for x in orig_coeff]
    if root_box is not None:
        def rational(text):
            f = Fraction(text)
            return iv.mpf(f.numerator)/f.denominator
        if not (len(root_box) == 3):
            raise AssertionError()
        X = [iv.mpf([rational(a).a, rational(b).b]) for a, b in root_box]
    Q1, Q2 = miv(group.Q1), miv(group.Q2)
    if corruption == 'root-equation':
        Q1[0][0] += 1
    def F(x):
        return [quad(Q1, x), quad(Q2, x), quad(G, x)-1]
    def J(x):
        return [[2*y for y in matvec(M, x)] for M in (Q1, Q2, G)]
    K = krawczyk(F, J, X)
    if not (inside(orig_coeff, X)):
        raise AssertionError('original root box in uniqueness box')
    if not (inside(matvec(T, K), old['X'])):
        raise AssertionError('independent root in original root box')
    # Certify that the ORIGINAL Krawczyk operator encloses this same root.
    # Same exact equations: the Cholesky simple roots have Gram G; products
    # r0*r1,r1*r2,r0*r2 conjugate the exact coefficient matrices by T.
    xm, Y = old['xm'], old['Y']
    fx, JX = old['F'](xm), old['J'](old['X'])
    YJ = matmul(Y, JX)
    O = []
    E = [[(ONE if i == j else ZERO)-YJ[i][j] for j in range(3)] for i in range(3)]
    for i in range(3):
        z = xm[i]-dot(Y[i], fx)
        for j in range(3):
            z += E[i][j]*(old['X'][j]-xm[j])
        O.append(z)
    if not (all(o._mpi_ == k._mpi_ for o, k in zip(O, old['Kx']))):
        raise AssertionError('original Krawczyk enclosure')
    if not (inside(O, old['X'])):
        raise AssertionError()
    if not (all(sum(max(abs(e.a), abs(e.b)) for e in row) < 1 for row in E)):
        raise AssertionError()
    # Original p=Kx/sqrt(distance_form_A(Kx)). Its interval contains the
    # normalized exact root. All subsequent interval assignments contain
    # exact word images by interval arithmetic. Index decisions are checked
    # by exact matrix identities, with NO separation premise.
    expected = [[*p] for p in group.perms]
    if corruption == 'permutation':
        expected[0][0], expected[0][1] = expected[0][1], expected[0][0]
    if not (perms == expected):
        raise AssertionError('exact generator permutation')
    if not (adds[0][1] == (0, True)):
        raise AssertionError()
    if not (all(x._mpi_ == y._mpi_ for x, y in zip(adds[0][0], old['p']))):
        raise AssertionError('initial interval assignment')
    seen = {0}
    at = 1
    # The exact matrix BFS uses the same frontier order as geom.snub_perm.
    for i in range(group.n):
        for k in range(2):
            image, (j, new) = adds[at]
            computed = geom._matvec(old['gens'][k], V[i])
            if not (all(x._mpi_ == y._mpi_ for x, y in zip(image, computed))):
                raise AssertionError('interval word assignment')
            want = group.perms[k][i]
            if not (j == want and new == (want not in seen)):
                raise AssertionError('construction-word index')
            seen.add(want)
            at += 1
    if not (len(V) == group.n and len(seen) == group.n):
        raise AssertionError()
    edge = quad(miv(group.edge), X)
    if not (edge.a > 0):
        raise AssertionError()
    for i in range(1, group.n):
        if i not in group.seeds:
            delta = quad(miv(group.D[i]), X)-edge
            if not (delta.a > 0):
                raise AssertionError(('non-neighbor distance', i, delta))
    # Cartesian enclosures for the independently defined, normalized model.
    scale = iv.sqrt(quad(miv(group.edge), K))
    coeff = [x/scale for x in K]
    points = [matvec(T, matvec(miv(m), coeff)) for m in group.mats]
    return points, X, V


def cross(a, b):
    return [a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2], a[0]*b[1]-a[1]*b[0]]


def support(points, face):
    a, b, c = [points[i] for i in face[:3]]
    normal = cross(vsub(b, a), vsub(c, a))
    if not (dot(normal, normal).a > 0):
        raise AssertionError('nondegenerate face')
    signs = [dot(normal, vsub(p, a)) for i, p in enumerate(points) if i not in face]
    if not (signs and (all(x.a > 0 for x in signs) or all(x.b < 0 for x in signs))):
        raise AssertionError('strict facet support')
