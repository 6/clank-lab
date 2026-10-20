"""Vertex figures VF(K) of the facet types K (uniform 4-polytopes, unit edges).

Built from the definitions only: Wythoff constructions for the A4, B4, D4,
F4, H4 families and for the 3-dimensional factors of prisms, explicit
coordinates for duoprisms and antiprism prisms, the 600-cell's coordinates
for the snub 24-cell and the grand antiprism.

For a vertex v0 of K (centre at the origin, circumradius R_K) the neighbours
lie in the hyperplane y.v0 = R_K^2 - 1/2; VF(K) is their convex hull, given in
3D coordinates about its circumcentre.  Its 2-faces are the vertex figures of
the cells at v0 and are labelled by the cell type, read off from the cyclic
sequence of polygon sizes (edge of VF(K) of length 2cos(pi/p) <-> p-gon).

All of this is done in mpmath mpf at BUILD_PREC bits; the facet data are then
enclosed in intervals of radius 2^-(BUILD_PREC-64) (see README for the error
argument).
"""
import itertools
from mpmath import mp, mpf, matrix, cos, sin, pi, sqrt, findroot
BUILD_PREC = 512
mp.prec = BUILD_PREC
TOL = mpf(2) ** (-300)

def dot(a, b):
    return sum((x * y for x, y in zip(a, b)))

def sub(a, b):
    return [x - y for x, y in zip(a, b)]

def scal(c, a):
    return [c * x for x in a]

def norm(a):
    return sqrt(dot(a, a))

def key(p):
    return tuple((int(mp.nint(x * 10 ** 30)) for x in p))

def coxeter_normals(m):
    """Unit mirror normals n_i with n_i.n_j = -cos(pi/m_ij) (Cholesky)."""
    k = len(m)
    G = [[mpf(1) if i == j else -cos(pi / m[i][j]) for j in range(k)] for i in range(k)]
    L = [[mpf(0)] * k for _ in range(k)]
    for i in range(k):
        for j in range(i + 1):
            s = G[i][j] - sum((L[i][t] * L[j][t] for t in range(j)))
            if i == j:
                if not s > 0:
                    raise AssertionError()
                L[i][i] = sqrt(s)
            else:
                L[i][j] = s / L[j][j]
    return L

def cox_matrix(k, edges):
    m = [[2] * k for _ in range(k)]
    for i, j, v in edges:
        m[i][j] = m[j][i] = v
    return m
GROUPS4 = {'A4': cox_matrix(4, [(0, 1, 3), (1, 2, 3), (2, 3, 3)]), 'B4': cox_matrix(4, [(0, 1, 3), (1, 2, 3), (2, 3, 4)]), 'D4': cox_matrix(4, [(1, 0, 3), (1, 2, 3), (1, 3, 3)]), 'F4': cox_matrix(4, [(0, 1, 3), (1, 2, 4), (2, 3, 3)]), 'H4': cox_matrix(4, [(0, 1, 5), (1, 2, 3), (2, 3, 3)])}
GROUPS3 = {'A3': cox_matrix(3, [(0, 1, 3), (1, 2, 3)]), 'B3': cox_matrix(3, [(0, 1, 4), (1, 2, 3)]), 'H3': cox_matrix(3, [(0, 1, 5), (1, 2, 3)])}

def reflect(n, y):
    c = 2 * dot(n, y)
    return [a - c * b for a, b in zip(y, n)]

def wythoff_point(N, rings):
    """Point at distance 1/2 from ringed mirrors, on unringed ones."""
    k = len(N)
    b = [mpf(1) / 2 if r else mpf(0) for r in rings]
    x = [mpf(0)] * k
    for i in range(k):
        x[i] = (b[i] - sum((N[i][t] * x[t] for t in range(i)))) / N[i][i]
    return x

def orbit(gens, pts):
    """Closure of pts under the reflections/maps in gens."""
    seen = {}
    todo = list(pts)
    for p in todo:
        seen[key(p)] = p
    while todo:
        p = todo.pop()
        for g in gens:
            q = g(p)
            kq = key(q)
            if kq not in seen:
                seen[kq] = q
                todo.append(q)
    return list(seen.values())

def wythoff_vertex_and_neighbours(m, rings):
    N = coxeter_normals(m)
    x = wythoff_point(N, rings)
    J = [i for i in range(len(rings)) if not rings[i]]
    gensJ = [lambda y, n=N[i]: reflect(n, y) for i in J]
    first = [reflect(N[i], x) for i in range(len(rings)) if rings[i]]
    nb = orbit(gensJ, first)
    return (x, nb)
POLY3 = {'tet': ('A3', (1, 0, 0)), 'oct': ('B3', (0, 0, 1)), 'cube': ('B3', (1, 0, 0)), 'ico': ('H3', (0, 0, 1)), 'doe': ('H3', (1, 0, 0)), 'tut': ('A3', (1, 1, 0)), 'co': ('B3', (0, 1, 0)), 'tic': ('B3', (1, 1, 0)), 'toe': ('B3', (0, 1, 1)), 'sirco': ('B3', (1, 0, 1)), 'girco': ('B3', (1, 1, 1)), 'id': ('H3', (0, 1, 0)), 'tid': ('H3', (0, 1, 1)), 'ti': ('H3', (1, 1, 0)), 'srid': ('H3', (1, 0, 1)), 'grid': ('H3', (1, 1, 1))}

def snub3(group):
    """Snub polyhedron: orbit of x under the rotation group with all of
    |x - a x|, |x - b x|, |x - c x| equal to 1 (a = s0 s1, b = s1 s2,
    c = s0 s2); returns (x, neighbours)."""
    N = coxeter_normals(GROUPS3[group])
    s = [lambda y, n=N[i]: reflect(n, y) for i in range(3)]
    a = lambda y: s[0](s[1](y))
    b = lambda y: s[1](s[2](y))
    c = lambda y: s[0](s[2](y))

    def eqs(x0, x1, x2):
        x = [x0, x1, x2]
        return [dot(sub(x, a(x)), sub(x, a(x))) - 1, dot(sub(x, b(x)), sub(x, b(x))) - 1, dot(sub(x, c(x)), sub(x, c(x))) - 1]
    x0 = wythoff_point(N, (1, 1, 1))
    sol = findroot(eqs, [x0[0], x0[1], x0[2]])
    x = [sol[0], sol[1], sol[2]]
    if not all((dot(N[i], x) > 0 for i in range(3))):
        raise AssertionError('snub point outside chamber')
    rot = [a, b, c]
    allv = orbit(rot, [x])
    d2 = sorted(((dot(sub(y, x), sub(y, x)), i) for i, y in enumerate(allv) if key(y) != key(x)))
    nb = [allv[i] for dd, i in d2 if abs(dd - 1) < TOL]
    if not (len(nb) == 5 and d2[5][0] > 1 + mpf('1e-3')):
        raise AssertionError((group, len(nb)))
    return (x, nb)

def poly3(name):
    """(vertex x0, neighbours) of the uniform polyhedron with unit edges,
    centred at the origin."""
    if name == 'snic':
        return snub3('B3')
    if name == 'snid':
        return snub3('H3')
    g, rings = POLY3[name]
    return wythoff_vertex_and_neighbours(GROUPS3[g], rings)

def polygon(n):
    rad = 1 / (2 * sin(pi / n))
    return [[rad * cos(2 * pi * k / n), rad * sin(2 * pi * k / n)] for k in range(n)]

def antiprism(n):
    rad = 1 / (2 * sin(pi / n))
    chord2 = 2 * rad ** 2 * (1 - cos(pi / n))
    h = sqrt(1 - chord2) / 2
    pts = []
    for k in range(n):
        pts.append([rad * cos(2 * pi * k / n), rad * sin(2 * pi * k / n), h])
        pts.append([rad * cos((2 * k + 1) * pi / n), rad * sin((2 * k + 1) * pi / n), -h])
    return pts

def nearest(allv, x):
    d = [(dot(sub(y, x), sub(y, x)), i) for i, y in enumerate(allv)]
    d = [t for t in d if t[0] > TOL]
    m = min((t[0] for t in d))
    if not abs(m - 1) < TOL:
        raise AssertionError(m)
    return [allv[i] for dd, i in d if abs(dd - 1) < TOL]

def cell600():
    phi = (1 + sqrt(5)) / 2
    V = []
    for i in range(4):
        for s in (1, -1):
            v = [mpf(0)] * 4
            v[i] = mpf(s)
            V.append(v)
    for signs in itertools.product((1, -1), repeat=4):
        V.append([mpf(s) / 2 for s in signs])
    base = [phi / 2, mpf(1) / 2, 1 / (2 * phi), mpf(0)]
    even = [p for p in itertools.permutations(range(4)) if sum((1 for i in range(4) for j in range(i + 1, 4) if p[i] > p[j])) % 2 == 0]
    for p in even:
        for signs in itertools.product((1, -1), repeat=3):
            v = [mpf(0)] * 4
            for t in range(3):
                v[p[t]] = signs[t] * base[t]
            V.append(v)
    if not len(V) == 120:
        raise AssertionError()
    return (V, phi)

def facet4(name):
    """(v0, neighbours) of facet type K (unit edges, centre at origin)."""
    if name[:2] in ('A4', 'B4', 'D4', 'F4', 'H4') and len(name) == 6:
        rings = tuple((int(c) for c in name[2:]))
        return wythoff_vertex_and_neighbours(GROUPS4[name[:2]], rings)
    if name.startswith('pr-'):
        x, nb = poly3(name[3:])
        h = mpf(1) / 2
        v0 = list(x) + [h]
        return (v0, [list(y) + [h] for y in nb] + [list(x) + [-h]])
    if name.startswith('antiprism-prism-'):
        n = int(name.split('-')[-1])
        A = antiprism(n)
        h = mpf(1) / 2
        allv = [p + [h] for p in A] + [p + [-h] for p in A]
        return (allv[0], nearest(allv, allv[0]))
    if name.startswith('duoprism-'):
        p, q = map(int, name.split('-')[1:])
        P, Q = (polygon(p), polygon(q))
        v0 = P[0] + Q[0]
        nb = [P[1] + Q[0], P[p - 1] + Q[0], P[0] + Q[1], P[0] + Q[q - 1]]
        return (v0, nb)
    if name in ('sadi', 'gap'):
        V, phi = cell600()
        if name == 'sadi':
            V = V[24:]
        else:
            g = [phi / 2, mpf(1) / 2, 1 / (2 * phi), mpf(0)]
            e = [mpf(1), mpf(0), mpf(0), mpf(0)]
            u = sub(g, scal(g[0], e))
            u = scal(1 / norm(u), u)

            def inplane(v, a, b):
                pr = add(scal(dot(v, a), a), scal(dot(v, b), b))
                return dot(sub(v, pr), sub(v, pr)) < TOL
            ring1 = [v for v in V if inplane(v, e, u)]
            comp = []
            for t in range(4):
                w = [mpf(0)] * 4
                w[t] = mpf(1)
                for bvec in [e, u] + comp:
                    w = sub(w, scal(dot(w, bvec), bvec))
                if norm(w) > mpf('1e-10'):
                    comp.append(scal(1 / norm(w), w))
            if not len(comp) == 2:
                raise AssertionError()
            ring2 = [v for v in V if inplane(v, comp[0], comp[1])]
            if not (len(ring1) == 10 and len(ring2) == 10):
                raise AssertionError((len(ring1), len(ring2)))
            rm = set((key(v) for v in ring1 + ring2))
            V = [v for v in V if key(v) not in rm]
            if not len(V) == 100:
                raise AssertionError()
        V = [scal(phi, v) for v in V]
        return (V[0], nearest(V, V[0]))
    raise ValueError(name)

def add(a, b):
    return [x + y for x, y in zip(a, b)]
P_MAX = int(__import__('os').environ.get('U2_PMAX', '12'))

def p_of_length(L):
    for p in range(3, P_MAX + 1):
        if abs(L - 2 * cos(pi / p)) < TOL:
            return p
    raise ValueError('edge length %s' % L)

def cell_label(cfg):
    """cfg: cyclic list of polygon sizes around a vertex of the cell."""
    ms = sorted(cfg)
    fixed = {(3, 3, 3): 'tet', (4, 4, 4): 'cube', (3, 3, 3, 3): 'oct', (5, 5, 5): 'doe', (3, 3, 3, 3, 3): 'ico', (3, 6, 6): 'tut', (3, 3, 4, 4): 'co', (3, 8, 8): 'tic', (4, 6, 6): 'toe', (3, 4, 4, 4): 'sirco', (4, 6, 8): 'girco', (3, 3, 5, 5): 'id', (3, 10, 10): 'ti', (5, 6, 6): 'tid', (3, 4, 4, 5): 'srid', (4, 6, 10): 'grid', (3, 3, 3, 3, 4): 'snic', (3, 3, 3, 3, 5): 'snid'}
    t = tuple(ms)
    if t in fixed:
        if t in ((3, 3, 4, 4), (3, 3, 5, 5)):
            if not cfg[0] != cfg[1]:
                raise AssertionError(cfg)
        if t == (3, 4, 4, 5):
            if not any((cfg[i] == 3 and cfg[(i + 2) % 4] == 5 for i in range(4))):
                raise AssertionError(cfg)
        return fixed[t]
    if len(ms) == 3 and ms[0] == 4 and (ms[1] == 4):
        return 'P%d' % ms[2]
    if len(ms) == 3 and ms.count(4) == 2:
        return 'P%d' % ms[0]
    if len(ms) == 4 and ms.count(3) == 3:
        return 'A%d' % ms[3]
    raise ValueError('cell config %s' % cfg)

def cross(a, b):
    return [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]]

def hull3(pts):
    """Faces of the convex hull of pts (3D, in convex position, centre 0
    strictly inside) as cyclic index lists ordered counter-clockwise seen
    from outside, with outward unit normal and distance."""
    n = len(pts)
    faces = {}
    for i, j, k in itertools.combinations(range(n), 3):
        nv = cross(sub(pts[j], pts[i]), sub(pts[k], pts[i]))
        if norm(nv) < mpf('1e-20'):
            continue
        nv = scal(1 / norm(nv), nv)
        h = dot(nv, pts[i])
        if h < 0:
            nv, h = (scal(-1, nv), -h)
        side = [dot(nv, p) - h for p in pts]
        if all((s < TOL for s in side)):
            on = tuple(sorted((t for t in range(n) if abs(side[t]) < TOL)))
            if not all((s < -mpf('1e-6') for t, s in enumerate(side) if t not in on)):
                raise AssertionError()
            faces[on] = (nv, h)
    out = []
    for on, (nv, h) in faces.items():
        c = scal(mpf(1) / len(on), [sum((pts[t][a] for t in on)) for a in range(3)])
        e1 = sub(pts[on[0]], c)
        e1 = scal(1 / norm(e1), e1)
        e2 = cross(nv, e1)
        from mpmath import atan2
        order = sorted(on, key=lambda t: atan2(dot(sub(pts[t], c), e2), dot(sub(pts[t], c), e1)))
        if not h > mpf('1e-6'):
            raise AssertionError()
        out.append((order, nv, h))
    E = set()
    for order, _, _ in out:
        for a in range(len(order)):
            E.add(frozenset((order[a], order[(a + 1) % len(order)])))
    if not n - len(E) + len(out) == 2:
        raise AssertionError((n, len(E), len(out)))
    return out

class FacetType:
    pass

def build_facet(name):
    v0, nb = facet4(name)
    R2 = dot(v0, v0)
    for y in nb:
        if not abs(dot(sub(y, v0), sub(y, v0)) - 1) < TOL:
            raise AssertionError()
        if not abs(dot(y, y) - R2) < TOL:
            raise AssertionError()
    c = scal((R2 - mpf(1) / 2) / R2, v0)
    basis = []
    vn = scal(1 / sqrt(R2), v0)
    for t in range(4):
        w = [mpf(0)] * 4
        w[t] = mpf(1)
        for b in [vn] + basis:
            w = sub(w, scal(dot(w, b), b))
        if norm(w) > mpf('1e-6') and len(basis) < 3:
            basis.append(scal(1 / norm(w), w))
    if not len(basis) == 3:
        raise AssertionError()
    pts = [[dot(sub(y, c), b) for b in basis] for y in nb]
    rK2 = 1 - 1 / (4 * R2)
    for p in pts:
        if not abs(dot(p, p) - rK2) < TOL:
            raise AssertionError()
    faces = hull3(pts)
    F = FacetType()
    F.name = name
    F.R2 = R2
    F.rK2 = rK2
    F.verts = pts
    F.faces = []
    F.edge_p = {}
    for order, nv, h in faces:
        cfg = []
        for a in range(len(order)):
            i, j = (order[a], order[(a + 1) % len(order)])
            p = p_of_length(norm(sub(pts[i], pts[j])))
            cfg.append(p)
            F.edge_p[frozenset((i, j))] = p
        F.faces.append({'verts': order, 'normal': nv, 'h': h, 'label': cell_label(cfg), 'ps': cfg})
    return F
if __name__ == '__main__':
    import json, sys
    names = [f['name'] for f in json.load(open(sys.argv[1]))]
    for nm in names:
        F = build_facet(nm)
        print(nm, len(F.verts), len(F.faces), sorted((f['label'] for f in F.faces)))
