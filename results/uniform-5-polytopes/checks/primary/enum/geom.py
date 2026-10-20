"""Numerical construction of uniform polytopes and their face lattices.

Floating-point exploration layer: builds vertex sets (Wythoff constructions,
snubs, products), convex hulls and face lattices, and measures the local
data the enumeration needs (circumradii, dihedral angles between the two
facets at each ridge, ...).  Certified values are recomputed elsewhere with
interval arithmetic; nothing here is trusted by a checker.
"""
import itertools
import numpy as np
from scipy.spatial import ConvexHull
TOL = 1e-07

def coxeter_matrix(name):
    """Coxeter matrix m_ij for a connected diagram name like 'A3','B4','H4','I2_5'."""
    if name.startswith('I2_'):
        p = int(name[3:])
        return np.array([[1, p], [p, 1]])
    kind, n = (name[0], int(name[1:]))
    m = np.full((n, n), 2)
    np.fill_diagonal(m, 1)
    for i in range(n - 1):
        m[i, i + 1] = m[i + 1, i] = 3
    if kind == 'A':
        pass
    elif kind == 'B':
        m[n - 2, n - 1] = m[n - 1, n - 2] = 4
    elif kind == 'D':
        m[n - 2, n - 1] = m[n - 1, n - 2] = 2
        m[n - 3, n - 1] = m[n - 1, n - 3] = 3
    elif kind == 'F':
        if not n == 4:
            raise AssertionError()
        m[1, 2] = m[2, 1] = 4
    elif kind == 'H':
        m[0, 1] = m[1, 0] = 5
    else:
        raise ValueError(name)
    return m

def mirror_normals(m):
    """Unit normals with <n_i,n_j> = -cos(pi/m_ij) (Cholesky of the Gram matrix)."""
    n = len(m)
    G = np.array([[1.0 if i == j else -np.cos(np.pi / m[i][j]) for j in range(n)] for i in range(n)])
    L = np.linalg.cholesky(G)
    return L

def block_diag_normals(blocks):
    dims = [b.shape[1] for b in blocks]
    D = sum(dims)
    rows = []
    off = 0
    for b in blocks:
        for r in b:
            v = np.zeros(D)
            v[off:off + len(r)] = r
            rows.append(v)
        off += b.shape[1]
    return np.array(rows)

def normals_for(diagram):
    """diagram: list of component names, e.g. ['B3','A1'] for a prism group."""
    blocks = []
    for comp in diagram:
        if comp == 'A1':
            blocks.append(np.array([[1.0]]))
        else:
            blocks.append(mirror_normals(coxeter_matrix(comp)))
    return block_diag_normals(blocks)

def reflect(v, n):
    return v - 2 * np.dot(v, n) * n

def orbit(seed, normals, maxsize=200000):
    key = lambda v: tuple(np.round(v, 6))
    seen = {key(seed): seed}
    frontier = [seed]
    while frontier:
        nf = []
        for v in frontier:
            for n in normals:
                w = reflect(v, n)
                k = key(w)
                if k not in seen:
                    seen[k] = w
                    nf.append(w)
        frontier = nf
        if len(seen) > maxsize:
            raise RuntimeError('orbit too large')
    return np.array(list(seen.values()))

def wythoff(diagram, rings):
    """Vertices of the Wythoffian with unit edges. rings: 0/1 per node (global order)."""
    N = normals_for(diagram)
    b = np.array([0.5 if r else 0.0 for r in rings])
    seed = np.linalg.solve(N, b)
    return orbit(seed, N)

def snub(diagram):
    """Vertices of the snub (alternated omnitruncate) with unit edges, via the
    rotation subgroup orbit of a seed chosen so that all edges are equal."""
    from scipy.optimize import least_squares
    N = normals_for(diagram)
    k = len(N)
    rots = [(i, j) for i in range(k) for j in range(i + 1, k)]

    def pts(x):
        seed = np.linalg.solve(N, x)
        return seed

    def resid(x):
        s = pts(x)
        out = []
        for i, j in rots:
            w = reflect(reflect(s, N[j]), N[i])
            out.append(np.linalg.norm(w - s) - 1.0)
        return out
    sol = least_squares(resid, np.full(k, 0.3), xtol=1e-15, ftol=1e-15)
    seed = pts(sol.x)
    key = lambda v: tuple(np.round(v, 6))
    gens = [(N[i], N[j]) for i, j in rots]
    seen = {key(seed): seed}
    fr = [seed]
    while fr:
        nf = []
        for v in fr:
            for a, c in gens:
                for w in (reflect(reflect(v, c), a), reflect(reflect(v, a), c)):
                    kk = key(w)
                    if kk not in seen:
                        seen[kk] = w
                        nf.append(w)
        fr = nf
    return np.array(list(seen.values()))

def affine_basis(P):
    c = P.mean(axis=0)
    U, S, Vt = np.linalg.svd(P - c)
    r = int((S > 1e-08).sum())
    return (c, Vt[:r])

def hull_facets(V):
    """Facets of conv(V) as sorted tuples of vertex indices (V full-dimensional)."""
    c, B = affine_basis(V)
    X = (V - c) @ B.T
    if X.shape[1] == 1:
        i, j = (np.argmin(X[:, 0]), np.argmax(X[:, 0]))
        return [(int(i),), (int(j),)]
    H = ConvexHull(X)
    facets = {}
    for eq in H.equations:
        nrm, off = (eq[:-1], eq[-1])
        on = tuple(sorted(np.where(np.abs(X @ nrm + off) < 1e-07)[0].tolist()))
        facets[on] = True
    return list(facets.keys())

class Polytope:

    def __init__(self, V, name=''):
        self.V = np.array(V, dtype=float)
        self.name = name
        self.dim = affine_basis(self.V)[1].shape[0]
        self._faces = None

    def faces(self):
        """faces[k] = list of frozensets of vertex indices of k-faces, k=0..dim-1."""
        if self._faces is not None:
            return self._faces
        d = self.dim
        F = {d - 1: set((frozenset(f) for f in hull_facets(self.V)))}
        for k in range(d - 2, -1, -1):
            nxt = set()
            for f in F[k + 1]:
                idx = sorted(f)
                if k == 0:
                    for i in idx:
                        nxt.add(frozenset([i]))
                    continue
                sub = hull_facets(self.V[idx])
                for s in sub:
                    nxt.add(frozenset((idx[i] for i in s)))
            F[k] = nxt
        self._faces = {k: sorted(F[k], key=lambda s: sorted(s)) for k in F}
        return self._faces

    def circumradius(self):
        c = self.V.mean(axis=0)
        r = np.linalg.norm(self.V - c, axis=1)
        return (r.mean(), r.max() - r.min())

    def edge_lengths(self):
        E = self.faces()[1]
        return np.array([np.linalg.norm(self.V[a] - self.V[b]) for a, b in (sorted(e) for e in E)])

    def subpolytope(self, face):
        idx = sorted(face)
        return Polytope(self.V[idx], self.name + '-face')

def polygon_type(P, face):
    return len(face)

def face_signature(P, face):
    """A cheap invariant of a face: its dimension, vertex count and circumradius."""
    sub = P.subpolytope(face)
    return (sub.dim, len(face), round(sub.circumradius()[0], 6))
