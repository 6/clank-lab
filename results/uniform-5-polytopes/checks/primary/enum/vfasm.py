"""Dimension-generic vertex-figure assembly.

The vertex figure VF of a uniform d-polytope P (unit edges, circumradius R)
is an m-polytope, m = d-1, inscribed in a sphere of radius
r = sqrt(1 - 1/(4R^2)).  Its facets are the vertex figures of P's facets
(models given as point sets in R^{m-1} with their own facets, the "ridges",
labelled by the type of the P-face they come from).  Two VF facets meet
along a ridge (the vertex figure of a (d-2)-face of P).  Around every
codimension-2 face of VF (the vertex figure of a (d-3)-face of P) the VF
facets form one of the stage-1 neighbourhood cycles of radius class R.

The search starts from one facet placed at a fixed position, repeatedly
fills an open ridge with a facet hinged across it (two flats through the
ridge at the right distance from the centre, two orientations), keeps the
figure convex, and checks every closed codimension-2 face against the
neighbourhood list.  Seeding with the least facet type present and
allowing only types at least as large makes the enumeration complete for
each radius class (every VF has a least facet type).
"""
import itertools, math
import numpy as np
TOL = 1e-06

def small_r(R):
    return math.sqrt(1 - 1 / (4 * R * R))

class Model:
    """A VF-facet model: vertices X (n x (m-1)), ridges = list of (label, vertex index tuple)."""

    def __init__(self, name, X, ridges, R_facet):
        self.name = name
        self.X = np.array(X, dtype=float)
        self.ridges = ridges
        self.R = R_facet
        self.rc = small_r(R_facet)
        X0 = self.X[0]
        A = 2 * (self.X[1:] - X0)
        b = (self.X[1:] ** 2).sum(axis=1) - (X0 ** 2).sum()
        c = np.linalg.lstsq(A, b, rcond=None)[0]
        self.X = self.X - c
        rad = np.linalg.norm(self.X, axis=1)
        if not np.max(np.abs(rad - self.rc)) < 1e-06:
            raise AssertionError((name, rad, self.rc))

def orth_complement(D, m):
    """Orthonormal basis of the orthogonal complement of span(D) in R^m."""
    if len(D) == 0:
        return np.eye(m)
    U, S, Vt = np.linalg.svd(np.array(D))
    rank = int((S > 1e-09).sum())
    return Vt[rank:]

def affine_dirs(P):
    c = P.mean(axis=0)
    U, S, Vt = np.linalg.svd(P - c)
    rank = int((S > 1e-09).sum())
    return (c, Vt[:rank])

def cyclic_order(fig, ids):
    """Order the vertices of a 2-dimensional ridge cyclically (other ridges: unchanged)."""
    if len(ids) <= 3:
        return list(ids)
    P = np.array([fig.pos[i] for i in ids])
    c, D = affine_dirs(P)
    if D.shape[0] != 2:
        return list(ids)
    Q = (P - c) @ D.T
    ang = np.arctan2(Q[:, 1], Q[:, 0])
    return [ids[i] for i in np.argsort(ang)]

def ridge_maps(model, ridx, target_pts):
    """Bijections model ridge vertices -> target points (as index permutations) that are isometries."""
    A = model.X[list(model.ridges[ridx][1])]
    k = len(A)
    DA = np.linalg.norm(A[:, None] - A[None], axis=2)
    DB = np.linalg.norm(target_pts[:, None] - target_pts[None], axis=2)
    out = []
    orders = []
    for s in range(k):
        orders.append([(s + t) % k for t in range(k)])
        orders.append([(s - t) % k for t in range(k)])
    if k <= 2:
        orders = [list(p) for p in itertools.permutations(range(k))]
    for o in orders:
        if np.max(np.abs(DA[np.ix_(o, o)] - DB)) < 1e-06:
            out.append(o)
    return out

def place_across(model, ridx, perm, target_pts, r, m):
    """Placements of model in R^m so that ridge ridx (vertices permuted by perm) lands on target_pts,
    the facet's flat at distance d from the origin.  Returns list of (points, normal, d)."""
    d = math.sqrt(max(0.0, r * r - model.rc * model.rc))
    c, D = affine_dirs(target_pts)
    W = orth_complement(D, m)
    if W.shape[0] != 2:
        return []
    x0w = W @ c
    nx = np.linalg.norm(x0w)
    if nx < d - 1e-09:
        return []
    base = x0w / nx
    perp = np.array([-base[1], base[0]])
    cosang = min(1.0, d / nx)
    sinang = math.sqrt(max(0.0, 1 - cosang * cosang))
    out = []
    A = model.X[[model.ridges[ridx][1][i] for i in perm]]
    for sgn in (1, -1):
        nw = cosang * base + sgn * sinang * perp
        n = nw @ W
        F = orth_complement([n], m)
        Bloc = (target_pts - d * n) @ F.T
        ca, cb = (A.mean(axis=0), Bloc.mean(axis=0))
        U, S, Vt = np.linalg.svd((Bloc - cb).T @ (A - ca))
        Q0 = U @ Vt
        cands = [Q0]
        _, Dm = affine_dirs(A)
        free = orth_complement(Dm, A.shape[1])
        for fv in free:
            Rf = np.eye(A.shape[1]) - 2 * np.outer(fv, fv)
            cands.append(Q0 @ Rf)
        for Q in cands:
            t = cb - Q @ ca
            if np.max(np.linalg.norm(A @ Q.T + t - Bloc, axis=1)) > 1e-06:
                continue
            Y = (model.X @ Q.T + t) @ F + d * n
            if np.max(np.abs(np.linalg.norm(Y, axis=1) - r)) > 1e-06:
                continue
            out.append((Y, n, d))
    return out

class Fig:

    def __init__(self, r, m):
        self.r, self.m = (r, m)
        self.pos = []
        self.facets = []
        self.ridges = {}

    def copy(self):
        o = Fig(self.r, self.m)
        o.pos = list(self.pos)
        o.facets = list(self.facets)
        o.ridges = {k: list(v) for k, v in self.ridges.items()}
        return o

    def vid(self, p):
        for i, q in enumerate(self.pos):
            if np.linalg.norm(p - q) < 1e-06:
                return i
        self.pos.append(p)
        return len(self.pos) - 1

def try_add(fig, model, Y, n, d):
    for p in fig.pos:
        if np.dot(n, p) > d + 1e-07:
            return None
    for _, _, n2, d2, _ in fig.facets:
        if np.linalg.norm(n2 - n) < 1e-07:
            return None
        for p in Y:
            if np.dot(n2, p) > d2 + 1e-07:
                return None
    o = fig.copy()
    ids = [o.vid(p) for p in Y]
    if len(set(ids)) != len(ids):
        return None
    fi = len(o.facets)
    rl = []
    for lab, ridx in model.ridges:
        key = frozenset((ids[i] for i in ridx))
        lst = o.ridges.setdefault(key, [])
        if lst and lst[0][1] != lab:
            return None
        lst.append((fi, lab))
        if len(lst) > 2:
            return None
        rl.append((lab, key))
    o.facets.append((model.name, ids, n, d, rl))
    return o

def codim2_faces(fig):
    """Codimension-2 faces of the figure: intersections of pairs of ridges of one facet
    that have the right dimension; returned as frozensets of vertex ids."""
    out = set()
    for _, ids, n, d, rl in fig.facets:
        keys = [k for _, k in rl]
        for a, b in itertools.combinations(keys, 2):
            s = a & b
            if len(s) >= fig.m - 2 and len(s) >= 1:
                P = np.array([fig.pos[i] for i in s])
                if len(s) == 1:
                    dim = 0
                else:
                    dim = affine_dirs(P)[1].shape[0]
                if dim == fig.m - 3:
                    out.add(frozenset(s))
    return out

def cycle_at(fig, face):
    """Cyclic sequence (facet name, label of ridge after it) around a codim-2 face if closed; None if open."""
    ridges = [k for k in fig.ridges if face <= k]
    if not ridges or any((len(fig.ridges[k]) != 2 for k in ridges)):
        return None
    adj = {}
    for k in ridges:
        (fa, la), (fb, lb) = fig.ridges[k]
        adj.setdefault(fa, []).append((k, fb, la))
        adj.setdefault(fb, []).append((k, fa, la))
    if any((len(v) != 2 for v in adj.values())):
        return None
    start = next(iter(adj))
    seq = []
    prev_ridge = adj[start][0][0]
    cur = start
    for _ in range(len(adj)):
        nxt = [x for x in adj[cur] if x[0] != prev_ridge][0]
        seq.append((fig.facets[cur][0], nxt[2]))
        prev_ridge, cur = (nxt[0], nxt[1])
    if cur != start:
        return None
    return seq

def canon_cycle(seq):
    k = len(seq)
    cands = []
    for rr in range(k):
        rot = seq[rr:] + seq[:rr]
        cands.append(tuple(rot))
        rc = [c for c, _ in reversed(rot)]
        rl = [l for _, l in reversed(rot)]
        rl = rl[1:] + rl[:1]
        cands.append(tuple(zip(rc, rl)))
    return min(cands)

def enumerate_figs(models, cycles, R, m, limit=10 ** 6):
    """models: dict name -> Model (only facet types occurring in this radius class);
    cycles: list of neighbourhood cycles [(facet name, label after)];
    returns dict signature -> representative."""
    r = small_r(R)
    allowed_all = [canon_cycle(c) for c in cycles]
    types = sorted(models)
    results = {}
    nodes = [0]
    for j, t0 in enumerate(types):
        allowed_types = set(types[j:])
        allowed = set((c for c in allowed_all if all((f in allowed_types for f, _ in c))))
        if not any((t0 in [f for f, _ in c] for c in allowed)):
            continue

        def ok(fig):
            for face in codim2_faces(fig):
                cy = cycle_at(fig, face)
                if cy is not None and canon_cycle(cy) not in allowed:
                    return False
            return True

        def search(fig):
            nodes[0] += 1
            if nodes[0] > limit:
                return
            openr = [k for k, v in fig.ridges.items() if len(v) == 1]
            if not openr:
                faces = codim2_faces(fig)
                cys = [cycle_at(fig, f) for f in faces]
                if all((c is not None and canon_cycle(c) in allowed for c in cys)):
                    sig = (tuple(sorted((f[0] for f in fig.facets))), tuple(sorted((canon_cycle(c) for c in cys))))
                    if sig not in results:
                        results[sig] = dict(count=0, pos=[p.tolist() for p in fig.pos], facets=[(f[0], list(f[1])) for f in fig.facets])
                    results[sig]['count'] += 1
                return
            key = min(openr, key=lambda k: sorted(k))
            (fi, lab), = fig.ridges[key]
            ids = cyclic_order(fig, sorted(key))
            T = np.array([fig.pos[i] for i in ids])
            tried = []
            for name in sorted(allowed_types):
                mod = models[name]
                for ridx, (lab2, rv) in enumerate(mod.ridges):
                    if lab2 != lab or len(rv) != len(ids):
                        continue
                    for perm in ridge_maps(mod, ridx, T):
                        for Y, n, d in place_across(mod, ridx, perm, T, r, m):
                            keyY = (name, tuple(sorted((tuple(np.round(y, 5)) for y in Y))))
                            if keyY in tried:
                                continue
                            tried.append(keyY)
                            o = try_add(fig, mod, Y, n, d)
                            if o is not None and ok(o):
                                search(o)
        mod = models[t0]
        d = math.sqrt(max(0.0, r * r - mod.rc * mod.rc))
        Y = np.hstack([mod.X, np.full((len(mod.X), 1), d)])
        fig = try_add(Fig(r, m), mod, Y, np.eye(m)[m - 1], d)
        if fig is not None:
            search(fig)
    return (results, nodes[0])
