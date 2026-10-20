"""Facet templates: a uniform 4-polytope K (unit edges, centre 0) with a base
vertex, its neighbours (vertex figure VF(K)), the cells and polygons through
the base, the stabiliser of the base and, for every neighbour j of the base,
all symmetries s of K with s(base) = j.

Every template fact is certified (referee gap G-T), against the exact model
of K from its construction (tcert.py):
* neighbours: the model's vertices at exact distance 1; every other vertex
  certified at distance > 1 by intervals;
* cells: proposed in double precision, then each one certified: its vertex
  set lies in a 3-flat exactly (model.dimbound), contains four linearly
  independent points (interval inverse), every other vertex is certified off
  that hyperplane and the off-plane neighbours certified on one side (so it
  is a supporting hyperplane through the base: a cell); the cyclic order of
  its VF polygon is certified by interval orientation signs; every VF edge
  lies in exactly two certified cells (so no cell is missing: the certified
  VF facets form a closed surface, the whole VF boundary);
* polygon sizes p and cell labels: unique interval overlap, all other
  candidates certified apart; the patch radius: interval comparison;
* symmetries: the candidates (frames sent to frames) are enumerated and one
  is rejected only for a certified reason, so the accepted set contains
  every true symmetry; it must equal the exact set from the model (the
  stabiliser closure, and e_t o Stab for an exact e_t with e_t(base) = t),
  so the accepted set is exactly the set of symmetries.
"""
import math
import itertools
import numpy as np
from functools import lru_cache
from mpmath import iv
from ivla import ZERO, ONE, HALF, dot, norm2, dist2, vsub, vadd, vscale, inverse, matmul, transpose, matvec, solve, vmid
import geom
import tcert
from ivla import orth_complement_vector
GAPS = {'min_offplane': 1000000000.0, 'max_onplane': 0.0, 'templates': 0, 'cells': 0, 'rejected_gram': 0, 'rejected_orth': 0, 'rejected_vertex_local': 0, 'rejected_vertex_global': 0, 'trans_certified': 0, 'min_nonneighbour_d2': 1000000000.0}

class Undecided(Exception):
    pass

def _note_gap(on, off):
    if on is not None:
        GAPS['max_onplane'] = max(GAPS['max_onplane'], on)
    if off is not None:
        GAPS['min_offplane'] = min(GAPS['min_offplane'], off)

def _disjoint(x, y):
    return x.b < y.a or y.b < x.a

def _excl0(x):
    return x.a > 0 or x.b < 0

class Lookup:
    """float hash of a vertex set"""

    def __init__(self, Vf):
        self.Vf = Vf
        self.d = {}
        for i, v in enumerate(Vf):
            self.d.setdefault(tuple(np.floor(v * 2).astype(int)), []).append(i)
        self.dim = Vf.shape[1]
        self.r = {k.tobytes(): i for i, k in enumerate(np.round(Vf * 100000.0).astype(np.int64))}

    def find(self, x, tol=1e-07):
        c = np.floor(x * 2).astype(int)
        for d in itertools.product((-1, 0, 1), repeat=self.dim):
            for i in self.d.get(tuple(c + np.array(d)), ()):
                if np.max(np.abs(self.Vf[i] - x)) < tol:
                    return i
        return -1

    def find_all(self, W, tol=1e-07):
        """the index of a vertex within tol (max norm) of each row of W, or -1
        (a rounding dictionary first, the grid search when it misses)"""
        R = np.round(W * 100000.0).astype(np.int64)
        out = np.empty(len(W), dtype=np.int64)
        for k, (w, rk) in enumerate(zip(W, R)):
            i = self.r.get(rk.tobytes(), -1)
            if i < 0 or np.max(np.abs(self.Vf[i] - w)) >= tol:
                i = self.find(w, tol)
            out[k] = i
        return out

def isometries_vertexset(Vf, look, src, dst, nbr_src, nbr_dst, tol=1e-07):
    """all orthogonal maps s with s(Vf) = Vf, s(Vf[src]) = Vf[dst]; found via
    frames (src + 3 neighbours) -> (dst + 3 neighbours)."""
    b = Vf[src]
    best = None
    for tr in itertools.combinations(nbr_src, 3):
        M = np.array([b] + [Vf[t] for t in tr]).T
        c = abs(np.linalg.det(M))
        if best is None or c > best[0]:
            best = (c, tr)
    tr = best[1]
    Msrc = np.array([b] + [Vf[t] for t in tr]).T
    Minv = np.linalg.inv(Msrc)
    G = np.array([[np.dot(Vf[x] - b, Vf[y] - b) for y in tr] for x in tr])
    out = []
    for img in itertools.permutations(nbr_dst, 3):
        H = np.array([[np.dot(Vf[x] - Vf[dst], Vf[y] - Vf[dst]) for y in img] for x in img])
        if np.max(np.abs(G - H)) > 1e-06:
            continue
        S = np.array([Vf[dst]] + [Vf[t] for t in img]).T @ Minv
        if np.max(np.abs(S.T @ S - np.eye(len(b)))) > 1e-06:
            continue
        W = Vf @ S.T
        perm = np.empty(len(Vf), dtype=np.int32)
        ok = True
        for i, w in enumerate(W):
            k = look.find(w, tol)
            if k < 0:
                ok = False
                break
            perm[i] = k
        if ok:
            out.append((S, perm))
    return out

def isometries_cert(T, dst, nbr_dst, tol=1e-07):
    """all symmetries s of T with s(base) = dst, as (float matrix, perm).
    Candidates: the frame (base + 3 neighbours) sent to dst + 3 of nbr_dst
    (a superset of the true neighbours of dst).  The double-precision tests
    only propose; a candidate is rejected only when an interval computation
    certifies it: its frame Gram matrix differs from the base frame's, its
    matrix (exact frame correspondence) is not orthogonal, or it sends a
    vertex to a point certified apart from every vertex.  So the result
    contains every true symmetry."""
    V, Vf, look, dim = (T.V, T.Vf, T.look, T.dim)
    b = Vf[0]
    tr = (0,) + T.frame3()
    A = [[V[t][r] for t in tr] for r in range(dim)]
    Ainv = _frame_inv(T, tr, A)
    Minv = np.array([[float(x.mid) for x in row] for row in Ainv])
    G = np.array([[np.dot(Vf[x] - b, Vf[y] - b) for y in tr[1:]] for x in tr[1:]])
    Giv = None
    out = []
    for img in itertools.permutations(nbr_dst, 3):
        H = np.array([[np.dot(Vf[x] - Vf[dst], Vf[y] - Vf[dst]) for y in img] for x in img])
        D = np.abs(G - H)
        if np.max(D) > 1e-06:
            if Giv is None:
                Giv = [[dot(vsub(V[x], V[0]), vsub(V[y], V[0])) for y in tr[1:]] for x in tr[1:]]
                dif = {}
            i, j = np.unravel_index(np.argmax(D), D.shape)
            for t in (img[i], img[j]):
                if t not in dif:
                    dif[t] = vsub(V[t], V[dst])
            if not _disjoint(Giv[i][j], dot(dif[img[i]], dif[img[j]])):
                raise Undecided('frame Gram')
            GAPS['rejected_gram'] += 1
            continue
        fr = (dst,) + img
        S = np.array([Vf[t] for t in fr]).T @ Minv
        Biv = [[V[t][r] for t in fr] for r in range(dim)]
        if np.max(np.abs(S.T @ S - np.eye(dim))) > 1e-06:
            Siv = matmul(Biv, Ainv)
            StS = matmul(transpose(Siv), Siv)
            if not any((_excl0(StS[i][j] - (1 if i == j else 0)) for i in range(dim) for j in range(dim))):
                raise Undecided('orthogonality')
            GAPS['rejected_orth'] += 1
            continue
        p = look.find_all(Vf @ S.T, tol)
        if np.min(p) < 0:
            i = int(np.argmin(p))
            _certify_not_vertex(T, matvec(matmul(Biv, Ainv), V[i]))
            continue
        out.append((S, p))
    return out

def _certify_not_vertex(T, y):
    """y (an interval point) is certified apart from every vertex of T.
    Vertices with some coordinate of the double midpoint 0.5 or more away
    from y's are apart by the coordinate lemma (README): with coordinate
    magnitude at most 64 and enclosure width below 1e-6, midpoint conversion
    error is bounded by 1e-6 + 2^-53 * 64 < 1.1e-6. Twice this bound is
    below the 0.5 separation cutoff. The remaining vertices use intervals.
    """
    if not (max((float(c.delta) for c in y)) < 1e-06 and T.coord_ok):
        raise AssertionError()
    yf = np.array(vmid(y))
    near = np.where(np.max(np.abs(T.Vf - yf), axis=1) < 0.5)[0]
    for i in near:
        d = dist2(y, T.V[i])
        if d.a > 0 and d.b < 0.25:
            GAPS['rejected_vertex_local'] += 1
            return
    if all((dist2(y, T.V[i]).a > 0 for i in near)):
        GAPS['rejected_vertex_global'] += 1
        return
    raise Undecided('image of a vertex')
PATCH_T = iv.mpf(4) + iv.mpf('1e-9')
CP = {p: 2 * iv.cos(iv.pi / p) for p in range(3, 65)}

class Template:

    def __init__(self, name, V=None):
        self.name = name
        if V is None:
            V = geom.polytope4(name)
        self.V = V
        self.n = len(V)
        self.Vf = np.array([[float(c.mid) for c in v] for v in V])
        self.coord_ok = np.max(np.abs(self.Vf)) <= 64 and max((float(c.delta) for v in V for c in v)) < 1e-20
        if not self.coord_ok:
            raise AssertionError(name)
        self.look = Lookup(self.Vf)
        self.R2 = norm2(V[0])
        self.R = iv.sqrt(self.R2)
        self.dim = len(V[0])
        self.model = tcert.model4(name)
        if not self.model.n == self.n:
            raise AssertionError(name)
        b = self.Vf[0]
        d2f = np.sum((self.Vf - b) ** 2, axis=1)
        self.nb = sorted(self.model.nbrs())
        nbset = set(self.nb)
        if not self.nb == [int(i) for i in np.where(np.abs(d2f - 1) < 1e-09)[0]]:
            raise AssertionError(name)
        patch = []
        for i, v in enumerate(V):
            dd = dist2(V[0], v)
            if i and i not in nbset:
                if not dd.a > 1:
                    raise AssertionError((name, i))
                GAPS['min_nonneighbour_d2'] = min(GAPS['min_nonneighbour_d2'], float(dd.a))
            if dd.b < PATCH_T.a:
                patch.append(i)
            elif not dd.a > PATCH_T.b:
                raise AssertionError((name, i))
        self.patch = patch
        self._adj = {}
        self._cells()
        self._polys()
        self._syms()
        GAPS['templates'] += 1

    def nbrs_of(self, i):
        """the exact neighbours of vertex i: e(neighbours of the base) for an
        exact symmetry e with e(base) = i"""
        if i not in self._adj:
            e = self.model.elem_to(i)
            self._adj[i] = sorted((int(e[k]) for k in self.nb))
        return self._adj[i]

    def _cells(self):
        Vf = self.Vf
        b = Vf[0]
        nb = self.nb
        nbset = set(nb)
        faces = {}
        for tr in itertools.combinations(nb, 3):
            M = np.array([Vf[t] - b for t in tr])
            _, s, vt = np.linalg.svd(M)
            if s[-1] < 1e-06:
                continue
            nrm = vt[-1]
            vals = np.array([np.dot(Vf[t] - b, nrm) for t in nb])
            if np.all(vals > -1e-09) or np.all(vals < 1e-09):
                on = frozenset((t for t, v in zip(nb, vals) if abs(v) < 1e-09))
                if on not in faces:
                    faces[on] = nrm
        cells = []
        for on, nrm in sorted(faces.items(), key=lambda kv: sorted(kv[0])):
            vals = (Vf - b) @ nrm
            verts = [int(i) for i in np.where(np.abs(vals) < 1e-09)[0]]
            offs = np.abs(vals[np.abs(vals) >= 1e-09])
            _note_gap(float(np.max(np.abs(vals[verts]))), float(offs.min()) if len(offs) else None)
            pts = [t for t in nb if t in on]
            cen = np.mean([Vf[t] for t in pts], axis=0)
            e1 = Vf[pts[0]] - cen
            e1 /= np.linalg.norm(e1)
            M = np.array([Vf[t] - cen for t in pts])
            _, _, vt = np.linalg.svd(M)
            e2 = vt[1] - np.dot(vt[1], e1) * e1
            if np.linalg.norm(e2) < 1e-06:
                e2 = vt[0] - np.dot(vt[0], e1) * e1
            e2 /= np.linalg.norm(e2)
            ang = {t: math.atan2(np.dot(Vf[t] - cen, e2), np.dot(Vf[t] - cen, e1)) for t in pts}
            poly = sorted(pts, key=lambda t: ang[t])
            self._certify_cell(frozenset(verts), poly, nbset)
            nvc = len(verts)
            cc = [sum((self.V[i][k] for i in verts), ZERO) / nvc for k in range(self.dim)]
            RC2 = dist2(cc, self.V[0])
            label = cell_label(nvc, RC2)
            cpatch = [i for i in verts if i in set(self.patch)]
            cells.append({'label': label, 'verts': verts, 'poly': poly, 'centre': cc, 'RC2': RC2, 'patch': cpatch, 'normal': nrm})
        self.cells = cells
        self.cellkey = {frozenset(c['poly']): k for k, c in enumerate(cells)}
        for c in cells:
            P = c['poly']
            Y = [[self.V[t][r] for t in (0, P[0], P[1], P[2])] for r in range(self.dim)]
            c['Yinv'] = inverse(Y)

    def _certify_cell(self, S, poly, nbset):
        """S (vertex indices) is the vertex set of a cell through the base and
        poly the cyclic order of its VF polygon."""
        V = self.V
        name = self.name
        if not (0 in S and set(poly) == S & nbset):
            raise AssertionError(name)
        if not self.model.dimbound(S) <= 3:
            raise AssertionError((name, sorted(S)))
        b = V[0]
        nrm = orth_complement_vector([vsub(V[t], b) for t in poly[:3]])
        side = None
        for i in range(self.n):
            if i in S:
                continue
            val = dot(vsub(V[i], b), nrm)
            if not _excl0(val):
                raise AssertionError((name, i))
            if i in nbset:
                sd = val.a > 0
                if not (side is None or side == sd):
                    raise AssertionError((name, 'not supporting'))
                side = sd
        k = len(poly)
        pts = [V[t] for t in poly]
        c = [sum((p[r] for p in pts), ZERO) / k for r in range(self.dim)]
        e1 = vsub(pts[0], c)
        pf = [np.array(vmid(vsub(p, c))) for p in pts]
        e1f = pf[0] / np.linalg.norm(pf[0])
        j = min(range(1, k), key=lambda m: abs(np.dot(pf[m], e1f)) / np.linalg.norm(pf[m]))
        w = vsub(pts[j], c)
        e2 = vsub(w, vscale(dot(w, e1) / dot(e1, e1), e1))
        xy = [(dot(vsub(p, c), e1), dot(vsub(p, c), e2)) for p in pts]
        sgn = None
        for a_ in range(k):
            b_ = (a_ + 1) % k
            (xa, ya), (xb, yb) = (xy[a_], xy[b_])
            for m in range(k):
                if m in (a_, b_):
                    continue
                xm, ym = xy[m]
                cr = (xb - xa) * (ym - ya) - (yb - ya) * (xm - xa)
                if not _excl0(cr):
                    raise AssertionError((name, 'polygon order undecided'))
                sd = cr.a > 0
                if not (sgn is None or sgn == sd):
                    raise AssertionError((name, 'polygon order'))
                sgn = sd
        GAPS['cells'] += 1

    def _polys(self):
        """polygons through the base: neighbour pairs consecutive in some
        cell polygon; their size, cells and dihedral angle."""
        polys = {}
        for ci, c in enumerate(self.cells):
            P = c['poly']
            for k in range(len(P)):
                a, b = (P[k], P[(k + 1) % len(P)])
                key = frozenset((a, b))
                polys.setdefault(key, []).append(ci)
        out = {}
        for key, cl in polys.items():
            if not len(cl) == 2:
                raise AssertionError((self.name, key, cl))
            a, b = sorted(key)
            d = iv.sqrt(dist2(self.V[a], self.V[b]))
            hit = [p for p, cp in CP.items() if not _disjoint(cp, d)]
            if not len(hit) == 1:
                raise AssertionError((self.name, key, hit))
            p = hit[0]
            out[key] = {'p': p, 'cells': cl, 'alpha': self._dihedral(a, b, cl)}
        self.polys = out

    def _dihedral(self, a, b, cl):
        """interval dihedral angle of K at the polygon (base, a, b) between
        the two cells cl."""
        V = self.V
        base = V[0]
        from ivla import gram_schmidt
        u1, u2 = gram_schmidt([vsub(V[a], base), vsub(V[b], base)])
        dirs = []
        for ci in cl:
            cc = self.cells[ci]['centre']
            w = vsub(cc, base)
            w = vsub(w, vscale(dot(w, u1), u1))
            w = vsub(w, vscale(dot(w, u2), u2))
            nw = iv.sqrt(norm2(w))
            dirs.append([x / nw for x in w])
        cosang = dot(dirs[0], dirs[1])
        from ivla import iacos
        return iacos(cosang)

    def _syms(self):
        stab = isometries_cert(self, 0, self.nb)
        exact = self.model.stab()
        if not {tcert.key(tcert.perm(p)) for _, p in stab} == {tcert.key(g) for g in exact}:
            raise AssertionError((self.name, 'stabiliser', len(stab), len(exact)))
        if not len(stab) == len(exact):
            raise AssertionError()
        self.stab_np = stab
        self.stab_perm = [p for S, p in stab]
        self.stab = [self._ivmat(S, 0, 0, p) for S, p in stab]
        self.trans = {}
        self.trans_perm = {}
        for j in self.nb:
            self._trans_to(j)

    def _trans_to(self, j):
        """all symmetries with s(base) = j: the certified candidates must be
        exactly e_j o Stab (e_j exact from the model)"""
        if j in self.trans:
            return
        res = isometries_cert(self, j, self.nbrs_of(j))
        e = self.model.elem_to(j)
        want = {tcert.key(tcert.compose(e, g)) for g in self.model.stab()}
        if not ({tcert.key(tcert.perm(p)) for _, p in res} == want and len(res) == len(want)):
            raise AssertionError((self.name, j, len(res), len(want)))
        GAPS['trans_certified'] += 1
        self.trans[j] = [self._ivmat(S, 0, j, p) for S, p in res]
        self.trans_perm[j] = [p for S, p in res]

    def sym_to(self, t):
        """all symmetries s with s(base) = t (for development)."""
        self._trans_to(t)
        return (self.trans[t], self.trans_perm[t])

    def frame3(self):
        """three neighbours of the base with a well conditioned frame"""
        if not hasattr(self, '_frame3'):
            b = self.Vf[0]
            best = None
            for tr in itertools.combinations(self.nb, 3):
                M = np.array([b] + [self.Vf[t] for t in tr]).T
                c = abs(np.linalg.det(M))
                if best is None or c > best[0]:
                    best = (c, tr)
            self._frame3 = best[1]
        return self._frame3

    def _ivmat(self, S, src, dst, perm):
        """interval matrix of the symmetry: S = [img frame] [src frame]^-1
        computed in interval arithmetic from the exact frame correspondence."""
        V = self.V
        tr = (src,) + self.frame3()
        A = [[V[t][r] for t in tr] for r in range(self.dim)]
        B = [[V[int(perm[t])][r] for t in tr] for r in range(self.dim)]
        Mi = _frame_inv(self, tr, A)
        return matmul(B, Mi)

    def nbr_index(self):
        return {t: k for k, t in enumerate(self.nb)}
_FRAME_INV = {}

def _frame_inv(T, tr, A):
    k = (T.name, tr)
    if k not in _FRAME_INV:
        _FRAME_INV[k] = inverse(A)
    return _FRAME_INV[k]
CELL_TABLE = None

def cell_label(n, RC2):
    """label of a cell with n vertices and squared circumradius in RC2: the
    cell is a uniform polyhedron with unit edges, i.e. one of the table's
    polyhedra (Platonic, Archimedean, prisms and antiprisms up to 40 sides);
    exactly one entry with n vertices may meet RC2, all others are certified
    apart."""
    global CELL_TABLE
    if CELL_TABLE is None:
        tab = []
        for lab, V in geom.poly3_table().items():
            tab.append((lab, len(V), norm2(V[0])))
        for k in range(3, 41):
            if k != 4:
                V = geom.prism3(k)
                tab.append(('P%d' % k, len(V), norm2(V[0])))
            if k != 3:
                V = geom.antiprism(k)
                tab.append(('A%d' % k, len(V), norm2(V[0])))
        CELL_TABLE = tab
    hit = [l for l, k, r2 in CELL_TABLE if k == n and (not _disjoint(r2, RC2))]
    if not len(hit) == 1:
        raise AssertionError((n, RC2, hit))
    return hit[0]
_CACHE = {}

def template(name):
    if name not in _CACHE:
        _CACHE[name] = Template(name)
    return _CACHE[name]
