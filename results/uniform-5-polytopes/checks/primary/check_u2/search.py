"""Stage-2 independent checker: all vertex figures of a radius class.

Gluing search.  A vertex figure VF is a convex 4-polytope inscribed in the
3-sphere of radius r = sqrt(1 - 1/(4R^2)); its facets are copies of VF(K),
each in a hyperplane at distance d_K = sqrt(r^2 - r_K^2) from the centre.
(The centre is strictly inside VF: it is the projection of P's centre, which
is strictly inside every facet half-space of P.)  Two facets meeting at a
ridge (cell label c) are related rigidly: the ridge polygon sits at distance
d_c = sqrt(r^2 - rho_c^2) from the centre, and the facet normals make angles
alpha with cos alpha = d_K / d_c, sin alpha = h / d_c (h = distance in VF(K)
from its centre to the face) on opposite sides of the ridge direction u.
So once a facet is placed, a neighbour across a ridge is fixed by the choice
of (type K', face f of VF(K') with label c, vertex correspondence of f with
the ridge preserving edge types).  The search places a first facet in
standard position and glues neighbours across open ridges until none is
left, discarding a branch only on

  * an interval proof that two vertices are at distance in (0, 1)
    (separation lemma),
  * an interval proof that a vertex lies strictly outside a facet
    hyperplane (convexity),
  * a combinatorial contradiction: two facets whose common vertex set is
    not a common face of both (empty, a vertex, an edge, a 2-face), a ridge
    in more than two facets, inconsistent cell labels, or a partial
    sequence of facets around a VF-edge that is not a factor of an allowed
    cycle (a closed one not an allowed cycle).

Vertices are identified only when an interval proves their distance < 1/2
(then they are equal, by the separation lemma).  All geometry is in
mpmath.iv interval arithmetic.
"""
import json, sys, time
from mpmath import iv, mp, mpf
from facets import build_facet, sub as msub, dot as mdot, norm as mnorm, BUILD_PREC, TOL
IV_PREC = 200
import os
FILTER = os.environ.get('U2_FILTER', '1') != '0'
NOSYM = os.environ.get('U2_NOSYM', '0') == '1'
FIRST = os.environ.get('U2_FIRST', '0') == '1'
NOEXCL = os.environ.get('U2_NOEXCL', '0') == '1'
iv.prec = IV_PREC
ENCL = mpf(2) ** (-(BUILD_PREC - 64))
QUARTER = iv.mpf(1) / 4

def enc(x):
    """Interval enclosure of a 512-bit facet constant."""
    if isinstance(x, type(iv.mpf(0))):
        return x
    x = mpf(x)
    e = ENCL * (1 + abs(x))
    with mp.workprec(BUILD_PREC):
        return iv.mpf([mp.mpf(x - e), mp.mpf(x + e)])

def ivdot(a, b):
    s = a[0] * b[0]
    for i in range(1, len(a)):
        s += a[i] * b[i]
    return s

def lin(cs, vs):
    """sum_k cs[k] * vs[k] for 4-vectors."""
    out = []
    for t in range(4):
        s = cs[0] * vs[0][t]
        for k in range(1, len(cs)):
            s += cs[k] * vs[k][t]
        out.append(s)
    return tuple(out)

def vsub(a, b):
    return tuple((x - y for x, y in zip(a, b)))

def vscal(c, a):
    return tuple((c * x for x in a))

class LegacyTypeData:
    """R-independent data of VF(K), enclosed in intervals."""

    def __init__(self, name):
        F = build_facet(name)
        self.name = name
        self.nv = len(F.verts)
        self.R2 = F.R2
        self.rK2 = enc(F.rK2)
        self.verts = [tuple((enc(c) for c in p)) for p in F.verts]
        self.faces = []
        self.edge_faces = {}
        self.edge_p = dict(F.edge_p)
        for fi, f in enumerate(F.faces):
            vs = f['verts']
            m = len(vs)
            x0, x1, x2 = (F.verts[vs[0]], F.verts[vs[1]], F.verts[vs[2]])
            e1 = msub(x1, x0)
            L1 = mnorm(e1)
            t1 = [c / L1 for c in e1]
            w2 = msub(x2, x0)
            pr = mdot(w2, t1)
            w2 = [a - pr * b for a, b in zip(w2, t1)]
            L2 = mnorm(w2)
            self.faces.append({'verts': list(vs), 'label': f['label'], 'ps': list(f['ps']), 'h': enc(f['h']), 'L1': enc(L1), 'L2': enc(L2), 'normal': f['normal'], 'vset': frozenset(vs)})
            for a in range(m):
                k = frozenset((vs[a], vs[(a + 1) % m]))
                self.edge_faces.setdefault(k, []).append(fi)
        for k, v in self.edge_faces.items():
            if not len(v) == 2:
                raise AssertionError()
        self.edges = list(self.edge_faces.keys())
        fs = {frozenset()}
        fs |= {frozenset([i]) for i in range(self.nv)}
        fs |= set(self.edges)
        fs |= {f['vset'] for f in self.faces}
        self.face_vsets = fs
        self.face_of_vset = {f['vset']: fi for fi, f in enumerate(self.faces)}
        self.corr = []
        for fi, f in enumerate(F.faces):
            vs = f['verts']
            m = len(vs)
            lst = []
            for s in range(m):
                for dr in (1, -1):
                    order = [vs[(s + dr * i) % m] for i in range(m)]
                    ps = tuple((self.edge_p[frozenset((order[i], order[(i + 1) % m]))] for i in range(m)))
                    x0, x1, x2 = (F.verts[order[0]], F.verts[order[1]], F.verts[order[2]])
                    e1 = msub(x1, x0)
                    t1 = [c / mnorm(e1) for c in e1]
                    w2 = msub(x2, x0)
                    pr = mdot(w2, t1)
                    w2 = [a - pr * b for a, b in zip(w2, t1)]
                    t2 = [c / mnorm(w2) for c in w2]
                    t3 = f['normal']
                    coef = [(enc(mdot(p, t1)), enc(mdot(p, t2)), enc(mdot(p, t3))) for p in F.verts]
                    other = []
                    for i in range(m):
                        k = frozenset((order[i], order[(i + 1) % m]))
                        a, b = self.edge_faces_raw(F, k)
                        g = b if a == fi else a
                        other.append(F.faces[g]['label'])
                    lst.append({'order': order, 'ps': ps, 'coef': coef, 'other': tuple(other)})
            self.corr.append(lst)
        self.syms = symmetries(F, self.corr)
        idx = {(gf, tuple(c['order'])): (gf, ci) for gf in range(len(self.corr)) for ci, c in enumerate(self.corr[gf])}
        self.idx = idx
        for gf in range(len(self.corr)):
            for ci, c in enumerate(self.corr[gf]):
                orb = set()
                for g in self.syms:
                    o2 = tuple((g[v] for v in c['order']))
                    fs = frozenset(o2)
                    gf2 = self.face_of_vset[fs]
                    orb.add(idx[gf2, o2])
                c['rep'] = min(orb) == (gf, ci)
                c['orbit'] = orb

    def edge_faces_raw(self, F, k):
        return self.edge_faces[k]

def symmetries(F, corr):
    """Vertex permutations of VF(K) induced by its isometries (checked at
    512 bits: every vertex maps to a vertex within 2^-300)."""

    def frame(order, normal):
        x0, x1, x2 = (F.verts[order[0]], F.verts[order[1]], F.verts[order[2]])
        e1 = msub(x1, x0)
        t1 = [c / mnorm(e1) for c in e1]
        w2 = msub(x2, x0)
        pr = mdot(w2, t1)
        w2 = [a - pr * b for a, b in zip(w2, t1)]
        t2 = [c / mnorm(w2) for c in w2]
        return [t1, t2, list(normal)]
    ref = corr[0][0]
    A = frame(ref['order'], F.faces[0]['normal'])
    lab0 = F.faces[0]['label']
    out = []
    for gf in range(len(corr)):
        if F.faces[gf]['label'] != lab0:
            continue
        for c in corr[gf]:
            if c['ps'] != ref['ps']:
                continue
            B = frame(c['order'], F.faces[gf]['normal'])
            perm = []
            for x in F.verts:
                co = [mdot(x, a) for a in A]
                y = [sum((co[k] * B[k][t] for k in range(3))) for t in range(3)]
                hit = [j for j, z in enumerate(F.verts) if mnorm(msub(y, z)) < TOL]
                if len(hit) != 1:
                    perm = None
                    break
                perm.append(hit[0])
            if perm is not None:
                out.append(tuple(perm))
    if not tuple(range(len(F.verts))) in out:
        raise AssertionError()
    return out

def alt_seq(cy):
    s = []
    for K, c in zip(cy['facets'], cy['cells']):
        s += [K, c]
    return s

def canon_word(word):
    """word: list of (K, c); least over rotations and reversals."""
    n = len(word)
    best = None
    rev = [(word[(n - 1 - i) % n][0], word[(n - 2 - i) % n][1]) for i in range(n)]
    for w in (word, rev):
        for s in range(n):
            cand = [list(w[(s + i) % n]) for i in range(n)]
            if best is None or cand < best:
                best = cand
    return best

class CycleSet:

    def __init__(self, cycles):
        self.factors = {}
        self.closed = {}
        self.maxlen = {}
        for cy in cycles:
            p = cy['p']
            S = alt_seq(cy)
            n = len(cy['facets'])
            self.maxlen[p] = max(self.maxlen.get(p, 0), n)
            fs = self.factors.setdefault(p, set())
            for seq in (S, S[::-1]):
                L = len(seq)
                for st in range(L):
                    if not is_label_pos(seq, st, S):
                        continue
                    for k in range(0, n + 1):
                        fs.add(tuple((seq[(st + i) % L] for i in range(2 * k + 1))))
            word = list(zip(cy['facets'], cy['cells']))
            self.closed.setdefault(p, set()).add(json.dumps(canon_word(word)))

def is_label_pos(seq, st, S):
    if seq is S:
        return st % 2 == 1
    return st % 2 == 0

class Prune(Exception):
    pass

class PrecisionError(Exception):
    pass

class Facet:
    __slots__ = ('T', 'gids', 'n', 'd', 'partner', 'cls')

class ClassSearch:

    def __init__(self, cls, types_all, log=None, node_limit=None):
        self.cls = cls
        self.log = log
        self.node_limit = node_limit
        R = iv.mpf([cls['R'][0], cls['R'][1]])
        self.r2 = 1 - 1 / (4 * R * R)
        self.inv4R2 = 1 / (4 * R * R)
        names = sorted(set((K for cy in cls['cycles'] for K in cy['facets'])))
        self.types = {nm: types_all[nm] for nm in names}
        self.geo = {}
        self.too_big = set()
        for nm, T in list(self.types.items()):
            dK2 = 1 / (4 * enc(T.R2)) - self.inv4R2
            if dK2.b <= 0:
                self.too_big.add(nm)
                del self.types[nm]
                continue
            if not dK2.a > 0:
                dK2 = iv.mpf([0, dK2.b])
            dK = iv.sqrt(dK2)
            fg = []
            for f in T.faces:
                rho2 = T.rK2 - f['h'] * f['h']
                dc = iv.sqrt(self.r2 - rho2)
                fg.append((dc, dK / dc, f['h'] / dc))
            self.geo[nm] = (dK, fg)
        self.stats = {'nodes': 0, 'placements': 0, 'geo_prunes': 0, 'comb_prunes': 0, 'completions': 0}
        self.found = {}
        self.uncertified = set()

    def run(self):
        names = sorted(self.types)
        for i, start in enumerate(names):
            allowed = set(names if NOEXCL else names[i:])
            cycles = [cy for cy in self.cls['cycles'] if set(cy['facets']) <= allowed]
            allowed = self.usable_types(allowed, cycles)
            if start not in allowed:
                continue
            cycles = [cy for cy in cycles if set(cy['facets']) <= allowed]
            self.allowed = sorted(allowed)
            self.cs = CycleSet(cycles)
            self.start_search(start)
        return self.found

    def usable_types(self, allowed, cycles):
        """Drop types with an edge whose single-facet word occurs in no cycle."""
        allowed = set(allowed)
        while True:
            cs = CycleSet([cy for cy in cycles if set(cy['facets']) <= allowed])
            bad = set()
            for nm in allowed:
                T = self.types[nm]
                for e, (fa, fb) in T.edge_faces.items():
                    p = T.edge_p[e]
                    w = (T.faces[fa]['label'], nm, T.faces[fb]['label'])
                    if w not in cs.factors.get(p, ()):
                        bad.add(nm)
                        break
            if not bad:
                return allowed
            allowed -= bad

    def start_search(self, start):
        T = self.types[start]
        dK, _ = self.geo[start]
        self.verts = []
        self.vert_facets = []
        self.facets = []
        self.edge_index = {}
        self.open = set()
        coords = [(p[0], p[1], p[2], dK) for p in T.verts]
        G = Facet()
        G.T = T
        G.gids = list(range(T.nv))
        G.n = (iv.mpf(0), iv.mpf(0), iv.mpf(0), iv.mpf(1))
        G.d = dK
        G.partner = [None] * len(T.faces)
        self.apply(G, coords, [])
        self.recurse()

    def apply(self, G, new_coords, glues):
        fidx = len(self.facets)
        undo = {'nverts': len(self.verts), 'glues': glues, 'fidx': fidx}
        for c in new_coords:
            self.verts.append(c)
            self.vert_facets.append([])
        self.facets.append(G)
        for g in G.gids:
            self.vert_facets[g].append(fidx)
        for e in G.T.edges:
            k = frozenset((G.gids[i] for i in e))
            self.edge_index.setdefault(k, []).append(fidx)
        for F, phi, gf in glues:
            self.facets[F].partner[phi] = (fidx, gf)
            G.partner[gf] = (F, phi)
            self.open.discard((F, phi))
        for gf in range(len(G.T.faces)):
            if G.partner[gf] is None:
                self.open.add((fidx, gf))
        return undo

    def undo(self, u):
        fidx = u['fidx']
        G = self.facets[fidx]
        for gf in range(len(G.T.faces)):
            self.open.discard((fidx, gf))
        for F, phi, gf in u['glues']:
            self.facets[F].partner[phi] = None
            G.partner[gf] = None
            self.open.add((F, phi))
        for e in G.T.edges:
            k = frozenset((G.gids[i] for i in e))
            lst = self.edge_index[k]
            lst.pop()
            if not lst:
                del self.edge_index[k]
        for g in G.gids:
            self.vert_facets[g].pop()
        self.facets.pop()
        del self.verts[u['nverts']:]
        del self.vert_facets[u['nverts']:]

    def edge_chain(self, key):
        """Components of the facets around VF-edge `key`: list of
        ('cycle', word) or ('path', alt-tuple)."""
        fl = self.edge_index[key]
        seen = set()
        comps = []
        for f0 in fl:
            if f0 in seen:
                continue
            comp = self.walk(key, f0)
            for f, _, _ in comp[1]:
                seen.add(f)
            comps.append(comp)
        return comps

    def faces_at(self, F, key):
        Fa = self.facets[F]
        loc = frozenset((Fa.gids.index(g) for g in key))
        return Fa.T.edge_faces[loc]

    def walk(self, key, f0):
        """Return ('cycle', [(K, c)...]) or ('path', [(f, in_face, out_face)...])."""
        fa, fb = self.faces_at(f0, key)
        cur, entry = (f0, fb)
        start, start_in = (f0, fa)
        steps = 0
        while True:
            p = self.facets[start].partner[start_in]
            if p is None:
                break
            nf, nface = p
            a, b = self.faces_at(nf, key)
            nin = b if nface == a else a
            start, start_in = (nf, nin)
            steps += 1
            if start == f0:
                break
            if steps > 1000:
                raise RuntimeError('walk loop')
        closed = start == f0 and steps > 0
        seq = []
        cur, cin = (start, start_in)
        while True:
            a, b = self.faces_at(cur, key)
            cout = b if cin == a else a
            seq.append((cur, cin, cout))
            p = self.facets[cur].partner[cout]
            if p is None:
                break
            nf, nface = p
            if nf == start and closed:
                break
            cur, cin = (nf, nface)
            if len(seq) > 1000:
                raise RuntimeError('walk loop 2')
        return ('cycle' if closed else 'path', seq)

    def check_edge(self, key):
        fl = self.edge_index[key]
        F0 = self.facets[fl[0]]
        loc = [F0.gids.index(g) for g in key]
        p = F0.T.edge_p[frozenset(loc)]
        if p not in self.cs.factors:
            raise Prune('p')
        comps = self.edge_chain(key)
        if len(fl) > self.cs.maxlen[p]:
            raise Prune('too many facets at edge')
        for kind, seq in comps:
            if kind == 'cycle':
                if len(comps) > 1:
                    raise Prune('cycle plus more')
                word = []
                for f, cin, cout in seq:
                    Fa = self.facets[f]
                    word.append((Fa.T.name, Fa.T.faces[cout]['label']))
                if json.dumps(canon_word(word)) not in self.cs.closed[p]:
                    raise Prune('closed cycle not allowed')
            else:
                alt = []
                for f, cin, cout in seq:
                    Fa = self.facets[f]
                    if not alt:
                        alt.append(Fa.T.faces[cin]['label'])
                    alt.append(Fa.T.name)
                    alt.append(Fa.T.faces[cout]['label'])
                if tuple(alt) not in self.cs.factors[p]:
                    raise Prune('path not a factor')
        return p

    def ridge_paths(self, F, phi):
        """For each edge of open face phi of facet F (in face order), the
        alternating word of the path through F starting at the open face."""
        Fa = self.facets[F]
        f = Fa.T.faces[phi]
        vs = f['verts']
        m = len(vs)
        out = []
        for a in range(m):
            key = frozenset((Fa.gids[vs[a]], Fa.gids[vs[(a + 1) % m]]))
            kind, seq = self.walk_from(key, F, phi)
            out.append((key, f['ps'][a], seq))
        return out

    def walk_from(self, key, F, phi):
        alt = [self.facets[F].T.faces[phi]['label']]
        cur, cin = (F, phi)
        n = 0
        while True:
            Fa = self.facets[cur]
            a, b = self.faces_at(cur, key)
            cout = b if cin == a else a
            alt.append(Fa.T.name)
            alt.append(Fa.T.faces[cout]['label'])
            p = Fa.partner[cout]
            if p is None:
                break
            cur, cin = p
            n += 1
            if n > 1000:
                raise RuntimeError('walk_from loop')
        return ('path', tuple(alt))

    def candidates(self, F, phi):
        Fa = self.facets[F]
        f = Fa.T.faces[phi]
        label = f['label']
        rps = tuple(f['ps'])
        paths = self.ridge_paths(F, phi)
        out = []
        for nm in self.allowed:
            T = self.types[nm]
            for gf, g in enumerate(T.faces):
                if g['label'] != label:
                    continue
                for ci, c in enumerate(T.corr[gf]):
                    if c['ps'] != rps or not (c['rep'] or NOSYM):
                        continue
                    ok = True
                    for a, (key, p, alt) in enumerate(paths if FILTER else ()):
                        w = (c['other'][a], nm) + alt
                        fs = self.cs.factors.get(p)
                        if fs is None or w not in fs:
                            ok = False
                            break
                    if ok:
                        out.append((nm, gf, ci))
        return out

    def place(self, F, phi, nm, gf, ci):
        """Place facet of type nm across ridge (F, phi), face gf, corr ci.
        Returns (Facet, new_coords, glues) or raises Prune."""
        Fa = self.facets[F]
        TF = Fa.T
        fF = TF.faces[phi]
        rv = [Fa.gids[i] for i in fF['verts']]
        Q0, Q1, Q2 = (self.verts[rv[0]], self.verts[rv[1]], self.verts[rv[2]])
        T1 = vscal(1 / fF['L1'], vsub(Q1, Q0))
        w2 = vsub(Q2, Q0)
        w2 = vsub(w2, vscal(ivdot(w2, T1), T1))
        T2 = vscal(1 / fF['L2'], w2)
        cr = vsub(Q0, lin([ivdot(Q0, T1), ivdot(Q0, T2)], [T1, T2]))
        dKF, fgF = self.geo[TF.name]
        dc, cosF, sinF = fgF[phi]
        u = vscal(1 / dc, cr)
        w = vscal(1 / sinF, vsub(Fa.n, vscal(cosF, u)))
        T = self.types[nm]
        dG, fgG = self.geo[nm]
        dc2, cosG, sinG = fgG[gf]
        nG = lin([cosG, -sinG], [u, w])
        h = T.faces[gf]['h']
        T3 = vscal(1 / h, vsub(cr, vscal(dG, nG)))
        c = T.corr[gf][ci]
        order = c['order']
        loc2g = [None] * T.nv
        for i, lv in enumerate(order):
            loc2g[lv] = rv[i]
        nverts = len(self.verts)
        new_coords = []
        used = set(rv)
        newpts = []
        for j in range(T.nv):
            if loc2g[j] is not None:
                continue
            a1, a2, a3 = c['coef'][j]
            x = lin([a1, a2, a3, dG], [T1, T2, T3, nG])
            ident = None
            for gi in range(nverts):
                y = self.verts[gi]
                d2 = 2 * self.r2 - 2 * ivdot(x, y)
                if d2.b < 1 and d2.a > 0:
                    self.stats['geo_prunes'] += 1
                    raise Prune('separation')
                if d2.b < QUARTER:
                    if ident is not None:
                        raise PrecisionError('two identifications')
                    ident = gi
                elif d2.a <= 0:
                    raise PrecisionError('wide distance interval %s' % d2)
            if ident is not None:
                if ident in used:
                    self.stats['comb_prunes'] += 1
                    raise Prune('vertex used twice')
                used.add(ident)
                loc2g[j] = ident
            else:
                for Fb in self.facets:
                    s = ivdot(Fb.n, x) - Fb.d
                    if s.a > 0:
                        self.stats['geo_prunes'] += 1
                        raise Prune('outside facet')
                loc2g[j] = nverts + len(new_coords)
                new_coords.append(x)
                newpts.append(x)
        gset = set(loc2g)
        for gi in range(nverts):
            if gi in gset:
                continue
            s = ivdot(nG, self.verts[gi]) - dG
            if s.a > 0:
                self.stats['geo_prunes'] += 1
                raise Prune('outside new facet')
        g2l = {g: i for i, g in enumerate(loc2g)}
        others = {}
        for g in gset:
            if g < nverts:
                for fb in self.vert_facets[g]:
                    others.setdefault(fb, set()).add(g)
        glues = []
        gface_used = set()
        for fb, S in others.items():
            Fb = self.facets[fb]
            locB = frozenset((Fb.gids.index(g) for g in S))
            locG = frozenset((g2l[g] for g in S))
            if locB not in Fb.T.face_vsets or locG not in T.face_vsets:
                self.stats['comb_prunes'] += 1
                raise Prune('common vertices not a face')
            if len(S) >= 3:
                fbi = Fb.T.face_of_vset[locB]
                gfi = T.face_of_vset[locG]
                if Fb.T.faces[fbi]['label'] != T.faces[gfi]['label']:
                    self.stats['comb_prunes'] += 1
                    raise Prune('label')
                if Fb.partner[fbi] is not None or gfi in gface_used:
                    self.stats['comb_prunes'] += 1
                    raise Prune('ridge in three facets')
                eB = {frozenset((Fb.gids[x], Fb.gids[y])) for x, y in cyc_edges(Fb.T.faces[fbi]['verts'])}
                eG = {frozenset((loc2g[x], loc2g[y])) for x, y in cyc_edges(T.faces[gfi]['verts'])}
                if eB != eG:
                    self.stats['comb_prunes'] += 1
                    raise Prune('polygon edges differ')
                gface_used.add(gfi)
                glues.append((fb, fbi, gfi))
        if not any((gl[0] == F and gl[1] == phi for gl in glues)):
            raise AssertionError()
        G = Facet()
        G.T = T
        G.gids = loc2g
        G.n = nG
        G.d = dG
        G.partner = [None] * len(T.faces)
        return (G, new_coords, glues)

    def recurse(self):
        self.stats['nodes'] += 1
        if self.node_limit and self.stats['nodes'] > self.node_limit:
            raise RuntimeError('node limit')
        if self.log and self.stats['nodes'] % 2000 == 0:
            self.log(self.stats)
        if not self.open:
            self.complete()
            return
        best = None
        for F, phi in sorted(self.open)[:1] if FIRST else sorted(self.open):
            cands = self.candidates(F, phi)
            if best is None or len(cands) < len(best[1]):
                best = ((F, phi), cands)
                if not cands:
                    break
        (F, phi), cands = best
        if not cands:
            self.stats['comb_prunes'] += 1
            return
        for nm, gf, ci in cands:
            self.stats['placements'] += 1
            try:
                G, coords, glues = self.place(F, phi, nm, gf, ci)
            except Prune:
                continue
            u = self.apply(G, coords, glues)
            try:
                fidx = len(self.facets) - 1
                for e in G.T.edges:
                    self.check_edge(frozenset((G.gids[i] for i in e)))
            except Prune:
                self.stats['comb_prunes'] += 1
                self.undo(u)
                continue
            self.recurse()
            self.undo(u)

    def complete(self):
        self.stats['completions'] += 1
        facets = sorted((F.T.name for F in self.facets))
        words = []
        for key in self.edge_index:
            comps = self.edge_chain(key)
            if not (len(comps) == 1 and comps[0][0] == 'cycle'):
                raise AssertionError()
            word = [(self.facets[f].T.name, self.facets[f].T.faces[cout]['label']) for f, cin, cout in comps[0][1]]
            cw = canon_word(word)
            p = self.check_edge(key)
            words.append(cw)
        words.sort()
        sig = json.dumps({'facets': facets, 'cycles': words}, sort_keys=True)
        strict = True
        for Fb in self.facets:
            gs = set(Fb.gids)
            for gi, y in enumerate(self.verts):
                if gi in gs:
                    continue
                s = ivdot(Fb.n, y) - Fb.d
                if not s.b < 0:
                    strict = False
        if sig not in self.found:
            self.found[sig] = {'count': 0, 'nverts': len(self.verts), 'nfacets': len(self.facets), 'strict': strict}
        self.found[sig]['count'] += 1
        self.found[sig]['strict'] = self.found[sig]['strict'] and strict

def cyc_edges(vs):
    m = len(vs)
    return [(vs[i], vs[(i + 1) % m]) for i in range(m)]
_TYPES = {}

def get_type(nm):
    if nm not in _TYPES:
        if os.environ.get('U2_LEGACY') == '1':
            _TYPES[nm] = LegacyTypeData(nm)
        else:
            from pathlib import Path
            sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'stage2'))
            from exact_types import ExactTypeData
            iv.prec = IV_PREC
            _TYPES[nm] = ExactTypeData(nm)
            if os.environ.get('U2_CERT_DIR'):
                path = Path(os.environ['U2_CERT_DIR'])
                path.mkdir(parents=True, exist_ok=True)
                (path / (nm + '.json')).write_text(json.dumps(_TYPES[nm].certificate(), sort_keys=True, separators=(',', ':')) + '\n')
    return _TYPES[nm]

def run_class(cls, log=None, node_limit=None):
    names = sorted(set((K for cy in cls['cycles'] for K in cy['facets'])))
    types = {nm: get_type(nm) for nm in names}
    S = ClassSearch(cls, types, log=log, node_limit=node_limit)
    t0 = time.process_time()
    try:
        found = S.run()
    except Exception as e:
        e.search_stats = dict(S.stats)
        raise
    cpu = time.process_time() - t0
    return (found, S.stats, cpu)
if __name__ == '__main__':
    classes = json.load(open(sys.argv[1]))
    want = set((int(x) for x in sys.argv[2:]))
    for cls in classes:
        if want and cls['index'] not in want:
            continue
        found, stats, cpu = run_class(cls, log=lambda s: print('   ', s, flush=True))
        print(cls['index'], 'cpu %.1f' % cpu, stats, flush=True)
        for sig, info in found.items():
            print('   ', info, sig[:300])
