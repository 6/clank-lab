"""Step 3 (REFUTED): develop stars vertex by vertex.

A hypothetical polytope P with the realisation X as vertex figure is built
around v0: its known facets are placed templates with all their vertices.
At the next vertex w whose star is not fixed, every congruence g with
g(v0) = w whose image star contains every known facet through w is tried
(g maps a facet F of the star of v0 onto one known facet F* through w,
through any template symmetry; see locuniq.py).  g is kept unless a certified
violation occurs when its star is added:
  * a vertex at distance in (0, 1) from a known vertex (separation lemma),
  * a known vertex strictly outside a facet hyperplane, or a new vertex
    strictly outside a known facet hyperplane (convexity),
  * a cell (3-face) in three facets, or two different facets sharing five
    affinely independent vertices (one hyperplane),
  * a known facet through w that is not in g(star) (certified mismatch).
Distinct stars are distinguished by exact encodings (canon.encode); each
distinct consistent star is a branch.  A branch with no consistent star at
some vertex is dead; the realisation is REFUTED when every branch dies.
"""
import itertools
import numpy as np
from mpmath import iv
from ivla import (ZERO, dot, norm2, dist2, matmul, transpose, vmid, vsub, vadd,
                  matvec)
import canon
from locuniq import frame5, _overlap_vec, _overlap_mat


class Dead(Exception):
    pass


class Undecided(Exception):
    """An unresolved branch must contribute OPEN, never a refutation."""


def all_cells(T):
    """every cell of the template as (frozenset of vertex indices, label)."""
    if hasattr(T, '_allcells'):
        return T._allcells
    out = {}
    for t in range(T.n):
        mats, perms = T.sym_to(t)
        perm = perms[0]
        for c in T.cells:
            key = frozenset(int(perm[i]) for i in c['verts'])
            out[key] = c['label']
    T._allcells = list(out.items())
    return T._allcells


class Dev:
    def __init__(self, R2):
        self.R2 = R2
        self.pts = []
        self.pf = []
        self.grid = {}
        self.facets = []   # dicts: type, T, L, c, c2, vids
        self.cells = {}
        self.vfac = {}     # pid -> list of (facet index, template index)
        self.done = set()

    def copy(self):
        d = Dev(self.R2)
        d.pts = list(self.pts)
        d.pf = list(self.pf)
        d.grid = {k: list(v) for k, v in self.grid.items()}
        d.facets = list(self.facets)
        d.cells = {k: list(v) for k, v in self.cells.items()}
        d.vfac = {k: list(v) for k, v in self.vfac.items()}
        d.done = set(self.done)
        return d

    # ---------------------------------------------------------- points
    def _cell(self, xf):
        return tuple(int(np.floor(v)) for v in xf)

    def resolve(self, x):
        """Existing id or -1; every possible identity is tested by intervals."""
        for pid, y in enumerate(self.pts):
            dd = dist2(x, y)
            if dd.b < 0.25:
                if dd.a > 0:
                    raise Dead("separation: distinct vertices closer than 1/2")
                return pid
            if dd.a > 0 and dd.b < 1:
                raise Dead("separation: vertex at distance in (1/2, 1)")
            if dd.a <= 0 <= dd.b:
                raise Undecided("point identity")
        return -1

    def add_point(self, x):
        pid = len(self.pts)
        self.pts.append(x)
        xf = vmid(x)
        self.pf.append(xf)
        self.grid.setdefault(self._cell(xf), []).append(pid)
        return pid

    # ---------------------------------------------------------- facets
    def add_facet(self, Ftype, T, L, c):
        c2 = norm2(c)
        V = [vadd(matvec(L, y), c) for y in T.V]
        vids = []
        newp = []
        for x in V:
            pid = self.resolve(x)
            if pid < 0:
                pid = self.add_point(x)
                newp.append(pid)
            vids.append(pid)
        if len(set(vids)) != len(vids):
            raise Dead("two vertices of a facet coincide")
        vs = frozenset(vids)
        for k, G in enumerate(self.facets):
            if G['vset'] == vs:
                return k, False
        # five affinely independent shared vertices -> same hyperplane
        for G in self.facets:
            sh = list(vs & G['vset'])
            if len(sh) >= 5 and _affinely_independent5(self, sh):
                raise Dead("two facets in one hyperplane")
        # convexity
        cf = vmid(c)
        c2f = float(c2.mid)
        own = vs
        for pid, xf in enumerate(self.pf):
            if pid in own:
                continue
            if sum(a * b for a, b in zip(xf, cf)) - c2f > -1e-9:
                if (dot(self.pts[pid], c) - c2).a > 0:
                    raise Dead("convexity: known vertex outside new facet")
        for pid in newp:
            xf = self.pf[pid]
            for G in self.facets:
                if sum(a * b for a, b in zip(xf, G['cf'])) - G['c2f'] > -1e-9:
                    if (dot(self.pts[pid], G['c']) - G['c2']).a > 0:
                        raise Dead("convexity: new vertex outside known facet")
        fi = len(self.facets)
        self.facets.append({'type': Ftype, 'T': T, 'L': L, 'c': c, 'c2': c2, 'vids': vids,
                            'vset': vs, 'cf': cf, 'c2f': c2f})
        for t, pid in enumerate(vids):
            self.vfac.setdefault(pid, []).append((fi, t))
        for cset, lab in all_cells(T):
            key = frozenset(vids[i] for i in cset)
            lst = self.cells.setdefault(key, [])
            lst.append(fi)
            if len(lst) > 2:
                raise Dead("cell in three facets")
        return fi, True


def _affinely_independent5(D, sh):
    for comb in itertools.combinations(sh, 5):
        P = [D.pts[i] for i in comb]
        Pf = np.array([D.pf[i] for i in comb])
        M = Pf[1:] - Pf[0]
        if abs(np.linalg.det(M @ M.T)) < 1e-8:
            continue
        vecs = [vsub(p, P[0]) for p in P[1:]]
        G = [[dot(a, b) for b in vecs] for a in vecs]
        from ivla import det
        dg = det(G)
        if dg.a > 0:
            return True
    return False


def start(s, R2):
    """Dev from the realisation's star (all facets through v0, full)."""
    D = Dev(R2)
    D.add_point(s.pts[0])
    for F in s.facets:
        D.add_facet(F.type, F.T, F.L, F.c)
    D.done.add(0)
    return D


def stars_at(D, s, w, adj):
    """all consistent distinct stars at w: list of (encoding, new Dev)."""
    known = D.vfac[w]
    fs, tw = known[0]
    Fs = D.facets[fs]
    mats, perms = Fs['T'].sym_to(tw)
    cn = iv.sqrt(Fs['c2'])
    frames = [frame5(F) for F in s.facets]
    out = {}
    reasons = {}
    for fi, F in enumerate(s.facets):
        if F.type != Fs['type']:
            continue
        AT = transpose(frames[fi])
        for S, perm in zip(mats, perms):
            frame = {F.m[j]: int(perm[j]) for j in F.T.nb}
            enc = canon.encode(s, fi, frame, adj)
            if enc in out:
                continue
            LS = matmul(Fs['L'], S)
            B = [list(LS[r]) + [Fs['c'][r] / cn] for r in range(5)]
            g = matmul(B, AT)
            imgs = [(G.type, G.T, matmul(g, G.L), [dot(row, G.c) for row in g]) for G in s.facets]
            # every known facet through w must be an image
            okk = True
            for hk, th in known:
                H = D.facets[hk]
                hit = False
                for (ty, T, L, c) in imgs:
                    if ty != H['type'] or not _overlap_vec(c, H['c']):
                        continue
                    M = matmul(transpose(H['L']), L)
                    hm, _ = H['T'].sym_to(th)
                    if any(_overlap_mat(M, X) for X in hm):
                        hit = True
                        break
                if not hit:
                    okk = False
                    break
            if not okk:
                reasons['known facet not in image'] = reasons.get('known facet not in image', 0) + 1
                continue
            D2 = D.copy()
            try:
                for (ty, T, L, c) in imgs:
                    D2.add_facet(ty, T, L, c)
            except Dead as e:
                reasons[str(e)] = reasons.get(str(e), 0) + 1
                continue
            except Undecided as e:
                key = 'UNDECIDED ' + str(e)
                reasons[key] = reasons.get(key, 0) + 1
                continue
            D2.done.add(w)
            out[enc] = D2
    return out, reasons


def develop(s, R2, max_vertices=3000, max_branches=10000, log=None):
    adj = canon.facet_adjacency(s)
    stats = {'branches': 0, 'dead': 0, 'closed': 0, 'stuck_reasons': {}, 'max_vertices': 0,
             'stars': 0, 'open': 0, 'undecided': 0, 'undecided_reasons': {}}
    try:
        D0 = start(s, R2)
    except Dead as e:
        stats['dead'] = 1
        stats['stuck_reasons'] = {'star of v0: ' + str(e): 1}
        stats['refuted'] = True
        return stats
    except Undecided as e:
        stats['open'] = stats['undecided'] = 1
        stats['undecided_reasons'] = {'star of v0: ' + str(e): 1}
        stats['refuted'] = False
        return stats
    stack = [(D0, 0)]
    while stack:
        D, depth = stack.pop()
        stats['branches'] += 1
        stats['max_vertices'] = max(stats['max_vertices'], len(D.pts))
        if stats['branches'] > max_branches or len(D.pts) > max_vertices:
            stats['open'] += 1
            continue
        todo = [p for p in range(len(D.pts)) if p not in D.done]
        if not todo:
            stats['closed'] += 1
            continue
        w = todo[0]
        res, reasons = stars_at(D, s, w, adj)
        stats['stars'] += 1
        # Count uncertainty even when another candidate star survives.
        unresolved = {k: v for k, v in reasons.items() if k.startswith('UNDECIDED ')}
        nopen = sum(unresolved.values())
        stats['open'] += nopen
        stats['undecided'] += nopen
        for k, v in unresolved.items():
            stats['undecided_reasons'][k] = stats['undecided_reasons'].get(k, 0) + v
        if not res:
            stats['dead'] += not nopen
            for k, v in reasons.items():
                stats['stuck_reasons'][k] = stats['stuck_reasons'].get(k, 0) + v
            if log is not None:
                log.append({'vertex': w, 'known_vertices': len(D.pts), 'facets': len(D.facets),
                            'candidates': reasons})
            continue
        for enc, D2 in res.items():
            stack.append((D2, depth + 1))
    stats['refuted'] = (stats['closed'] == 0 and stats['open'] == 0)
    return stats
