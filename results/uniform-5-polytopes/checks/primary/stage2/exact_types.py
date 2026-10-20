"""Interval VF templates and exact, labelled correspondence reductions.

Uses the existing exact construction models read-only.  No mpf padding,
approximate symmetry acceptance, rounded placements, or stage-3 search.
The stabilizer may be a subgroup: reductions need soundness, not maximality.
"""
import os
import sys
from pathlib import Path
from mpmath import iv
U3 = Path(__file__).resolve().parents[1] / 'check_u3'
sys.path.insert(0, str(U3))
import templates
import tcert
from model_runtime import ensure_guard
from ivla import dot, norm2, dist2, vsub, vscale, gram_schmidt

class LocalTemplate(templates.Template):

    def _dihedral(self, *args):
        return None

    def _syms(self):
        pass

def unit(v):
    n2 = norm2(v)
    if not n2.a > 0:
        raise ValueError('frame length not certified positive')
    return vscale(1 / iv.sqrt(n2), v)

def cross(a, b):
    return [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]]

def frame(V, order, normal):
    x0, x1, x2 = [V[i] for i in order[:3]]
    u = unit(vsub(x1, x0))
    w = vsub(x2, x0)
    v = unit(vsub(w, vscale(dot(w, u), u)))
    return [u, v, normal]

class ExactTypeData:

    def __init__(self, name):
        ensure_guard()
        model = tcert.model4(name)
        V = [[tcert.qiv(c) for c in v] for v in model.E] if hasattr(model, 'E') else None
        T = LocalTemplate(name, V=V)
        self.name = name
        self.template = T
        self.R2 = T.R2
        self.rK2 = 1 - 1 / (4 * T.R2)
        self.nb = T.nb
        self.nv = len(T.nb)
        local = {v: i for i, v in enumerate(T.nb)}
        centre = vscale(1 - 1 / (2 * T.R2), T.V[0])
        radial = unit(T.V[0])
        import itertools
        axes = None
        W = [vsub(T.V[i], centre) for i in T.nb]
        for tr in itertools.combinations(range(self.nv), 3):
            try:
                basis = []
                for v in [radial] + [W[i] for i in tr]:
                    w = list(v)
                    for u in basis:
                        w = vsub(w, vscale(dot(w, u), u))
                    basis.append(unit(w))
                axes = basis[1:]
                break
            except (ZeroDivisionError, ValueError):
                continue
        if not axes is not None:
            raise AssertionError(name)
        self.verts = [tuple((dot(w, a) for a in axes)) for w in W]
        self.faces = []
        self.edge_faces = {}
        self.edge_p = {frozenset((local[v] for v in k)): q['p'] for k, q in T.polys.items()}
        for ci, cell in enumerate(T.cells):
            vs = [local[v] for v in cell['poly']]
            pts = [self.verts[v] for v in vs]
            normal = unit(cross(vsub(pts[1], pts[0]), vsub(pts[2], pts[0])))
            h = dot(pts[0], normal)
            if h.b < 0:
                normal = vscale(-1, normal)
                h = -h
            if not h.a > 0:
                raise AssertionError((name, 'centre on face'))
            basis = frame(self.verts, vs, normal)
            e1 = vsub(pts[1], pts[0])
            w2 = vsub(pts[2], pts[0])
            w2 = vsub(w2, vscale(dot(w2, basis[0]), basis[0]))
            ps = [self.edge_p[frozenset((vs[i], vs[(i + 1) % len(vs)]))] for i in range(len(vs))]
            self.faces.append(dict(verts=vs, label=cell['label'], ps=ps, h=h, L1=iv.sqrt(norm2(e1)), L2=iv.sqrt(norm2(w2)), normal=normal, vset=frozenset(vs)))
            for i, v in enumerate(vs):
                self.edge_faces.setdefault(frozenset((v, vs[(i + 1) % len(vs)])), []).append(ci)
        if not all((len(v) == 2 for v in self.edge_faces.values())):
            raise AssertionError()
        self.edges = list(self.edge_faces)
        self.face_of_vset = {f['vset']: i for i, f in enumerate(self.faces)}
        self.face_vsets = {frozenset()} | {frozenset([i]) for i in range(self.nv)} | set(self.edges) | set(self.face_of_vset)
        self.syms = []
        for g in T.model.stab():
            if not int(g[0]) == 0:
                raise AssertionError()
            p = tuple((local[int(g[v])] for v in T.nb))
            if not sorted(p) == list(range(self.nv)):
                raise AssertionError()
            if p not in self.syms:
                self.syms.append(p)
        for p in self.syms:
            for e, size in self.edge_p.items():
                if not self.edge_p[frozenset((p[v] for v in e))] == size:
                    raise AssertionError()
            for f in self.faces:
                j = self.face_of_vset[frozenset((p[v] for v in f['verts']))]
                if not self.faces[j]['label'] == f['label']:
                    raise AssertionError()
        self.corr = []
        for gf, f in enumerate(self.faces):
            vs = f['verts']
            m = len(vs)
            lst = []
            for s in range(m):
                for dr in (1, -1):
                    order = [vs[(s + dr * i) % m] for i in range(m)]
                    basis = frame(self.verts, order, f['normal'])
                    ps = tuple((self.edge_p[frozenset((order[i], order[(i + 1) % m]))] for i in range(m)))
                    other = []
                    for i in range(m):
                        a, b = self.edge_faces[frozenset((order[i], order[(i + 1) % m]))]
                        other.append(self.faces[b if a == gf else a]['label'])
                    lst.append(dict(order=order, ps=ps, coef=[tuple((dot(x, a) for a in basis)) for x in self.verts], other=tuple(other)))
            self.corr.append(lst)
        self.idx = {(gf, tuple(c['order'])): (gf, ci) for gf, cs in enumerate(self.corr) for ci, c in enumerate(cs)}
        self.reductions = []
        for gf, cs in enumerate(self.corr):
            for ci, c in enumerate(cs):
                images = []
                for si, p in enumerate(self.syms):
                    order = tuple((p[v] for v in c['order']))
                    j = self.face_of_vset[frozenset(order)]
                    images.append((self.idx[j, order], si))
                rep, si = min(images)
                j, k = rep
                rc = self.corr[j][k]
                if not [self.syms[si][v] for v in c['order']] == rc['order']:
                    raise AssertionError()
                if not (c['ps'] == rc['ps'] and c['other'] == rc['other']):
                    raise AssertionError()
                if not self.faces[gf]['label'] == self.faces[j]['label']:
                    raise AssertionError()
                c['rep'] = rep == (gf, ci)
                c['orbit'] = {im for im, _ in images}
                self.reductions.append(dict(source=[gf, ci], representative=list(rep), symmetry=si, hinge='opposite'))

    def certificate(self):
        return dict(schema='stage2-exact-equivalence-v1', name=self.name, neighbours=self.nb, faces=[dict(verts=f['verts'], label=f['label'], ps=f['ps']) for f in self.faces], symmetries=[list(p) for p in self.syms], reductions=self.reductions)
