"""Uniform polyhedra (convex): local data for the 4-D control enumeration.

For each cell type: circumradius (unit edge), vertex configuration, and the
edge orbits as (q1, q2, alpha) with alpha the dihedral angle between the two
faces (a q1-gon and a q2-gon) at that edge.  Finite types are measured from
the constructed polytopes; prisms and antiprisms use closed forms.
"""
import itertools, math
import numpy as np
from geom import wythoff, snub, Polytope
ARCH = {'tet': ('A3', (1, 0, 0)), 'oct': ('B3', (1, 0, 0)), 'cube': ('B3', (0, 0, 1)), 'ico': ('H3', (0, 0, 1)), 'doe': ('H3', (1, 0, 0)), 'tut': ('A3', (1, 1, 0)), 'co': ('B3', (0, 1, 0)), 'tic': ('B3', (0, 1, 1)), 'toe': ('B3', (1, 1, 0)), 'sirco': ('B3', (1, 0, 1)), 'girco': ('B3', (1, 1, 1)), 'id': ('H3', (0, 1, 0)), 'tid': ('H3', (0, 1, 1)), 'ti': ('H3', (1, 1, 0)), 'srid': ('H3', (1, 0, 1)), 'grid': ('H3', (1, 1, 1)), 'snic': ('B3', 'snub'), 'snid': ('H3', 'snub')}

def build(name):
    g, r = ARCH[name]
    V = snub([g]) if r == 'snub' else wythoff([g], r)
    return Polytope(V, name)

def edge_orbits(P):
    """Distinct (q1<=q2, alpha) over edges, with alpha rounded for grouping."""
    F = P.faces()
    faces2 = F[2]
    c = P.V.mean(axis=0)
    out = {}
    for e in F[1]:
        inc = [f for f in faces2 if e <= f]
        if not len(inc) == 2:
            raise AssertionError()
        a, b = sorted(e)
        mid = (P.V[a] + P.V[b]) / 2
        u = P.V[b] - P.V[a]
        u /= np.linalg.norm(u)
        dirs = []
        for f in inc:
            fc = P.V[sorted(f)].mean(axis=0)
            w = fc - mid
            w -= np.dot(w, u) * u
            dirs.append(w / np.linalg.norm(w))
        alpha = math.acos(max(-1, min(1, float(np.dot(dirs[0], dirs[1])))))
        qs = tuple(sorted((len(f) for f in inc)))
        key = (qs, round(alpha, 9))
        out[key] = out.get(key, 0) + 1
    return [(k[0][0], k[0][1], k[1], cnt) for k, cnt in sorted(out.items())]

def prism_data(n):
    R = math.sqrt(1 / (4 * math.sin(math.pi / n) ** 2) + 0.25)
    return (R, [(4, 4, math.pi - 2 * math.pi / n), (4, n, math.pi / 2)])

def antiprism_data(n):
    V = []
    rho = 1 / (2 * math.sin(math.pi / n))
    hh = math.sqrt(max(0.0, 1 - (2 * rho * math.sin(math.pi / (2 * n))) ** 2))
    for k in range(n):
        t = 2 * math.pi * k / n
        V.append((rho * math.cos(t), rho * math.sin(t), hh / 2))
        t2 = t + math.pi / n
        V.append((rho * math.cos(t2), rho * math.sin(t2), -hh / 2))
    P = Polytope(np.array(V), 'anti%d' % n)
    R = P.circumradius()[0]
    return (R, [(a, b, al) for a, b, al, _ in edge_orbits(P)], P)

def library(pmax=14):
    lib = {}
    for name in ARCH:
        P = build(name)
        lib[name] = dict(R=P.circumradius()[0], edges=[(a, b, al) for a, b, al, _ in edge_orbits(P)])
    for n in range(3, pmax + 1):
        R, ed = prism_data(n)
        if n != 4:
            lib['P%d' % n] = dict(R=R, edges=ed)
        R, ed, _ = antiprism_data(n)
        if n != 3:
            lib['A%d' % n] = dict(R=R, edges=ed)
    return lib
if __name__ == '__main__':
    lib = library(8)
    for k, v in lib.items():
        print(k, round(v['R'], 6), [(a, b, round(al, 5)) for a, b, al in v['edges']])

def vertex_config(P, v=0):
    """Cyclic sequence of polygon sizes around vertex v of a polyhedron (one orientation)."""
    F = P.faces()
    inc = [f for f in F[2] if v in f]
    p = P.V[v]
    c = P.V.mean(axis=0)
    n = p - c
    n /= np.linalg.norm(n)
    a = np.cross(n, [1, 0, 0]) if abs(n[0]) < 0.9 else np.cross(n, [0, 1, 0])
    a /= np.linalg.norm(a)
    b = np.cross(n, a)
    ang = []
    for f in inc:
        fc = P.V[sorted(f)].mean(axis=0) - p
        ang.append((math.atan2(np.dot(fc, b), np.dot(fc, a)), len(f)))
    ang.sort()
    return [q for _, q in ang]

def configs(pmax=14):
    out = {}
    for name in ARCH:
        out[name] = vertex_config(build(name))
    for n in range(3, pmax + 1):
        if n != 4:
            out['P%d' % n] = [4, 4, n]
        if n != 3:
            out['A%d' % n] = [3, 3, 3, n]
    return out
