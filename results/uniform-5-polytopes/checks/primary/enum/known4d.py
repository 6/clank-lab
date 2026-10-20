"""Known convex uniform polychora and their vertex-figure signatures (control reference)."""
import itertools, math, sys, json
import numpy as np
from scipy.spatial import ConvexHull
from geom import wythoff, snub, affine_basis, hull_facets, Polytope
from vf3 import canon_cycle


def cell_name(P3):
    """Name a uniform polyhedron (Polytope) in the cells3d vocabulary."""
    F = P3.faces()
    from collections import Counter
    cnt = Counter(len(f) for f in F[2])
    nv = len(F[0])
    sig = (nv, tuple(sorted(cnt.items())))
    table = {
        (4, ((3, 4),)): 'tet', (6, ((3, 8),)): 'oct', (8, ((4, 6),)): 'cube', (12, ((3, 20),)): 'ico',
        (20, ((5, 12),)): 'doe', (12, ((3, 4), (6, 4))): 'tut', (12, ((3, 8), (4, 6))): 'co',
        (24, ((3, 8), (8, 6))): 'tic', (24, ((4, 6), (6, 8))): 'toe', (24, ((3, 8), (4, 18))): 'sirco',
        (48, ((4, 12), (6, 8), (8, 6))): 'girco', (30, ((3, 20), (5, 12))): 'id', (60, ((5, 12), (6, 20))): 'tid',
        (60, ((3, 20), (10, 12))): 'ti', (60, ((3, 20), (4, 30), (5, 12))): 'srid',
        (120, ((4, 30), (6, 20), (10, 12))): 'grid', (24, ((3, 32), (4, 6))): 'snic', (60, ((3, 80), (5, 12))): 'snid',
    }
    if sig in table:
        return table[sig]
    # prisms / antiprisms
    if nv % 2 == 0:
        n = nv // 2
        if dict(cnt) == {4: n, n: 2} or (n == 4 and dict(cnt) == {4: 6}):
            return 'P%d' % n
        if dict(cnt) == {3: 2 * n, n: 2} or (n == 3 and dict(cnt) == {3: 8}):
            return 'A%d' % n
    raise ValueError(sig)


def vf_signature(V, v=0):
    """(sorted cell names at v, sorted canonical edge neighbourhoods at v) for a uniform polychoron."""
    c, B = affine_basis(V)
    X = (V - c) @ B.T
    H = ConvexHull(X)
    cells = {}
    for eq in H.equations:
        on = tuple(sorted(np.where(np.abs(X @ eq[:-1] + eq[-1]) < 1e-7)[0].tolist()))
        cells[on] = True
    cells = [set(cc) for cc in cells]
    at_v = [cc for cc in cells if v in cc]
    names = {}
    for cc in at_v:
        names[frozenset(cc)] = cell_name(Polytope(V[sorted(cc)]))
    nbrs = [w for w in range(len(V)) if w != v and abs(np.linalg.norm(V[w] - V[v]) - 1) < 1e-6]
    fans = []
    for w in nbrs:
        around = [cc for cc in at_v if w in cc]
        # adjacency: two cells around the edge share a polygon containing v,w
        def shared_poly(a, b):
            s = a & b
            if len(s) >= 3 and Polytope(V[sorted(s)]).dim == 2:
                return len(s)
            return None
        # build cycle
        order = [around[0]]
        labs = []
        used = {0}
        while len(order) < len(around):
            cur = order[-1]
            for j, cc in enumerate(around):
                if j in used:
                    continue
                q = shared_poly(cur, cc)
                if q:
                    order.append(cc)
                    labs.append(q)
                    used.add(j)
                    break
            else:
                raise RuntimeError('broken fan')
        labs.append(shared_poly(order[-1], order[0]))
        seq = [(names[frozenset(cc)], labs[i]) for i, cc in enumerate(order)]
        fans.append(canon_cycle(seq))
    R = np.linalg.norm(V[v] - V.mean(axis=0))
    return R, (tuple(sorted(names.values())), tuple(sorted(fans)))


def known_list(pmax, groups=('A4', 'B4', 'D4', 'F4', 'H4')):
    out = []
    for g in groups:
        for rings in itertools.product([0, 1], repeat=4):
            if any(rings):
                out.append(('%s%s' % (g, ''.join(map(str, rings))), wythoff([g], rings)))
    out.append(('sadi', snub(['D4'])))
    if 'H4' in groups:
        out.append(('gap', grand_antiprism()))
    # prisms over uniform polyhedra
    from cells3d import ARCH
    for cname, (g, r) in ARCH.items():
        if r == 'snub':
            out.append(('pr-' + cname, prism_of(snub([g]))))
        else:
            out.append(('pr-' + cname, wythoff([g, 'A1'], list(r) + [1])))
    for n in range(3, pmax + 1):
        out.append(('antiprism-prism-%d' % n, prism_of(snub(['I2_%d' % n, 'A1']))))
        for m in range(n, pmax + 1):
            out.append(('duoprism-%d-%d' % (n, m), wythoff(['I2_%d' % n, 'I2_%d' % m], [1, 0, 1, 0])))
    return out


def prism_of(V3):
    a = np.hstack([V3, np.full((len(V3), 1), 0.5)])
    b = np.hstack([V3, np.full((len(V3), 1), -0.5)])
    return np.vstack([a, b])


def grand_antiprism():
    V = wythoff(['H4'], [0, 0, 0, 1])  # 600-cell? check vertex count
    if len(V) != 120:
        V = wythoff(['H4'], [1, 0, 0, 0])
    c = V.mean(axis=0)
    U = V - c
    Rr = np.linalg.norm(U[0])
    Un = U / Rr
    # decagon planes: pairs at angle 36 degrees
    planes = []
    n = len(Un)
    seen = set()
    for i in range(n):
        for j in range(i + 1, n):
            if abs(np.dot(Un[i], Un[j]) - math.cos(math.pi / 5)) < 1e-9:
                a = Un[i]
                b = Un[j] - np.dot(Un[j], a) * a
                b /= np.linalg.norm(b)
                inplane = [k for k in range(n) if abs(np.linalg.norm(Un[k] - np.dot(Un[k], a) * a - np.dot(Un[k], b) * b)) < 1e-9]
                if len(inplane) == 10:
                    key = tuple(sorted(inplane))
                    if key not in seen:
                        seen.add(key)
                        planes.append((key, a, b))
    for (k1, a1, b1), (k2, a2, b2) in itertools.combinations(planes, 2):
        if max(abs(np.dot(x, y)) for x in (a1, b1) for y in (a2, b2)) < 1e-9:
            keep = [k for k in range(n) if k not in k1 and k not in k2]
            return V[keep]
    raise RuntimeError('no orthogonal decagons')


if __name__ == '__main__':
    pmax = int(sys.argv[1])
    groups = sys.argv[2].split(',') if len(sys.argv) > 2 else ('A4', 'B4', 'D4', 'F4', 'H4')
    res = []
    for name, V in known_list(pmax, groups):
        R, sig = vf_signature(V)
        res.append((name, R, [list(sig[0]), [list(map(list, f)) for f in sig[1]]]))
        print(name, round(R, 6), sig[0], file=sys.stderr, flush=True)
    json.dump(res, open('known4d_p%d.json' % pmax, 'w'))
