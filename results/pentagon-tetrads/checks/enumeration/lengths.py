"""Length and closure screen for angle survivors (numerical screen).

Each map edge e is cut by its bends into bends[e]+1 segments (e, j),
j = 0..bends[e] in the traversal direction of the tile at the tail of dart 2e.
A tile edge (between consecutive corners of the tile) is a run of segments
through the map vertices where the tile is straight; its length equals the
prototile side carrying its label. The prototile closes:
    sum_i l_i (cos th_i, sin th_i) = 0,  th_0 = 0, th_{i+1} = th_i + 180 - a_{i+1}.
"""
import itertools
import json
import math
import sys

import numpy as np
from scipy.optimize import linprog, minimize

from placements import MapData, placements, corner_sequence, label_of


def tile_items(md, cs, bends, t):
    """Cyclic boundary items of tile t in ccw order: ('C', pos) corners and
    ('G', (e, j)) segments; straight vertex sectors are omitted."""
    items = []
    for d in md.tile_cycle(t):
        if cs[d] == 'C':
            items.append(('C', ('V', d)))
        e = d // 2
        b = bends[e]
        if d % 2 == 0:
            for j in range(b + 1):
                items.append(('G', (e, j)))
                if j < b:
                    items.append(('C', ('B', e, j)))
        else:
            for j in range(b, -1, -1):
                items.append(('G', (e, j)))
                if j > 0:
                    items.append(('C', ('B', e, j - 1)))
    return items


def tile_edges(md, cs, bends, t, lab, n):
    """List of (P-edge label, [segments]) for tile t, in ccw order starting
    after its corner 0 (corner order = corner_sequence order)."""
    seq = corner_sequence(md, cs, bends, t)
    items = tile_items(md, cs, bends, t)
    # rotate items to start at corner seq[0]
    idx = items.index(('C', seq[0]))
    items = items[idx:] + items[:idx]
    out = []
    k = -1
    cur = None
    for kind, val in items:
        if kind == 'C':
            k += 1
            assert seq[k] == val, (seq, items)
            if cur is not None:
                out.append(cur)
            proper, s = lab
            elab = (s + k) % n if proper else (s - k - 1) % n
            cur = (elab, [])
        else:
            cur[1].append(val)
    out.append(cur)
    assert k == n - 1
    return out


def length_system(md, cs, bends, labs, n):
    segs = sorted({(e, j) for e in range(len(md.edges)) for j in range(bends[e] + 1)})
    sid = {s: i for i, s in enumerate(segs)}
    rows = []  # each row: (P-edge label, list of segment ids)
    for t in range(4):
        for elab, sl in tile_edges(md, cs, bends, t, tuple(labs[t]), n):
            rows.append((elab, [sid[s] for s in sl]))
    return segs, rows


def angle_system(md, cs, bends, labs, n):
    from angles2 import constraints
    cons, seqs = constraints(md, cs, bends, n)
    rows = []
    for kind, slots, s in cons:
        coef = [0] * n
        for t, k in slots:
            coef[label_of(tuple(labs[t]), k, n)] += 1
        rows.append((kind, tuple(coef), 180 * s))
    return sorted(set(rows))


def build_problem(md, rec, n):
    cs = {int(k): v for k, v in rec['cs'].items()}
    bends = rec['bends']
    labs = rec['labs']
    segs, lrows = length_system(md, cs, bends, labs, n)
    arows = angle_system(md, cs, bends, labs, n)
    return cs, bends, labs, segs, lrows, arows


def length_lp(n, segs, lrows):
    """Max margin t with l_i >= t, x_s >= t, sum l = 1, rows exact."""
    ns = len(segs)
    nv = n + ns + 1
    A_eq = [[1] * n + [0] * ns + [0]]
    b_eq = [1]
    for elab, sl in lrows:
        r = [0] * nv
        r[elab] -= 1
        for s in sl:
            r[n + s] += 1
        A_eq.append(r)
        b_eq.append(0)
    A_ub = []
    b_ub = []
    for i in range(n + ns):
        r = [0] * nv
        r[i] = -1
        r[-1] = 1
        A_ub.append(r)
        b_ub.append(0)
    c = [0] * (nv - 1) + [-1]
    res = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq,
                  bounds=[(None, None)] * (nv - 1) + [(None, 1)], method='highs')
    if res.status != 0:
        return -1, None
    return -res.fun, res.x


def directions(alpha):
    th = [0.0]
    for i in range(1, len(alpha)):
        th.append(th[-1] + 180 - alpha[i])
    return np.radians(th)


def joint_search(n, segs, lrows, arows, pattern, starts=30, seed=0):
    """Maximise margin t subject to angle rows, length rows and closure.
    Variables: alpha (n), l (n), x (ns), t."""
    ns = len(segs)
    nv = 2 * n + ns + 1
    rng = np.random.default_rng(seed)
    eqs = []
    ineqs = []

    def A(i):
        return i

    def L(i):
        return n + i

    def X(i):
        return 2 * n + i
    T = nv - 1
    lin_eq = [([1] * n + [0] * (nv - n), (n - 2) * 180)]
    lin_ub = []  # a.x <= b
    for kind, coef, const in arows:
        r = list(coef) + [0] * (nv - n)
        if kind == 'E':
            if sum(coef) == 0:
                continue
            lin_eq.append((r, 360 - const))
        else:
            r[T] = 1
            lin_ub.append((r, 360 - const))
    for i in range(n):
        r = [0] * nv
        r[A(i)] = -1
        r[T] = 1
        lin_ub.append((r, 0))
        r = [0] * nv
        r[A(i)] = 1
        r[T] = 1
        lin_ub.append((r, 360))
        r = [0] * nv
        if pattern[i]:
            r[A(i)] = -1
            r[T] = 1
            lin_ub.append((r, -180))
        else:
            r[A(i)] = 1
            r[T] = 1
            lin_ub.append((r, 180))
    r = [0] * nv
    for i in range(n):
        r[L(i)] = 1
    lin_eq.append((r, 1))
    for elab, sl in lrows:
        r = [0] * nv
        r[L(elab)] -= 1
        for s in sl:
            r[X(s)] += 1
        lin_eq.append((r, 0))
    for i in range(n + ns):
        r = [0] * nv
        r[n + i] = -1
        r[T] = 0.01  # lengths margin scaled (lengths sum to 1)
        lin_ub.append((r, 0))
    Aeq = np.array([r for r, b in lin_eq], float)
    beq = np.array([b for r, b in lin_eq], float)
    Aub = np.array([r for r, b in lin_ub], float)
    bub = np.array([b for r, b in lin_ub], float)

    def closure(z):
        th = directions(z[:n])
        l = z[n:2 * n]
        return np.array([np.dot(l, np.cos(th)), np.dot(l, np.sin(th))])

    cons = [{'type': 'eq', 'fun': lambda z: Aeq @ z - beq},
            {'type': 'ineq', 'fun': lambda z: bub - Aub @ z},
            {'type': 'eq', 'fun': closure}]
    best = (-1e9, None)
    for s in range(starts):
        z0 = np.zeros(nv)
        z0[:n] = np.where(pattern, 180 + rng.uniform(1, 179, n), rng.uniform(1, 179, n))
        z0[n:2 * n] = rng.uniform(0.05, 0.4, n)
        z0[2 * n:2 * n + ns] = rng.uniform(0.01, 0.2, ns)
        z0[T] = 0
        res = minimize(lambda z: -z[T], z0, constraints=cons, method='SLSQP',
                       bounds=[(0, 360)] * n + [(0, 1)] * (n + ns) + [(-1, 1)],
                       options={'maxiter': 500, 'ftol': 1e-12})
        if res.success:
            z = res.x
            viol = max(np.max(np.abs(Aeq @ z - beq)), np.max(np.maximum(Aub @ z - bub, 0)),
                       np.max(np.abs(closure(z))))
            if viol < 1e-7 and z[T] > best[0]:
                best = (z[T], z)
    return best


def main(maps_file, surv_file, n, outf):
    maps = [MapData(json.loads(l)) for l in open(maps_file)]
    recs = [json.loads(l) for l in open(surv_file)]
    stats = {'records': len(recs), 'length_dead': 0, 'joint_dead': 0, 'joint_alive': 0}
    with open(outf, 'w') as out:
        for ri, rec in enumerate(recs):
            md = maps[rec['map']]
            cs, bends, labs, segs, lrows, arows = build_problem(md, rec, n)
            tm, x = length_lp(n, segs, lrows)
            if tm <= 1e-9:
                stats['length_dead'] += 1
                continue
            t, z = joint_search(n, segs, lrows, arows, rec['pattern'])
            if t > 1e-6:
                stats['joint_alive'] += 1
                rec2 = dict(rec)
                rec2['joint_margin'] = t
                rec2['z'] = [float(v) for v in z]
                out.write(json.dumps(rec2) + '\n')
            else:
                stats['joint_dead'] += 1
            if ri % 50 == 0:
                print(ri, stats, file=sys.stderr, flush=True)
    print(stats, file=sys.stderr)


if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4])
