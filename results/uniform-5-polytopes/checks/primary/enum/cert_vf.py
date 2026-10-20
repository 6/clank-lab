"""Diagnostic stage-2 producer: candidate vertex figures of a radius class.

The rounded placement deduplication below has no exact equivalence witness;
this producer is not the completeness proof. The rigorous route is
check_u2/search.py with stage2's exact correspondence certificates.

The vertex figure VF of a uniform 5-polytope P (unit edges, circumradius R) at v is a convex
4-polytope with vertices on the sphere of radius r = sqrt(1 - 1/(4R^2)) (centre at the
origin here): its vertices are the neighbours of v, its facets are the vertex figures of P's
facets at v (each a polyhedron on a sphere of radius r_K = sqrt(1 - 1/(4R_K^2)) in a
hyperplane at distance sqrt(r^2 - r_K^2)), its ridges are the vertex figures of cells, and
around each VF-edge (a polygon of P at v) the facets form one of the class's stage-1 cycles.

Search (same order as vfasm): seed the least facet type present, place it in a fixed
position; repeatedly take the least open ridge and try every facet type >= the seed type,
every ridge of that type with the same cell label, every isometric correspondence of the
ridge polygon, and both hinge positions; keep the placements that survive the predicates.
The geometric predicates below use Arb balls over the class interval:

- vertex identity: distinct vertices of P are >= 1 apart (nearest vertex is adjacent), so a
  squared-distance ball containing 0 with upper bound < 1 means the same vertex,
  a ball inside (0, 1) refutes the branch,
  an enclosure excluding zero permits a new vertex; an enclosure containing
  zero and reaching one is UNDECIDED, never a new vertex;
- convexity: a vertex certified outside a facet hyperplane refutes the branch;
- a facet with the vertex set of an existing facet is refuted (this removes the fold-back
  hinge solution); a placed ridge must land exactly on the target ridge;
- combinatorics: a ridge in more than two facets, label clash, or a closed VF-edge cycle not
  in the class refutes the branch.
These geometric tests do not justify the separate rounded duplicate filter.

usage: cert_vf.py PMAX CLASS_INDEX [...]  (indices into classes_pPMAX.json)
"""
import itertools, json, sys, time
from flint import arb, ctx
import cert_star as cs
from vfasm import canon_cycle
ctx.prec = 200
ZERO = arb(0)

def dot(a, b):
    return sum((x * y for x, y in zip(a, b)), arb(0))

def sub(a, b):
    return [x - y for x, y in zip(a, b)]

def add(a, b):
    return [x + y for x, y in zip(a, b)]

def scal(c, a):
    return [c * x for x in a]

def mid(a):
    return [float(x.mid()) for x in a]

def gram_schmidt(vecs, k):
    """k orthonormal vectors spanning the same space as the given ones (pivot on largest residual)."""
    out, pool = ([], list(vecs))
    while len(out) < k:
        best, bn = (None, -1.0)
        for v in pool:
            w = list(v)
            for u in out:
                w = sub(w, scal(dot(w, u), u))
            n = float(dot(w, w).mid())
            if n > bn:
                best, bn = (w, n)
        nrm = dot(best, best).sqrt()
        out.append(scal(1 / nrm, best))
    return out

def complement(D, m):
    """Orthonormal basis of the orthogonal complement of span(D) in R^m (D orthonormal)."""
    E = [[arb(1) if i == j else arb(0) for j in range(m)] for i in range(m)]
    res = []
    for e in E:
        w = list(e)
        for u in D:
            w = sub(w, scal(dot(w, u), u))
        res.append(w)
    return gram_schmidt(res, m - len(D))

class Model:
    """Vertex figure of facet K: points X (arb 3-vectors, centred), ridges (label, cyclic idx)."""

    def __init__(self, name):
        S = cs.star(name)
        self.name = name
        R = S['R']
        self.R = R
        c = scal(1 - 1 / (2 * R * R), S['v0'])
        Y = [sub(p, c) for p in S['nbrs']]
        E = gram_schmidt(Y, 3)
        self.X = [[dot(y, e) for e in E] for y in Y]
        self.rc2 = 1 - 1 / (4 * R * R)
        self.ridges = [(lab, tuple(idx)) for lab, idx in S['cells']]
        import cert_ridges
        self.ridge_stats = cert_ridges.check_model(self, S)
        for x in self.X:
            if not dot(x, x).overlaps(self.rc2):
                raise AssertionError()

def dist2(a, b):
    d = sub(a, b)
    return dot(d, d)

def solve3(A, b):
    """Solve the 3x3 system A x = b (A as rows) in arb by Cramer's rule."""

    def det(M):
        return M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1]) - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0]) + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0])
    D = det(A)
    out = []
    for j in range(3):
        M = [list(r) for r in A]
        for i in range(3):
            M[i][j] = b[i]
        out.append(det(M) / D)
    return out

class Fig:

    def __init__(self):
        self.pos = []
        self.facets = []
        self.ridges = {}

    def copy(self):
        o = Fig()
        o.pos = list(self.pos)
        o.facets = list(self.facets)
        o.ridges = {k: list(v) for k, v in self.ridges.items()}
        return o

class Refuted(Exception):
    pass

class Undecided(Exception):
    """The class cannot be certified without refining this enclosure."""

def identify(fig, p, extra):
    """Index of the vertex equal to p among fig.pos + extra (list of new points), or None if new.
    Raises Refuted if p is certified within distance < 1 of a different vertex."""
    pts = fig.pos + extra
    hit = None
    for i, q in enumerate(pts):
        d2 = dist2(p, q)
        if d2.contains(0) and d2 < 1:
            if hit is not None:
                raise Refuted('two vertices within tolerance')
            hit = i
        elif d2 < 1:
            raise Refuted('vertices closer than an edge')
        elif d2.contains(0):
            raise Undecided('point identity')
    return hit

def try_place(fig, mod, Y, n, d, allowed_cycles, target=None):
    """target: (model ridge vertex indices, target vertex ids) that must coincide."""
    'Add facet (model mod at points Y, hyperplane n.x = d) to a copy of fig, or raise Refuted.'
    for p in fig.pos:
        if dot(n, p) - d > 0:
            raise Refuted('existing vertex outside the new facet')
    for nm2, ids2, n2, d2, _ in fig.facets:
        for y in Y:
            if dot(n2, y) - d2 > 0:
                raise Refuted('new vertex outside an existing facet')
    o = fig.copy()
    new = []
    ids = []
    for y in Y:
        i = identify(o, y, new)
        if i is None:
            new.append(y)
            i = len(o.pos) + len(new) - 1
        ids.append(i)
    if len(set(ids)) != len(ids):
        raise Refuted('facet vertices coincide')
    if any((set(ids) == set(f[1]) for f in o.facets)):
        raise Refuted('same vertex set as an existing facet (e.g. the fold-back hinge solution)')
    if target is not None and frozenset((ids[i] for i in target[0])) != frozenset(target[1]):
        raise Refuted('placed ridge does not land on the target ridge')
    o.pos = o.pos + new
    fi = len(o.facets)
    keys = []
    for lab, ridx in mod.ridges:
        cyc = tuple((ids[i] for i in ridx))
        key = frozenset(cyc)
        lst = o.ridges.setdefault(key, [])
        if lst and lst[0][1] != lab:
            raise Refuted('ridge label clash')
        lst.append((fi, lab, cyc))
        if len(lst) > 2:
            raise Refuted('ridge in three facets')
        keys.append(key)
    o.facets.append((mod.name, tuple(ids), n, d, keys))
    for key in edges_of_facet(o, fi):
        cy = cycle_at(o, key)
        if cy is not None and canon_cycle(cy) not in allowed_cycles:
            raise Refuted('VF-edge cycle not in the class')
    return o

def edges_of_facet(fig, fi):
    keys = fig.facets[fi][4]
    out = set()
    for a, b in itertools.combinations(keys, 2):
        s = a & b
        if len(s) == 2:
            out.add(frozenset(s))
    return out

def cycle_at(fig, e):
    """Closed cycle (facet name, label after) around VF-edge e, or None if not closed."""
    rid = [k for k in fig.ridges if e <= k]
    if not rid or any((len(fig.ridges[k]) != 2 for k in rid)):
        return None
    adj = {}
    for k in rid:
        (fa, la, _), (fb, lb, _) = fig.ridges[k]
        adj.setdefault(fa, []).append((k, fb, la))
        adj.setdefault(fb, []).append((k, fa, la))
    if any((len(v) != 2 for v in adj.values())):
        return None
    start = next(iter(adj))
    seq, prev, cur = ([], adj[start][0][0], start)
    for _ in range(len(adj)):
        nxt = [x for x in adj[cur] if x[0] != prev][0]
        seq.append((fig.facets[cur][0], nxt[2]))
        prev, cur = (nxt[0], nxt[1])
    if cur != start:
        return None
    return seq

def placements(fig, mod, ridx, cyc_target, r2):
    """All placements of model mod with its ridge ridx onto the target ridge (cyclic ids)."""
    lab, ridge = mod.ridges[ridx]
    k = len(ridge)
    T = [fig.pos[i] for i in cyc_target]
    D = gram_schmidt([sub(T[1], T[0]), sub(T[2], T[0])], 2)
    W = complement(D, 4)
    cT = scal(arb(1) / k, [sum((t[j] for t in T), arb(0)) for j in range(4)])
    x0 = [dot(cT, w) for w in W]
    nx2 = dot(x0, x0)
    d2 = r2 - mod.rc2
    if not d2 >= 0 and d2 < 0:
        return []
    d = d2.sqrt() if d2 > 0 else arb(0).union(d2.abs_upper().sqrt())
    if nx2 < d2:
        return []
    nx = nx2.sqrt()
    cosv = d / nx
    if cosv > 1:
        return []
    sin2 = 1 - cosv * cosv
    sinv = sin2.sqrt() if sin2 > 0 else arb(0).union(sin2.abs_upper().sqrt())
    base = scal(1 / nx, x0)
    perp = [-base[1], base[0]]
    out = []
    for sg in (1, -1):
        nw = [cosv * base[0] + sg * sinv * perp[0], cosv * base[1] + sg * sinv * perp[1]]
        n = add(scal(nw[0], W[0]), scal(nw[1], W[1]))
        for s in range(k):
            for rev in (False, True):
                order = [ridge[(s - t) % k] if rev else ridge[(s + t) % k] for t in range(k)]
                A = [mod.X[order[t]] for t in range(k)]
                ok = True
                for a, b in itertools.combinations(range(k), 2):
                    if not dist2(A[a], A[b]).overlaps(dist2(T[a], T[b])):
                        ok = False
                        break
                if not ok:
                    continue
                B = [sub(T[t], scal(d, n)) for t in range(3)]
                Arows = [A[0], A[1], A[2]]
                Qcols = []
                Qt = []
                for j in range(4):
                    Qt.append(solve3(Arows, [B[t][j] for t in range(3)]))
                Y = [[dot(Qt[j], x) for j in range(4)] for x in mod.X]
                Y = [add(y, scal(d, n)) for y in Y]
                iso = True
                for a in range(3):
                    for b in range(3):
                        g = sum((Qt[j][a] * Qt[j][b] for j in range(4)), arb(0))
                        if not g.contains(1 if a == b else 0):
                            iso = False
                if not iso:
                    continue
                out.append((Y, n, d, order))
    return out

def search_class(models, cycles, Rball, limit=10 ** 6, audit=None):
    if audit is None:
        audit = {}
    audit.setdefault('undecided', 0)
    audit.setdefault('undecided_reasons', {})

    def unresolved(e):
        audit['undecided'] += 1
        reasons = audit['undecided_reasons']
        reasons[str(e)] = reasons.get(str(e), 0) + 1
    r2 = 1 - 1 / (4 * Rball * Rball)
    allowed_all = set((canon_cycle(c) for c in cycles))
    types = sorted(models)
    results, nodes = ({}, [0])
    for j, t0 in enumerate(types):
        allowed_types = set(types[j:])
        allowed = set((c for c in allowed_all if all((f in allowed_types for f, _ in c))))
        if not any((t0 in [f for f, _ in c] for c in allowed)):
            continue
        mod = models[t0]
        d = (r2 - mod.rc2).sqrt()
        Y = [x + [d] for x in mod.X]
        n0 = [arb(0), arb(0), arb(0), arb(1)]
        try:
            fig = try_place(Fig(), mod, Y, n0, d, allowed)
        except Refuted:
            continue
        except Undecided as e:
            unresolved(e)
            continue

        def rec(fig):
            nodes[0] += 1
            if nodes[0] > limit:
                raise RuntimeError('node limit')
            openr = [k for k, v in fig.ridges.items() if len(v) == 1]
            if not openr:
                es = set()
                for fi in range(len(fig.facets)):
                    es |= edges_of_facet(fig, fi)
                cys = [cycle_at(fig, e) for e in es]
                if all((c is not None and canon_cycle(c) in allowed for c in cys)):
                    sig = (tuple(sorted((f[0] for f in fig.facets))), tuple(sorted((canon_cycle(c) for c in cys))))
                    rep = results.setdefault(sig, dict(count=0, nV=len(fig.pos), nF=len(fig.facets), branches=[]))
                    rep['count'] += 1
                    rep['branches'].append(dict(seed=t0, pos=[[x.mid().str(50, radius=False) + ' +/- ' + x.rad().str(3, radius=False) for x in p] for p in fig.pos], facets=[[f[0], list(f[1])] for f in fig.facets]))
                return
            key = min(openr, key=lambda k: sorted(k))
            (fi, lab, cyc), = fig.ridges[key]
            seen = []
            for name in sorted(allowed_types):
                m = models[name]
                for ridx, (lab2, rv) in enumerate(m.ridges):
                    if lab2 != lab or len(rv) != len(cyc):
                        continue
                    for Y, n, dd, order in placements(fig, m, ridx, cyc, r2):
                        sig = (name, tuple(sorted((tuple((round(v, 6) for v in mid(y))) for y in Y))))
                        if sig in seen:
                            continue
                        seen.append(sig)
                        try:
                            o = try_place(fig, m, Y, n, dd, allowed, target=(rv, cyc))
                        except Refuted:
                            continue
                        except Undecided as e:
                            unresolved(e)
                            continue
                        rec(o)
        rec(fig)
    if audit['undecided']:
        raise Undecided(json.dumps(audit, sort_keys=True))
    return (results, nodes[0])

def run_class(pmax, ci):
    from mpmath import mpf
    cls = json.load(open('classes_p%d.json' % pmax))[ci]
    cyc = json.load(open('cert_stage1_5d_p%d.json' % pmax))
    Rball = arb(cls['R'][0]).union(arb(cls['R'][1]))
    cycles = [list(zip(cyc[i]['facets'], cyc[i]['cells'])) for i in cls['alive']]
    names = sorted(set((f for c in cycles for f, _ in c)))
    models = {n: Model(n) for n in names}
    t = time.time()
    audit = {}
    try:
        res, nodes = search_class(models, cycles, Rball, audit=audit)
    except Undecided:
        return dict(index=ci, R=cls['R'], status='OPEN', audit=audit, seconds=time.time() - t, vfs=[])
    return dict(index=ci, R=cls['R'], nodes=nodes, seconds=time.time() - t, status='COMPLETE', audit=audit, vfs=[dict(facets=list(k[0]), cycles=[list(map(list, c)) for c in k[1]], nV=v['nV'], nF=v['nF'], count=v['count'], branches=v['branches']) for k, v in res.items()])
if __name__ == '__main__':
    pmax = int(sys.argv[1])
    for ci in map(int, sys.argv[2:]):
        out = run_class(pmax, ci)
        print(json.dumps(out), flush=True)
        if out['status'] != 'COMPLETE':
            raise SystemExit('OPEN class: undecided identity; no complete signature list')
