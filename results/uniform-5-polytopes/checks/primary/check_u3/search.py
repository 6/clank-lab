"""Step 1: every geometric realisation of a vertex-figure signature.

Work in R^5 with the centre of P at the origin.  The star of v0 is built
facet by facet: a facet of type K is a placed copy of the template K (an
affine isometry y -> L y + c from the template's R^4 into a hyperplane of
R^5 at distance sqrt(R^2 - R_K^2) from the origin) with template base vertex
at v0.  A new facet is glued along an open cell C (a cell through v0 lying in
one placed facet so far): its hyperplane is the second hyperplane through
aff(C) at its distance from the origin (the first one is the old facet's), on
the other side, and its template cell is matched to C by a correspondence of
the cell's vertex-figure polygons (rotations and reflections; mirror images
of chiral facets arise from the reflections).  This determines the facet.

A branch is discarded only for a certified reason:
  * two vertices at distance in (0, 1) (separation lemma), or
  * a vertex strictly outside a facet hyperplane (convexity), or
  * a placement that is not an isometry / does not match the cell
    (certified mismatch of a vertex), or
  * a combinatorial contradiction (a cell in three facets, two cells through
    v0 sharing three vertex-figure points, a polygon with two sizes, a facet
    type used more often than the signature allows, a polygon whose facet
    multiset fits no allowed word, a wrong label).
Two enclosures closer than 1/2 are the same vertex (separation lemma).
"""
import itertools
from collections import Counter
from mpmath import iv
from ivla import (ZERO, ONE, HALF, dot, norm2, dist2, vsub, vadd, vscale, matvec,
                  vmid)
from templates import template


class Contradiction(Exception):
    pass


class Undecided(Exception):
    pass


def positive_height(d2, reason):
    """Strict positivity is required; overlap with zero is not a rejection."""
    if d2.b <= 0:
        raise Contradiction(reason)
    if not d2.a > 0:
        raise Undecided(reason)
    return iv.sqrt(d2)


def canon_word(word):
    """lexicographically least over rotations and reversals (labels shifted
    so that each label stays between the same two facets)."""
    k = len(word)
    w = [tuple(x) for x in word]
    rev = [(w[(k - 1 - i) % k][0], w[(k - 2 - i) % k][1]) for i in range(k)]
    best = None
    for cand in (w, rev):
        for r in range(k):
            c = cand[r:] + cand[:r]
            if best is None or c < best:
                best = c
    return tuple(best)


class State:
    __slots__ = ('pts', 'facets', 'cells', 'polys', 'counts', 'R2')

    def copy(self):
        s = State()
        s.R2 = self.R2
        s.pts = list(self.pts)
        s.facets = list(self.facets)
        s.cells = {k: list(v) for k, v in self.cells.items()}
        s.polys = {k: [v[0], list(v[1])] for k, v in self.polys.items()}
        s.counts = Counter(self.counts)
        return s


class Facet:
    __slots__ = ('type', 'T', 'L', 'c', 'c2', 'm', 'pts')

    def __init__(self, type_, T, L, c, m):
        self.type = type_
        self.T = T
        self.L = L
        self.c = c
        self.c2 = norm2(c)
        self.m = m  # template neighbour index -> point id

    def apply(self, y):
        return vadd(matvec(self.L, y), self.c)


class Signature:
    def __init__(self, vf):
        self.types = Counter(vf['facets'])
        self.words = Counter(canon_word(w) for w in vf['cycles'])
        self.word_multisets = [Counter(f for f, _ in w) for w in self.words]
        self.maxk = max(len(w) for w in self.words)


def first_state(R2, K):
    T = template(K)
    d2 = R2 - T.R2
    d = positive_height(d2, "facet radius >= R")
    L = [[ZERO] * 4] + [[ONE if r == k else ZERO for k in range(4)] for r in range(4)]
    c = [d, ZERO, ZERO, ZERO, ZERO]
    s = State()
    s.R2 = R2
    v0 = vadd(matvec(L, T.V[0]), c)
    s.pts = [v0]
    s.facets = []
    s.cells = {}
    s.polys = {}
    s.counts = Counter()
    m = {}
    for j in T.nb:
        s.pts.append(vadd(matvec(L, T.V[j]), c))
        m[j] = len(s.pts) - 1
    F = Facet(K, T, L, c, m)
    _register(s, F, None, None)
    return s


def _register(s, F, glued_cell_key, sig):
    """add facet F (points already resolved in F.m) to state s; raise
    Contradiction on a certified violation."""
    fi = len(s.facets)
    s.facets.append(F)
    s.counts[F.type] += 1
    if sig is not None and s.counts[F.type] > sig.types[F.type]:
        raise Contradiction("type count")
    T = F.T
    newkeys = []
    for ci, cell in enumerate(T.cells):
        key = frozenset(F.m[t] for t in cell['poly'])
        lst = s.cells.get(key)
        if lst is None:
            s.cells[key] = [(fi, ci)]
            newkeys.append(key)
        else:
            if len(lst) >= 2:
                raise Contradiction("cell in three facets")
            fj, cj = lst[0]
            G = s.facets[fj]
            if G.T.cells[cj]['label'] != cell['label']:
                raise Contradiction("cell label")
            if key != glued_cell_key:
                cell_patch_check(G, cj, F, ci)
            lst.append((fi, ci))
    for key in newkeys:
        for k2 in s.cells:
            if k2 is not key and k2 != key and len(k2 & key) >= 3:
                raise Contradiction("two cells through v0 share three VF points")
    for pk, pd in T.polys.items():
        a, b = tuple(pk)
        key = frozenset((F.m[a], F.m[b]))
        ent = s.polys.get(key)
        if ent is None:
            s.polys[key] = [pd['p'], [F.type]]
        else:
            if ent[0] != pd['p']:
                raise Contradiction("polygon size")
            ent[1].append(F.type)
            if sig is not None:
                if len(ent[1]) > sig.maxk:
                    raise Contradiction("polygon degree")
                cnt = Counter(ent[1])
                if not any(all(cnt[t] <= ms[t] for t in cnt) for ms in sig.word_multisets):
                    raise Contradiction("polygon word")


def cell_patch_check(F, ci, G, cj):
    """the cell ci of F and the cell cj of G must be the same placed cell:
    compare the images of their vertices within distance 2 of the base."""
    A = [F.apply(F.T.V[t]) for t in F.T.cells[ci]['patch']]
    B = [G.apply(G.T.V[t]) for t in G.T.cells[cj]['patch']]
    if len(A) != len(B):
        raise Contradiction("cell patch size")
    Bm = [vmid(b) for b in B]
    for a in A:
        am = vmid(a)
        ok = False
        for b, bm in zip(B, Bm):
            if sum((x - y) ** 2 for x, y in zip(am, bm)) < 0.25:
                d = dist2(a, b)
                if d.b < 0.25:
                    # closer than 1/2: the same vertex (separation lemma), so
                    # a certified gap is a contradiction
                    if d.a > 0:
                        raise Contradiction("cell patch mismatch")
                    ok = True
                    break
        if not ok:
            # certify the mismatch against every point
            for b in B:
                d = dist2(a, b)
                if not d.a > 0:
                    raise Undecided("cell patch")
            raise Contradiction("cell patch mismatch")


def options(s, sig, key):
    """gluing options at the open cell `key`."""
    (fi, ci), = s.cells[key]
    F = s.facets[fi]
    cell = F.T.cells[ci]
    lab = cell['label']
    X = [F.m[t] for t in cell['poly']]
    n = len(X)
    # polygon sizes of the open cell's VF polygon edges
    ep = []
    for k in range(n):
        ep.append(s.polys[frozenset((X[k], X[(k + 1) % n]))][0])
    out = []
    for K in sorted(sig.types):
        if s.counts[K] >= sig.types[K]:
            continue
        T = template(K)
        seen = set()
        for cj, c2 in enumerate(T.cells):
            if c2['label'] != lab or len(c2['poly']) != n:
                continue
            P = c2['poly']
            tp = [T.polys[frozenset((P[k], P[(k + 1) % n]))]['p'] for k in range(n)]
            for k0 in range(n):
                for dr in (1, -1):
                    sig_map = [X[(k0 + dr * k) % n] for k in range(n)]
                    # edge (P[k], P[k+1]) maps to (sig_map[k], sig_map[k+1])
                    good = True
                    for k in range(n):
                        a, b = sig_map[k], sig_map[(k + 1) % n]
                        if s.polys[frozenset((a, b))][0] != tp[k]:
                            good = False
                            break
                    if not good:
                        continue
                    # deduplicate under the stabiliser of the base
                    pm = dict(zip(P, sig_map))
                    ck = min(tuple(sorted((int(perm[j]), v) for j, v in pm.items()))
                             for perm in T.stab_perm)
                    if ck in seen:
                        continue
                    seen.add(ck)
                    out.append((K, cj, sig_map))
    return fi, ci, out


def place(s, fi, ci, K, cj, sig_map, sig):
    """new state with facet K glued to facet fi along its cell ci, or raise."""
    F = s.facets[fi]
    T = template(K)
    cell = F.T.cells[ci]
    pC = F.apply(cell['centre'])
    pC2 = norm2(pC)
    pCn = iv.sqrt(pC2)
    u = [x / pCn for x in pC]
    e = vsub(F.c, vscale(dot(F.c, u), u))
    en = iv.sqrt(norm2(e))
    e = [x / en for x in e]
    d2 = s.R2 - T.R2
    positive_height(d2, "facet radius")
    a = d2 / pCn
    b2 = d2 - a * a
    if not b2.a > 0:
        raise Undecided("degenerate hyperplane")
    b = iv.sqrt(b2)
    c = vsub(vscale(a, u), vscale(b, e))
    v0 = s.pts[0]
    P = T.cells[cj]['poly']
    cols = [vsub(v0, c)] + [vsub(s.pts[sig_map[k]], c) for k in range(3)]
    X = [[cols[k][r] for k in range(4)] for r in range(5)]
    Yinv = T.cells[cj]['Yinv']
    L = [[sum((X[r][k] * Yinv[k][q] for k in range(4)), ZERO) for q in range(4)]
         for r in range(5)]
    # isometry check
    for q1 in range(4):
        for q2 in range(q1, 4):
            g = sum((L[r][q1] * L[r][q2] for r in range(5)), ZERO)
            tgt = 1 if q1 == q2 else 0
            if g.a > tgt or g.b < tgt:
                raise Contradiction("not an isometry")
    G = Facet(K, T, L, c, {})
    for k in range(3, len(P)):
        y = G.apply(T.V[P[k]])
        d = dist2(y, s.pts[sig_map[k]])
        if d.a > 0:
            raise Contradiction("polygon mismatch")
        if not d.b < 0.25:
            raise Undecided("polygon point")
    # cell consistency with the old facet
    cell_patch_check(F, ci, G, cj)
    s2 = s.copy()
    m = {}
    pm = dict(zip(P, sig_map))
    newpts = []
    for j in T.nb:
        if j in pm:
            m[j] = pm[j]
            continue
        x = G.apply(T.V[j])
        pid = resolve_point(s2, x)
        if pid < 0:
            s2.pts.append(x)
            pid = len(s2.pts) - 1
            newpts.append(pid)
        m[j] = pid
    if len(set(m.values())) != len(m):
        raise Contradiction("two neighbours of a facet coincide")
    G.m = m
    own = set(m.values())
    # convexity: old points vs new hyperplane, new points vs old hyperplanes
    for pid in range(1, len(s2.pts)):
        if pid in own:
            continue
        if (dot(s2.pts[pid], c) - G.c2).a > 0:
            raise Contradiction("convexity (new facet)")
    for pid in newpts:
        x = s2.pts[pid]
        for H in s2.facets:
            if (dot(x, H.c) - H.c2).a > 0:
                raise Contradiction("convexity (new point)")
    key = frozenset(F.m[t] for t in cell['poly'])
    _register(s2, G, key, sig)
    return s2


def resolve_point(s, x):
    for pid in range(1, len(s.pts)):
        d = dist2(x, s.pts[pid])
        if d.b < 0.25:
            if d.a > 0:
                raise Contradiction("separation (distinct points closer than 1/2)")
            return pid
        if d.a > 0 and d.b < 1:
            raise Contradiction("separation")
        if d.a <= 0 <= d.b:
            raise Undecided("point identity")
    return -1


def open_cells(s):
    return [k for k, v in s.cells.items() if len(v) == 1]


def finish_check(s, sig):
    """complete VF: facet multiset, words, strict convexity."""
    if s.counts != sig.types:
        return None, "facet multiset"
    words = Counter()
    for key, (p, types) in s.polys.items():
        w = polygon_word(s, key)
        if w is None:
            return None, "polygon not a single cycle"
        words[canon_word(w)] += 1
    if words != sig.words:
        return None, "words"
    weak = 0
    for fi, F in enumerate(s.facets):
        own = set(F.m.values())
        for pid in range(1, len(s.pts)):
            if pid in own:
                continue
            v = dot(s.pts[pid], F.c) - F.c2
            if v.a > 0:
                return None, "convexity"
            if not v.b < 0:
                weak += 1
    return weak, "ok"


def polygon_word(s, key):
    a, b = tuple(key)
    # facets containing the polygon, with their two cells (keys)
    inc = {}
    for fi, F in enumerate(s.facets):
        inv = {v: j for j, v in F.m.items()}
        if a in inv and b in inv:
            tk = frozenset((inv[a], inv[b]))
            if tk in F.T.polys:
                cl = F.T.polys[tk]['cells']
                inc[fi] = [frozenset(F.m[t] for t in F.T.cells[c]['poly']) for c in cl]
    if not inc:
        return None
    start = min(inc)
    word = []
    f = start
    cprev = None
    seen = set()
    while True:
        seen.add(f)
        c0, c1 = inc[f]
        cnext = c1 if c0 == cprev else c0
        if cprev is None:
            cnext = c0
        lab = _cell_label(s, cnext)
        word.append((s.facets[f].type, lab))
        others = [g for g, _ in s.cells[cnext] if g != f]
        if len(others) != 1:
            return None
        g = others[0]
        cprev = cnext
        f = g
        if f == start:
            break
        if f in seen:
            return None
    if len(seen) != len(inc):
        return None
    return word


def _cell_label(s, key):
    fi, ci = s.cells[key][0]
    return s.facets[fi].T.cells[ci]['label']


def choose_open(s, sig):
    best = None
    for key in open_cells(s):
        fi, ci, opts = options(s, sig, key)
        if best is None or len(opts) < len(best[2]):
            best = (fi, ci, opts)
            if len(opts) <= 1:
                break
    return best


def realise(R2, sig, stats=None, first=None, limit_nodes=None):
    """all complete states (realisations) of the signature at R^2 in R2."""
    if stats is None:
        stats = Counter()
    stats['undecided'] += 0
    if first is None:
        # rarest type, smallest stabiliser
        first = min(sig.types, key=lambda K: (sig.types[K] * len(template(K).stab), K))
    out = []
    try:
        s0 = first_state(R2, first)
    except Contradiction as e:
        stats['root:' + str(e)] += 1
        return out, stats
    except Undecided as e:
        stats['undecided'] += 1
        stats['undecided:root:' + str(e)] += 1
        return out, stats
    stack = [s0]
    while stack:
        s = stack.pop()
        stats['nodes'] += 1
        if limit_nodes and stats['nodes'] > limit_nodes:
            raise RuntimeError("node limit")
        oc = open_cells(s)
        if not oc:
            weak, why = finish_check(s, sig)
            if weak is None:
                stats['final:' + why] += 1
            else:
                stats['complete'] += 1
                out.append((s, weak))
            continue
        fi, ci, opts = choose_open(s, sig)
        if not opts:
            stats['dead:no option'] += 1
        for (K, cj, sm) in opts:
            try:
                s2 = place(s, fi, ci, K, cj, sm, sig)
            except Contradiction as e:
                stats['cut:' + str(e)] += 1
                continue
            except Undecided as e:
                stats['undecided'] += 1
                stats['undecided:place:' + str(e)] += 1
                continue
            stack.append(s2)
    return out, stats
