"""Interval branch-and-bound for the wedge lemma (W), all decisions in arb.

Reduction (exact).  Let kappa = 1/(2R), chat = c/|c|, r = sqrt(1 - kappa^2).
The VF sphere {|p| = 1, p.chat = kappa} is p = kappa chat + r sum_j s_j f_j,
s = (s_1, s_3, s_4, s_5) in the unit 3-sphere S^3 of R^4, with the
orthonormal basis f_j = H e_j (j = 1, 3, 4, 5) of chat-perp, H the
reflection I - w w^T/(1 + chat_2), w = e2 + chat (H e2 = -chat; smooth in
chat since chat_2 >= 0).  Then for p, p' on the VF sphere

    |p - p'|^2 = r^2 |s - s'|^2 = r^2 (4 - |s + s'|^2),

so |p - p'| >= L := 2 cos(pi/17) iff |s + s'|^2 <= E := 4 - L^2/r^2.
A fan vertex x (on the VF sphere) has s-image sigma_x = (x.f_j / r)_j, and
|p - x| >= 1 iff p.x <= 1/2 iff s.sigma_x <= tau := (1/2 - kappa^2)/r^2.
A fan facet N.p >= 0 is kappa N.chat + r sum_j s_j N.f_j >= 0.

Claim certified for a parameter box: no s, s' in S^3 satisfying all the
constraints have |s + s'|^2 <= E, and no such s and allowed fan vertex
sigma_x have |s + sigma_x|^2 <= E.  Boxes in s-space are dyadic boxes in
[-1, 1]^4 (bisection of the widest side); a box is discarded when |s|^2 = 1
or some constraint certainly fails on it; a pair of boxes (A, B) is decided
when the minimum of |z|^2 over the box A + B certainly exceeds E.
"""
from flint import arb

from wgeom import PI, ZERO, ONE, dot, Undecided

L2 = 4 * (PI / 17).cos() ** 2           # (2 cos(pi/17))^2


class Reduced:
    """s-space data of one parameter box (all arb)."""

    def __init__(self, G, drop=()):
        k = G.kappa
        r2 = 1 - k * k
        r = r2.sqrt()
        c = G.chat
        den = 1 + c[1]
        if not den > 0:
            raise Undecided("1 + chat_2 > 0 not certified")
        w = [c[0], 1 + c[1], c[2], c[3], c[4]]
        F = []
        for j in (0, 2, 3, 4):
            F.append([(ONE if i == j else ZERO) - c[j] * w[i] / den for i in range(5)])
        self.F, self.r = F, r
        self.tau = (1 / arb(2) - k * k) / r2
        self.E = 4 - L2 / r2
        self.sigma = {}
        for name, x, allowed in G.verts:
            self.sigma[name] = [dot(x, f) / r for f in F]
        cons = []     # (name, g0, G): g0 + G.s >= 0
        if "facet" in drop:
            pass
        elif getattr(G, "scaled", None):
            cons += G.scaled(F, r)
        else:
            for name, N in G.normals:
                cons.append(("facet " + name, k * dot(N, c), [r * dot(N, f) for f in F]))
        for name, x, allowed in G.verts:
            if "separation" in drop:
                continue
            cons.append(("sep " + name, self.tau, [-t for t in self.sigma[name]]))
        self.cons = cons
        rads = [t.rad() for _, g0, Gv in cons for t in [g0] + Gv]
        rads += [t.rad() for v in self.sigma.values() for t in v] + [self.E.rad()]
        self.coefrad = float(max(rads))      # spread caused by the parameter box
        self.allowed = [(name, self.sigma[name]) for name, x, al in G.verts if al]


class Node:
    __slots__ = ("lo", "hi", "s", "w", "feas", "kids", "why")

    def __init__(self, lo, hi):
        self.lo, self.hi = lo, hi
        self.s = [arb((l + h) / 2, (h - l) / 2) for l, h in zip(lo, hi)]
        self.w = max(h - l for l, h in zip(lo, hi))
        self.feas = None
        self.kids = None
        self.why = None


class Tree:
    def __init__(self, red, minw):
        self.red, self.minw = red, minw
        self.root = Node((-1.0,) * 4, (1.0,) * 4)
        self.nodes = 0
        self.pairtests = 0
        self.finest = 2.0          # smallest s-box width created
        self.check(self.root)

    def check(self, nd):
        """Feasibility (possible admissible point of S^3 in the box)."""
        self.nodes += 1
        lo2, hi2 = ZERO, ZERO
        for l, h in zip(nd.lo, nd.hi):
            a, b = arb(l) * arb(l), arb(h) * arb(h)
            hi2 += a.max(b)
            if not (l <= 0 <= h):
                lo2 += a.min(b)
        if lo2 > 1 or hi2 < 1:
            nd.feas, nd.why = False, "sphere"
            return
        for name, g0, G in self.red.cons:
            v = g0 + G[0] * nd.s[0] + G[1] * nd.s[1] + G[2] * nd.s[2] + G[3] * nd.s[3]
            if v < 0:
                nd.feas, nd.why = False, name
                return
        nd.feas = True

    def children(self, nd):
        if nd.kids is None:
            j = max(range(4), key=lambda i: nd.hi[i] - nd.lo[i])
            m = (nd.lo[j] + nd.hi[j]) / 2
            hi1 = nd.hi[:j] + (m,) + nd.hi[j + 1:]
            lo2 = nd.lo[:j] + (m,) + nd.lo[j + 1:]
            kids = [Node(nd.lo, hi1), Node(lo2, nd.hi)]
            self.finest = min(self.finest, kids[0].w)
            for c in kids:
                self.check(c)
            nd.kids = [c for c in kids if c.feas]
        return nd.kids

    def far(self, s, t):
        """(decided, key): decided iff min |s + t|^2 over the box sum is
        certainly > E (s, t lists of arb); key orders the open pairs."""
        self.pairtests += 1
        tot = ZERO
        for a, b in zip(s, t):
            tot += (a + b).abs_lower() ** 2
        return tot > self.red.E, float(tot.mid())

    def pairs(self, budget=None):
        """Certify all pairs of admissible points.  Returns None (certified),
        a pair of boxes still open at the minimal width, or "budget".
        Depth-first; among siblings the smallest lower bound is explored
        first (only the order of work depends on floats)."""
        if not self.root.feas:
            return None
        stack = []

        def push(cands):
            open_ = []
            for A, B in cands:
                ok, key = self.far(A.s, B.s)
                if not ok:
                    open_.append((key, A, B))
            open_.sort(key=lambda t: -t[0])
            stack.extend((A, B) for _, A, B in open_)
        push([(self.root, self.root)])
        while stack:
            if budget and self.pairtests > budget:
                return "budget"
            A, B = stack.pop()
            if A is B:
                if A.w <= self.minw:
                    return (A, B)
                ks = self.children(A)
                push([(ks[i], ks[j]) for i in range(len(ks)) for j in range(i, len(ks))])
                continue
            if A.w < B.w:
                A, B = B, A
            if A.w <= self.minw:
                return (A, B)
            push([(c, B) for c in self.children(A)])
        return None

    def vertices(self, budget=None):
        """Certify admissible points vs allowed fan vertices (same scheme)."""
        if not self.root.feas:
            return None
        for name, sig in self.red.allowed:
            stack = []

            def push(cands):
                open_ = []
                for A in cands:
                    ok, key = self.far(A.s, sig)
                    if not ok:
                        open_.append((key, A))
                open_.sort(key=lambda t: -t[0])
                stack.extend(A for _, A in open_)
            push([self.root])
            while stack:
                if budget and self.pairtests > budget:
                    return "budget"
                A = stack.pop()
                if A.w <= self.minw:
                    return (A, name)
                push(self.children(A))
        return None
