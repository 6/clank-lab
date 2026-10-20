"""CNF encoder: a combinatorial-line-free subset of [3]^n with at least K points.

Variables 1..3^n are the points of [3]^n in lexicographic order
(point (x_1,...,x_n), x_i in {0,1,2}, has index 1 + sum x_i 3^(n-i)).
Variable true means the point is in the set.

Clauses:
  * line clauses: for every word over {0,1,2,*} with at least one *,
    not all three of its points are chosen;
  * unary counters (totalizers) over sub-cubes, built hierarchically:
    for an orientation (a permutation of the coordinates) a k-dim node is
    the sub-cube obtained by fixing the first n-k coordinates of the
    orientation.  Output bit j of a node (1-based) means "at least j
    chosen points in this sub-cube".  Every clause is valid under the
    intended assignment bit_j = [count >= j];
  * caps c_k on k-dim nodes (cap lemmas, proved separately);
  * the cardinality requirement on the root of orientation 0;
  * optional case constraints on the 6-dim slices (see --case).

Slices: slice (i, v) is {x : x_i = v}; it is the 6-dim node of the
orientation that starts with coordinate i, with fixed value v.
"""
import argparse
import itertools
import sys


class Enc:
    def __init__(self, n):
        self.n = n
        self.nv = 3 ** n
        self.clauses = []
        self.sem = {}

    def new(self, masks=None, j=None):
        self.nv += 1
        if masks is not None:
            self.sem[self.nv] = (masks, j)
        return self.nv

    def point(self, p):
        r = 0
        for x in p:
            r = 3 * r + x
        return r + 1

    def lines(self):
        n = self.n
        for w in itertools.product(range(4), repeat=n):
            if 3 not in w:
                continue
            self.clauses.append([-self.point(tuple(v if c == 3 else c for c in w)) for v in range(3)])

    def merge(self, A, B, L, masks=None):
        """A, B: (bits, exact). Returns (bits, exact) with len(bits) = L.

        bits[j-1] <-> count >= j for j <= L.  'exact' means the count can
        never exceed len(bits) (so 'not bit_{len+1}' is known true)."""
        a, ea = A
        b, eb = B
        L = min(L, len(a) + len(b))
        c = [self.new(masks, k + 1) for k in range(L)]
        # up: a_i & b_j -> c_{min(i+j, L)}
        for i in range(len(a) + 1):
            for j in range(len(b) + 1):
                if i + j == 0:
                    continue
                k = min(i + j, L)
                if i + j > L and ((i > 0 and i - 1 + j >= L) or (j > 0 and i + j - 1 >= L)):
                    continue  # implied by a pair with a smaller sum that already reaches L
                cl = [c[k - 1]]
                if i:
                    cl.append(-a[i - 1])
                if j:
                    cl.append(-b[j - 1])
                self.clauses.append(cl)
        # down: not a_{i+1} & not b_{j+1} -> not c_{i+j+1}
        for i in range(len(a) + 1):
            for j in range(len(b) + 1):
                k = i + j + 1
                if k > L:
                    continue
                cl = [-c[k - 1]]
                if i < len(a):
                    cl.append(a[i])
                elif not ea:
                    continue
                if j < len(b):
                    cl.append(b[j])
                elif not eb:
                    continue
                self.clauses.append(cl)
        exact = ea and eb and L == len(a) + len(b)
        return (c, exact)

    def node(self, orient, fixed, caps, store):
        """Counter of the sub-cube fixing coordinates orient[:len(fixed)]."""
        n = self.n
        d = n - len(fixed)
        if d == 0:
            p = [0] * n
            for c, v in zip(orient, fixed):
                p[c] = v
            return ([self.point(p)], True)
        ch = [self.node(orient, fixed + (v,), caps, store) for v in range(3)]
        cap = caps.get(d)
        full = 3 ** d
        L = full if cap is None else cap + 1
        masks = [7] * n
        for c, v in zip(orient, fixed):
            masks[c] = 1 << v
        masks_ab = list(masks)
        masks_ab[orient[len(fixed)]] = 3
        ab = self.merge(ch[0], ch[1], min(L, full), tuple(masks_ab))
        r = self.merge(ab, ch[2], min(L, full), tuple(masks))
        bits, exact = r
        if cap is not None and len(bits) > cap:
            self.clauses.append([-bits[cap]])
            bits = bits[:cap]
            exact = True
        store[(tuple(orient[:len(fixed)]), fixed)] = (bits, exact)
        return (bits, exact)


def build(n, K, caps, orients, case):
    e = Enc(n)
    e.lines()
    stores = []
    roots = []
    for o in orients:
        st = {}
        roots.append(e.node(list(o), (), caps, st))
        stores.append(st)
    bits, exact = roots[0]
    if K > len(bits):
        e.clauses.append([])
    elif K > 0:
        e.clauses.append([bits[K - 1]])

    def slice_bits(i, v):
        for o, st in zip(orients, stores):
            if o[0] == i:
                return st[((i,), (v,))]
        raise SystemExit('slice (%d,%d) needs an orientation starting with %d' % (i, v, i))

    def atleast(sb, t):
        b, ex = sb
        if t <= 0:
            return
        if t > len(b):
            e.clauses.append([])
        else:
            e.clauses.append([b[t - 1]])

    def atmost(sb, t):
        b, ex = sb
        if t < len(b):
            e.clauses.append([-b[t]])
        elif not ex:
            raise SystemExit('atmost on a non-exact counter beyond its length')

    if case is not None and 'prof' in case:
        # orientation-0 profile case: |slice(0,0)| = s0 >= |slice(0,1)| >= |slice(0,2)|
        sl = [slice_bits(0, v) for v in range(3)]
        s0, s1lo, s1hi = case['prof']
        atleast(sl[0], s0)
        atmost(sl[0], s0)
        for (hb, _), (lb, _) in ((sl[0], sl[1]), (sl[1], sl[2])):
            for t in range(1, min(len(hb), len(lb)) + 1):
                e.clauses.append([-lb[t - 1], hb[t - 1]])
            if len(lb) > len(hb):
                e.clauses.append([-lb[len(hb)]])
        if s1lo is not None:
            atleast(sl[1], s1lo)
        if s1hi is not None:
            atmost(sl[1], s1hi)
    elif case is not None:
        M = case['M']
        s00 = slice_bits(0, 0)
        atleast(s00, M)
        for i in range(n):
            for v in range(3):
                atmost(slice_bits(i, v), M)
        if case.get('order12'):
            # |slice(0,1)| >= |slice(0,2)|
            b1, _ = slice_bits(0, 1)
            b2, _ = slice_bits(0, 2)
            for t in range(1, min(len(b1), len(b2)) + 1):
                e.clauses.append([-b2[t - 1], b1[t - 1]])
            if len(b2) > len(b1):
                e.clauses.append([-b2[len(b1)]])
        if 's1' in case:
            atleast(slice_bits(0, 1), case['s1'])
            atmost(slice_bits(0, 1), case['s1'])
    return e


def parse_caps(s):
    return {i + 1: int(c) for i, c in enumerate(s.split(','))} if s else {}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('n', type=int)
    ap.add_argument('K', type=int)
    ap.add_argument('--caps', default='')
    ap.add_argument('--alldir', action='store_true', help='one orientation starting with each coordinate')
    ap.add_argument('--M', type=int, help='case: slice (0,0) is a largest slice, of size exactly-at-least M; all slices <= M')
    ap.add_argument('--order12', action='store_true')
    ap.add_argument('--s1', type=int)
    ap.add_argument('--s0', type=int, help='case: |slice(0,0)| = s0 >= |slice(0,1)| >= |slice(0,2)|')
    ap.add_argument('--s1lo', type=int)
    ap.add_argument('--s1hi', type=int)
    ap.add_argument('--map', help='write the semantic map: var masks threshold')
    ap.add_argument('-o', default='-')
    a = ap.parse_args()
    n = a.n
    caps = parse_caps(a.caps)
    orients = [tuple(range(n))]
    if a.alldir or a.M is not None:
        orients = [tuple([i] + [j for j in range(n) if j != i]) for i in range(n)]
    case = None
    if a.s0 is not None:
        case = {'prof': (a.s0, a.s1lo, a.s1hi)}
    elif a.M is not None:
        case = {'M': a.M, 'order12': a.order12}
        if a.s1 is not None:
            case['s1'] = a.s1
    e = build(n, a.K, caps, orients, case)
    out = sys.stdout if a.o == '-' else open(a.o, 'w')
    out.write('p cnf %d %d\n' % (e.nv, len(e.clauses)))
    for c in e.clauses:
        out.write(' '.join(map(str, c)) + ' 0\n')
    if out is not sys.stdout:
        out.close()
    if a.map:
        with open(a.map, 'w') as f:
            for v in sorted(e.sem):
                m, j = e.sem[v]
                f.write('%d %s %d\n' % (v, ''.join(map(str, m)), j))
    print(e.nv, len(e.clauses), file=sys.stderr)


if __name__ == '__main__':
    main()
