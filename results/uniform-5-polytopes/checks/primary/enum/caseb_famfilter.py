"""Case B, step (P1) of CASEB.md: the family-polygon filter, in ball arithmetic.

For every closable type-(i) configuration c = (q_1..q_k) (cyclic, entries 3..16,
sum(1 - 2/q_i) < 2) that contains a family polygon q in {7, 9, 11, ..., 16}, the cycle
around that q-gon contains {q}x{n} and must be of type (i)_q with configuration (n, c'')
or of type (ii)_q.  With R^2 = r_n^2 + R_c^2 this needs X := R_c^2 - r_q^2 to equal
  (ii)_q:        h_A(q)^2/4                    (R_c = R_{A_q})
  c'' = (4,4):   1/4
  c'' = (3,3,3): h_A(n)^2/4 in [h_A(17)^2/4, 3/16)
  c'' = (3,6):   (1-e)/(3-4e), e = sin^2(pi/n), in (1/3, value at n = 17]
  c'' = (3,7), (3,8), (3,9), (4,5): delta(n) at the finitely many n allowed by the
                 angle sum (n <= 41, 23, 17, 19)
(c'' = (3,3), (3,4), (3,5) are not closable: the triangle with sides 2cos(pi/n), 1|1, ...
is not acute.)  A configuration is EXCLUDED if, for one of its family polygons, X differs
from all of these (certified by disjoint balls/intervals).  Output: one line per
configuration.  Run: python3 caseb_famfilter.py

CLOSABILITY-UNDECIDED marks f(s_min) = 2 pi within the balls: (3,3,4), (3,4,6), (3,5,10).
They are exactly degenerate (right triangles of chords:
1^2 + 1^2 = (2cos(pi/4))^2, 1^2 + (2cos(pi/4))^2 = (2cos(pi/6))^2,
1^2 + (2cos(pi/5))^2 = (2cos(pi/10))^2 = (5 + sqrt5)/2), so the centre lies on the
hyperplane of the facet {n}x{q_max}: impossible for a convex polytope (centre interior).
None of the three contains a family polygon.
"""
import itertools, sys
from flint import arb, ctx
ctx.prec = 200
PI = arb.pi()
FAM = {7, 9, 11, 12, 13, 14, 15, 16}
DROP = __import__('os').environ.get('FAMFILTER_CORRUPT', '')

def ch(q):
    return 2 * (PI / q).cos()

def rn2(n):
    return 1 / (4 * (PI / n).sin() ** 2)

def hA2(n):
    return 1 - 1 / (4 * (PI / (2 * n)).cos() ** 2)

def closure_f(cfg, s):
    """sum of central angles on a circle of radius s (s = sin alpha) for the chords of cfg."""
    return sum((2 * (ch(q) / (2 * s)).asin() for q in cfg))

def Rc2(cfg):
    """R_c^2 for a closable configuration (None if not closable).  f(s) is strictly decreasing
    in s on [s_min, 1]; f(1) = angle sum < 2 pi; closable iff f(s_min) > 2 pi (centre strictly
    inside the polygon).  Bisection in s with certified signs."""
    qm = max(cfg)
    smin = ch(qm) / 2
    f0 = sum((PI if q == qm else 2 * (ch(q) / (2 * smin)).asin() for q in cfg)) - 2 * PI
    if f0 < 0:
        return None
    if not f0 > 0:
        return 'UNDECIDED'
    lo, hi = (smin, arb(1))
    lo = arb((smin + arb(10) ** (-40)).mid())
    hi = arb(1)
    if not closure_f(cfg, lo) - 2 * PI > 0:
        return 'UNDECIDED'
    for _ in range(170):
        mid = arb(((lo + hi) / 2).mid())
        v = closure_f(cfg, mid) - 2 * PI
        if v > 0:
            lo = mid
        elif v < 0:
            hi = mid
        else:
            break
    s = lo.union(hi)
    return 1 / (4 * (1 - s * s))

def tri_delta(n, p1, p2):
    """delta_{c''}(n) = R_{(n,p1,p2)}^2 - r_n^2 via the circumradius of the triangle of chords
    (None if the triangle is not acute, i.e. the configuration is not closable)."""
    A, B, C = (ch(n), ch(p1), ch(p2))
    if not A * A < B * B + C * C:
        return None
    a2, b2, c2 = (A * A, B * B, C * C)
    s16 = 2 * (a2 * b2 + b2 * c2 + c2 * a2) - (a2 * a2 + b2 * b2 + c2 * c2)
    rho2 = a2 * b2 * c2 / s16
    return 1 / (4 * (1 - rho2)) - rn2(n)

def configs(qmax=16):
    out = set()
    for k in (3, 4, 5):
        for t in itertools.combinations_with_replacement(range(3, qmax + 1), k):
            if sum((1 - arb(2) / q for q in t)) < 2:
                for p in set(itertools.permutations(t)):
                    rots = [p[i:] + p[:i] for i in range(k)]
                    rots += [tuple(reversed(x)) for x in rots]
                    out.add(min(rots))
    return sorted(out)

def main():
    tests = []
    lo333, hi333 = (hA2(17) / 4, arb(3) / 16)
    e17 = (PI / 17).sin() ** 2
    lo36, hi36 = (arb(1) / 3, (1 - e17) / (3 - 4 * e17))
    sporadic = []
    for p1, p2, nmax in [(3, 7, 41), (3, 8, 23), (3, 9, 17), (4, 5, 19)]:
        for n in range(17, nmax + 1):
            d = tri_delta(n, p1, p2)
            if d is not None:
                sporadic.append(((p1, p2), n, d))
    for p1, p2, nmax in [(3, 7, 41), (3, 8, 23), (3, 9, 17), (4, 5, 19)]:
        for n in (nmax, nmax + 1):
            ssum = 1 - arb(2) / n + (1 - arb(2) / p1) + (1 - arb(2) / p2)
            if not (ssum < 2) == (n <= nmax):
                raise AssertionError((p1, p2, n))
    for c2 in [(3, 3), (3, 4), (3, 5)]:
        for n in (17, 100, 10 ** 6):
            if not tri_delta(n, *c2) is None:
                raise AssertionError()
    nconf = nclos = nexcl = 0
    survivors = []
    for cfg in configs():
        nconf += 1
        R2 = Rc2(cfg)
        if R2 == 'UNDECIDED':
            print('CLOSABILITY-UNDECIDED', cfg)
            continue
        if R2 is None:
            print('NOT-CLOSABLE', cfg)
            continue
        nclos += 1
        fam = sorted(set(cfg) & FAM)
        if not fam:
            print('NO-FAMILY', cfg, 'Rc=%s' % R2.sqrt().str(8))
            continue
        excluded_by = None
        notes = []
        for q in fam:
            X = R2 - rn2(q)
            hits = []
            if not X != hA2(q) / 4:
                hits.append('(ii)_q')
            if not X != arb(1) / 4 and DROP != '(4,4)':
                hits.append('(4,4)')
            if not (X < lo333 or X > hi333):
                hits.append('(3,3,3)')
            if not (X < lo36 or X > hi36):
                hits.append('(3,6)')
            for c2, n, d in sporadic:
                if not X != d:
                    hits.append('%s@n=%d' % (c2, n))
            if not hits:
                excluded_by = q
                break
            notes.append('q=%d:%s' % (q, '+'.join(hits)))
        if excluded_by is not None:
            nexcl += 1
            print('EXCLUDED', cfg, 'by q=%d' % excluded_by, 'Rc=%s' % R2.sqrt().str(8))
        else:
            survivors.append(cfg)
            print('SURVIVES', cfg, 'Rc=%s' % R2.sqrt().str(8), ' '.join(notes))
    print('configurations %d, closable %d, with family polygon and excluded %d, surviving %s' % (nconf, nclos, nexcl, survivors))
if __name__ == '__main__':
    main()
