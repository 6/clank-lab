"""Independent checker for step B2 of Case B (uniform-5-polytopes, CASEB.md).

Claim B2: for every n >= 17 and every cycle of facets around an n-gon F of a
convex uniform 5-polytope with unit edges, the forced circumradius R lies in
no interval of Omega (the certified stage-1 roots, polygons <= 16).

Rigour: every quantity that decides anything is an mpmath.iv interval at
IV_PREC bits (outward rounded).  mpmath.iv has no arcsin, so arcsin is
enclosed by verification: a high-precision non-rigorous value theta is
widened and sin(theta_lo) < x < sin(theta_hi) is checked with iv.sin
(sin is increasing on [0, pi/2]).  Non-rigorous mp values are used only to
propose brackets, which are then verified with intervals.

Written without reading the producer (enum/).  Derivations: DERIVATION.md.
"""
import argparse
import bisect
import itertools
import json
import sys
import time
from fractions import Fraction
import mpmath
from mpmath import iv, mp
IV_PREC = 200
iv.prec = IV_PREC
mp.prec = IV_PREC + 20
QMAX = 397
NMIN = 17
PI = iv.pi
ONE = iv.mpf(1)
HALF = iv.mpf(1) / 2

def pt(x):
    """Point interval of an mp/mpf number (exact: x is a binary float)."""
    return iv.mpf(x)

def lo(x):
    return x.a

def hi(x):
    return x.b

def contains_zero(x):
    return x.a <= 0 <= x.b

def sign(x):
    if x.a > 0:
        return 1
    if x.b < 0:
        return -1
    return 0
EPS_ANG = mpmath.mpf(2) ** (-(IV_PREC - 12))

def rasin(x):
    """Rigorous enclosure of arcsin(x) for an interval x inside (0, 1].

    Returns None if x is not certainly inside (0, 1]."""
    xa, xb = (x.a, x.b)
    if xa <= 0 or xb > 1:
        return None
    half_pi = PI / 2
    th = mp.asin(mp.mpf(xa))
    eps = EPS_ANG
    while True:
        t_lo = th - eps
        if t_lo <= 0:
            t_lo = mpmath.mpf(0)
            break
        if not (pt(t_lo).a >= 0 and pt(t_lo).b <= half_pi.a):
            raise ArithmeticError('rasin lower proposal outside principal domain')
        if iv.sin(pt(t_lo)).b < xa:
            break
        eps *= 16
        if eps > 1e-20:
            raise ArithmeticError('rasin lower verification failed')
    if xb == 1:
        t_hi = half_pi.b
    else:
        th = mp.asin(mp.mpf(xb))
        eps = EPS_ANG
        while True:
            t_hi = th + eps
            if t_hi >= half_pi.a:
                t_hi = half_pi.b
                break
            if iv.sin(pt(t_hi)).a > xb:
                break
            eps *= 16
            if eps > 1e-20:
                raise ArithmeticError('rasin upper verification failed')
    return iv.mpf([t_lo, t_hi])
_cache = {}

def cospi(q):
    """cos(pi/q) as an interval (exact 1/2, sqrt2/2 for q = 3, 4)."""
    key = ('c', q)
    if key not in _cache:
        if q == 3:
            v = HALF
        elif q == 4:
            v = iv.sqrt(iv.mpf(2)) / 2
        else:
            v = iv.cos(PI / q)
        _cache[key] = v
    return _cache[key]

def r2(n):
    """r_n^2 = 1/(4 sin^2(pi/n)), the squared circumradius of a unit {n}."""
    key = ('r2', n)
    if key not in _cache:
        s = iv.sin(PI / n)
        _cache[key] = ONE / (4 * s * s)
    return _cache[key]

def hA2(n):
    """h_A^2 = 1 - 1/(4 cos^2(pi/(2n))): squared height of the unit A_n."""
    key = ('h2', n)
    if key not in _cache:
        c = iv.cos(PI / (2 * n))
        _cache[key] = ONE - ONE / (4 * c * c)
    return _cache[key]

class Omega:

    def __init__(self, intervals):
        items = []
        for a, b, idx in intervals:
            ia, ib = (iv.mpf(a), iv.mpf(b))
            if ia.a > ib.b:
                raise ValueError('bad Omega interval %r' % ((a, b, idx),))
            items.append((ia.a, ib.b, idx))
        items.sort(key=lambda t: t[0])
        self.items = items
        self.los = [t[0] for t in items]
        pm = []
        m = None
        for t in items:
            m = t[1] if m is None or t[1] > m else m
            pm.append(m)
        self.prefmax = pm
        self.max = pm[-1]
        self.min = items[0][0]

    def gap(self, R):
        """Relative distance from R to the nearest Omega endpoint."""
        j = bisect.bisect_right(self.los, R.b)
        best = None
        if j < len(self.los):
            best = self.los[j] - R.b
        if j > 0:
            d = R.a - self.prefmax[j - 1]
            best = d if best is None or d < best else best
        return best / R.a

    def hits(self, R):
        """Omega intervals [a, b] with a <= R.b and b >= R.a (overlap)."""
        j = bisect.bisect_right(self.los, R.b)
        if j == 0 or self.prefmax[j - 1] < R.a:
            return []
        out = []
        for k in range(j - 1, -1, -1):
            if self.prefmax[k] < R.a:
                break
            if self.items[k][1] >= R.a:
                out.append(self.items[k])
        return out

def angle_ok(qs):
    """sum(1 - 2/q_i) < 2 (tangent cone pointed), exact."""
    return sum((1 - Fraction(2, q) for q in qs)) < 2

def enumerate_multisets(qmax):
    """All sorted (q_1 <= ... <= q_k), k = 3, 4, 5, 3 <= q_i <= qmax, with
    sum(1 - 2/q_i) < 2.  Loops break as soon as the exact angle sum fails
    (it is increasing in each entry), so the enumeration is complete."""
    out = []

    def rec(prefix, start, k):
        if len(prefix) == k:
            out.append(tuple(prefix))
            return
        for q in range(start, qmax + 1):
            rest = k - len(prefix)
            if not angle_ok(prefix + [q] * rest):
                break
            rec(prefix + [q], q, k)
    for k in (3, 4, 5):
        rec([], 3, k)
    return out

def bracelets(ms):
    """Number of cyclic arrangements of the multiset up to rotation and
    reflection, and up to rotation only."""
    k = len(ms)
    seqs = set(itertools.permutations(ms))
    rot, dih = (set(), set())
    for s in seqs:
        rots = [s[i:] + s[:i] for i in range(k)]
        rot.add(min(rots))
        r = tuple(reversed(s))
        rots += [r[i:] + r[:i] for i in range(k)]
        dih.add(min(rots))
    return (len(dih), len(rot))

def f_mp(qs, s):
    return sum((2 * mp.asin(min(mp.cos(mp.pi / q) / s, 1)) for q in qs)) - 2 * mp.pi

def f_iv(qs, s_iv):
    """Interval enclosure of sum 2 arcsin(cos(pi/q_i)/s) - 2 pi."""
    tot = iv.mpf(0)
    for q in qs:
        t = rasin(cospi(q) / s_iv)
        if t is None:
            return None
        tot = tot + 2 * t
    return tot - 2 * PI

def classify_config(qs):
    """Return (status, data).  status in closable / not_closable /
    degenerate_candidate.  For closable: data = interval enclosing R_c^2.

    f(s) = sum 2 arcsin(c_i/s) is strictly decreasing on [c_max, 1];
    f(1) = sum pi(1 - 2/q_i) < 2 pi by the angle condition; so a root with
    every argument <= 1 exists iff f(c_max) >= 2 pi, it is unique, and the
    centre is strictly inside iff f(c_max) > 2 pi (every arc < pi).
    At s = c_max the terms with q_i = q_max equal pi exactly."""
    if len(qs) not in (3, 4, 5) or any((type(q) is not int or q < 3 for q in qs)):
        raise ValueError('pointed cycle requires 3..5 integer polygon entries >= 3')
    if not angle_ok(qs):
        raise ValueError('pointed cycle requires strict angle sum < 2 pi')
    qm = max(qs)
    nmax = qs.count(qm)
    others = [q for q in qs if q != qm]
    cm = cospi(qm)
    if nmax >= 2:
        D = None
        status = 'closable'
    else:
        D = iv.mpf(0)
        for q in others:
            t = rasin(cospi(q) / cm)
            D = D + 2 * t
        D = D - PI
        sg = sign(D)
        if sg < 0:
            return ('not_closable', {'D': D})
        if sg == 0:
            return ('degenerate_candidate', {'D': D})
        status = 'closable'
    a, b = (mp.cos(mp.pi / qm), mp.mpf(1))
    for _ in range(mp.prec + 10):
        m = (a + b) / 2
        if f_mp(qs, m) > 0:
            a = m
        else:
            b = m
    s0 = (a + b) / 2
    width = mp.mpf(2) ** (-(IV_PREC - 40))
    for _ in range(60):
        s_lo, s_hi = (s0 - width, s0 + width)
        if s_lo <= cm.b:
            s_lo = cm.b
        if s_hi >= 1:
            s_hi = (s0 + 1) / 2
        flo = f_iv(qs, pt(s_lo))
        fhi = f_iv(qs, pt(s_hi))
        if flo is not None and fhi is not None and (flo.a > 0) and (fhi.b < 0):
            break
        width *= 4
    else:
        raise ArithmeticError('type (i) bracket failed for %r' % (qs,))
    g_lo = ONE / (4 * (ONE - pt(s_lo) ** 2))
    g_hi = ONE / (4 * (ONE - pt(s_hi) ** 2))
    Rc2 = iv.mpf([g_lo.a, g_hi.b])
    return (status, {'Rc2': Rc2, 'D': D, 's': iv.mpf([s_lo, s_hi])})

class Q5:
    """Exact numbers x + y sqrt5, x, y rational."""

    def __init__(self, x, y=0):
        self.x, self.y = (Fraction(x), Fraction(y))

    def __add__(self, o):
        return Q5(self.x + o.x, self.y + o.y)

    def __mul__(self, o):
        return Q5(self.x * o.x + 5 * self.y * o.y, self.x * o.y + self.y * o.x)

    def __eq__(self, o):
        return self.x == o.x and self.y == o.y
COS2 = {3: Q5(Fraction(1, 4)), 4: Q5(Fraction(1, 2)), 6: Q5(Fraction(3, 4)), 5: Q5(Fraction(1, 4), Fraction(1, 4)) * Q5(Fraction(1, 4), Fraction(1, 4)), 10: Q5(Fraction(5, 8), Fraction(1, 8))}

def exact_degenerate(ms):
    """k = 3, q_max unique: f(c_max) = 2 pi iff arcsin x + arcsin y = pi/2
    with x = cos(pi/a)/cos(pi/c), y = cos(pi/b)/cos(pi/c) in (0, 1], iff
    x^2 + y^2 = 1, iff cos^2(pi/a) + cos^2(pi/b) = cos^2(pi/c) (a right
    triangle of chords inscribed with its hypotenuse a diameter)."""
    if len(ms) != 3 or ms.count(ms[2]) != 1 or any((q not in COS2 for q in ms)):
        return False
    a, b, c = ms
    for q in ms:
        e = COS2[q]
        val = iv.mpf(e.x.numerator) / e.x.denominator + iv.mpf(e.y.numerator) / e.y.denominator * iv.sqrt(iv.mpf(5))
        d = val - cospi(q) ** 2
        if not contains_zero(d):
            raise ArithmeticError('exact cos^2 table wrong at %d' % q)
    return COS2[a] + COS2[b] == COS2[c]

def cos_theta(q):
    """cos(pi(1 - 2/q)) = -cos(2 pi/q)."""
    if q == 3:
        return HALF
    if q == 4:
        return iv.mpf(0)
    return -iv.cos(2 * PI / q)

def padd(p, r):
    m = max(len(p), len(r))
    return [(p[i] if i < len(p) else 0) + (r[i] if i < len(r) else 0) for i in range(m)]

def pmul(p, r):
    out = [iv.mpf(0)] * (len(p) + len(r) - 1)
    for i, x in enumerate(p):
        for j, y in enumerate(r):
            out[i + j] = out[i + j] + x * y
    return out

def pscale(p, s):
    return [s * x for x in p]

def peval(p, x):
    acc = iv.mpf(0)
    for c in reversed(p):
        acc = acc * x + c
    return acc

def pder(p):
    return [i * p[i] for i in range(1, len(p))]

def type3_poly(q1, q2, h2):
    """Polynomial in c = cos(phi) whose roots in (-1, 1) are exactly the
    solutions of the squared closure h^2 (1 - T) = (1 - S)^2 (DERIVATION.md):
    P = h^2 N (1+c) - M^2 (1-c), N = 1 - c^2 - c1^2 - c2^2 + 2 c c1 c2,
    M = 1 + c - c1 - c2; for q1 = q2 the factor (1 - c) is removed."""
    c1, c2 = (cos_theta(q1), cos_theta(q2))
    one = iv.mpf(1)
    if q1 == q2:
        c0 = c1
        A = [one, one]
        B = [one - 2 * c0 * c0, one]
        M = [one - 2 * c0, one]
        return (padd(pscale(pmul(A, B), h2), pscale(pmul(M, M), -one)), c1, c2)
    N = [one - c1 * c1 - c2 * c2, 2 * c1 * c2, -one]
    M = [one - c1 - c2, one]
    P = padd(pscale(pmul(N, [one, one]), h2), pscale(pmul(pmul(M, M), [one, -one]), -one))
    return (P, c1, c2)

def isolate_roots(P, a, b, depth=0, maxdepth=90):
    """Rigorous root isolation of the polynomial P on the open interval
    (a, b), with P(a), P(b) != 0 checked by the caller.  Returns
    (roots, undecided): roots are disjoint intervals each containing exactly
    one root (P strictly monotone there, sign change at the ends)."""
    I = iv.mpf([a, b])
    if not contains_zero(peval(P, I)):
        return ([], [])
    dP = peval(pder(P), I)
    if not contains_zero(dP):
        sa, sb = (sign(peval(P, pt(a))), sign(peval(P, pt(b))))
        if sa != 0 and sb != 0:
            if sa == sb:
                return ([], [])
            lo_, hi_ = (a, b)
            for _ in range(IV_PREC):
                if hi_ - lo_ < mpmath.mpf(2) ** (-(IV_PREC - 30)):
                    break
                m = (lo_ + hi_) / 2
                sm = sign(peval(P, pt(m)))
                if sm == 0:
                    ml, mr = ((lo_ + m) / 2, (m + hi_) / 2)
                    sl = sign(peval(P, pt(ml)))
                    sr = sign(peval(P, pt(mr)))
                    if sl == sa and sr == -sa:
                        lo_, hi_ = (ml, mr)
                        continue
                    break
                if sm == sa:
                    lo_ = m
                else:
                    hi_ = m
            return ([iv.mpf([lo_, hi_])], [])
    if depth >= maxdepth:
        return ([], [I])
    m = (a + b) / 2
    if sign(peval(P, pt(m))) == 0:
        m = a + (b - a) * mpmath.mpf(0.4999)
        if sign(peval(P, pt(m))) == 0:
            return ([], [I])
    r1, u1 = isolate_roots(P, a, m, depth + 1, maxdepth)
    r2_, u2 = isolate_roots(P, m, b, depth + 1, maxdepth)
    return (r1 + r2_, u1 + u2)

def type3_roots(n, q1, q2):
    """Exhaust (-1,1), including negative and non-geometric roots.

    No sign/geometry prefilter is permitted before the Omega comparison.
    A failed subdivision returns undecided boxes, never an empty proof.
    """
    h2 = hA2(n)
    P, c1, c2 = type3_poly(q1, q2, h2)
    a, b = (mpmath.mpf(-1), mpmath.mpf(1))
    if sign(peval(P, pt(a))) == 0 or sign(peval(P, pt(b))) == 0:
        raise ArithmeticError('type (iii) endpoint value not decided')
    roots, und = isolate_roots(P, a, b)
    out = []
    for c in roots:
        if not -1 < c.a <= c.b < 1:
            raise ArithmeticError('type (iii) root not strictly inside (-1,1)')
        S = (c1 + c2) / (ONE + c)
        br = sign(ONE - S)
        R2 = r2(n) + h2 / 4 + ONE / (2 * (ONE + c))
        T = (c1 * c1 + c2 * c2 - 2 * c * c1 * c2) / (ONE - c * c) if q1 != q2 else 2 * c1 * c1 / (ONE + c)
        out.append({'c': c, 'branch': br, 'R2': R2, 'T': T})
    return (out, und)

def root_category(root):
    if root['branch'] == 0:
        raise ArithmeticError('type (iii) undecided geometric branch')
    return 'geo' if root['branch'] < 0 else 'nongeo'

def fmt(x, d=12):
    return mpmath.nstr(mp.mpf(x), d)

def run(omega_path, corrupt=None, nmin=NMIN, quiet=False, control=False):
    """control: n = 3..16 and entries <= 16 only (every such cycle is a
    stage-1 cycle, so its root should be IN Omega: a positive test)."""
    t0 = time.process_time()
    data = json.load(open(omega_path))
    intervals = [list(t) for t in data['intervals']]
    log = []

    def say(*a):
        s = ' '.join((str(x) for x in a))
        log.append(s)
        if not quiet:
            print(s, flush=True)
    rn2 = r2
    if corrupt == 'rn-2pi':

        def rn2(n):
            s = iv.sin(2 * PI / n)
            return ONE / (4 * s * s)
    om = Omega(intervals)
    maxO = om.max
    say('Omega: %d intervals, min %s, max %s' % (len(intervals), fmt(om.min), fmt(maxO)))
    rq = iv.sqrt(r2(QMAX + 1))
    if not rq.a > maxO:
        raise AssertionError('QMAX too small')
    say('bound: r_%d >= %s > max Omega, so n, q <= %d' % (QMAX + 1, fmt(rq.a), QMAX))
    nmax = QMAX
    qcap = QMAX
    if control:
        nmin, nmax, qcap = (3, 16, 16)
    ns = list(range(nmin, nmax + 1))
    coinc = []
    counts = {}
    gap = [None, None]
    ctl_bad = []
    categories = {name: dict(total=0, hits=0, negative=0) for name in ('geo', 'nongeo')}
    root_audit = []
    undecided = 0

    def check(typ, n, conf, R2, extra_info=''):
        R = iv.sqrt(R2)
        h = om.hits(R)
        if not h and R.a <= om.max:
            g = om.gap(R)
            if gap[0] is None or g < gap[0]:
                gap[0], gap[1] = (g, (typ, n, conf, fmt(R.a, 25)))
        counts[typ] = counts.get(typ, 0) + 1
        if h:
            coinc.append((typ, n, conf, R, h))
        if control:
            if not h:
                if not (typ == 'iii' and conf[2] == 'nongeo'):
                    ctl_bad.append((typ, n, conf))
                say('control MISS type %s n=%d conf=%s R=%s' % (typ, n, conf, fmt(R.a, 20)))
        elif h:
            say('COINCIDENCE type %s n=%d conf=%s R in [%s, %s] meets %s %s' % (typ, n, conf, fmt(R.a, 30), fmt(R.b, 30), [(fmt(x[0], 25), fmt(x[1], 25), x[2]) for x in h], extra_info))
        return R
    ms_all = enumerate_multisets(QMAX)
    stat = {'closable': [], 'not_closable': [], 'degenerate_candidate': []}
    Rc2 = {}
    for ms in ms_all:
        st, d = classify_config(ms)
        stat[st].append(ms)
        if st == 'closable':
            Rc2[ms] = d['Rc2']
    nb = {k: sum((bracelets(m)[0] for m in v)) for k, v in stat.items()}
    nr = {k: sum((bracelets(m)[1] for m in v)) for k, v in stat.items()}
    say('type (i): %d multisets with entries 3..%d and angle sum < 2 pi (%d cyclic configurations up to rotation+reflection, %d up to rotation)' % (len(ms_all), QMAX, sum(nb.values()), sum(nr.values())))
    for k in stat:
        say('  %s: %d multisets (%d bracelets, %d necklaces)' % (k, len(stat[k]), nb[k], nr[k]))
    say('  degenerate candidates:', stat['degenerate_candidate'])
    for ms in stat['degenerate_candidate']:
        if not exact_degenerate(ms):
            coinc.append(('i-undecided', None, ms, None, []))
            say('UNDECIDED type (i) closure of %s' % (ms,))
    say('  exact identities cos^2(pi/a) + cos^2(pi/b) = cos^2(pi/c) verified in Q(sqrt5) for all degenerate candidates')
    nc = {}
    for ms in stat['not_closable']:
        nc.setdefault((len(ms), ms[:-1]), []).append(ms[-1])
    say('  not closable, grouped by all-but-largest entries (largest-entry range):', '; '.join(('%s+(%d..%d)%s' % (p[1], min(v), max(v), '' if len(v) == max(v) - min(v) + 1 else ' [gaps]') for p, v in sorted(nc.items()))))
    relevant = [m for m in stat['closable'] if iv.sqrt(Rc2[m]).a <= maxO and max(m) <= qcap]
    say('  closable with R_c <= max Omega: %d multisets (%d bracelets)' % (len(relevant), sum((bracelets(m)[0] for m in relevant))))
    if corrupt == 'insert':
        targets = corrupt_insert_targets(Rc2)
        for a, b, tag in targets:
            intervals.append([a, b, tag])
        om = Omega(intervals)
        say('CORRUPTION insert: added', [t[2] for t in targets])
    t_i = 0
    for ms in relevant:
        for n in ns:
            check('i', n, ms, rn2(n) + Rc2[ms])
            t_i += 1
    for n in ns:
        RA2 = rn2(n) + hA2(n) / 4
        for q in range(3, qcap + 1):
            check('ii', n, (q,), RA2 + r2(q))
    t3 = {}
    for q1, q2 in [(3, 3), (3, 4), (3, 5)]:
        nroots, nbr = (set(), {})
        phis = []
        for n in ns:
            roots, und = type3_roots(n, q1, q2)
            if und:
                undecided += len(und)
                say('UNDECIDED type (iii) root isolation n=%d %s' % (n, (q1, q2)))
                coinc.append(('iii-undecided', n, (q1, q2), None, und))
                if control:
                    ctl_bad.append(('iii-undecided', n, (q1, q2)))
            nroots.add(len(roots))
            for r in roots:
                category = root_category(r)
                nbr[r['branch']] = nbr.get(r['branch'], 0) + 1
                R2 = r['R2']
                if corrupt == 'rn-2pi':
                    R2 = R2 - r2(n) + rn2(n)
                before = len(coinc)
                check('iii', n, (q1, q2, category), R2, 'branch %d phi %s deg' % (r['branch'], fmt(mp.degrees(mp.acos(mp.mpf(r['c'].a))), 15)))
                hit = len(coinc) > before
                categories[category]['total'] += 1
                categories[category]['hits'] += int(hit)
                categories[category]['negative'] += int(r['c'].b < 0)
                root_audit.append(dict(n=n, qs=[q1, q2], category=category, c=[fmt(r['c'].a, 75), fmt(r['c'].b, 75)], c_dyadic=[[s, str(m), e, bc] for s, m, e, bc in r['c']._mpi_], hit=hit))
                if n in (17, 397):
                    phis.append((n, r['branch'], fmt(mp.degrees(mp.acos(mp.mpf(r['c'].a))), 15), fmt(iv.sqrt(R2).a, 15)))
        t3[q1, q2] = (sorted(nroots), nbr, phis)
        say('type (iii) %s: roots per n %s; branch counts (gamma sign) %s; samples (n, branch, phi deg, R) %s' % ((q1, q2), sorted(nroots), nbr, phis))
    cpu = time.process_time() - t0
    say('counts (n, configuration) pairs:', counts)
    say('n range %d..%d' % (ns[0], ns[-1]))
    say('type (iii) audit: domain (-1,1); all isolated roots checked;', 'undecided boxes %d;' % undecided, 'categories', categories)
    if gap[0] is not None:
        say('closest approach (relative gap to an Omega endpoint): %s at %s' % (mpmath.nstr(gap[0], 6), gap[1]))
    if control:
        hit = {}
        for t in coinc:
            hit[t[0]] = hit.get(t[0], 0) + 1
        say('control: cycles whose radius IS in Omega, per type:', hit, 'of', counts)
        say('control: type (iii) geometric %d/%d; non-geometric %d/%d; total %d/%d' % (categories['geo']['hits'], categories['geo']['total'], categories['nongeo']['hits'], categories['nongeo']['total'], sum((c['hits'] for c in categories.values())), counts['iii']))
        if categories['geo']['total'] != 42 or categories['geo']['hits'] != 42 or categories['nongeo']['total'] != 28 or (categories['nongeo']['hits'] != 2):
            ctl_bad.append(('iii-category-regression', categories))
        say('control: misses other than non-geometric type (iii) roots: %d' % len(ctl_bad))
    else:
        say('COINCIDENCES: %d' % len(coinc))
    say('CPU seconds: %.1f' % cpu)
    return {'ctl_bad': ctl_bad, 'coinc': coinc, 'counts': counts, 'stat': stat, 'relevant': relevant, 'Rc2': Rc2, 't3': t3, 'cpu': cpu, 'log': log, 'root_audit': root_audit, 'categories': categories, 'undecided': undecided}

def corrupt_insert_targets(Rc2):
    """Three Omega intervals of half-width 1e-30 around radii of this
    checker: type (i) n=17 (4,4,5), type (ii) n=23 q=7, type (iii) n=101
    (3,4) (its geometric root)."""
    out = []
    w = mpmath.mpf('1e-30')

    def around(R2, tag):
        R = iv.sqrt(R2)
        m = mp.mpf(R.a)
        out.append([mpmath.nstr(m - w, 50), mpmath.nstr(m + w, 50), tag])
    around(r2(17) + Rc2[4, 4, 5], 'inserted-i-17-(4,4,5)')
    around(r2(23) + hA2(23) / 4 + r2(7), 'inserted-ii-23-7')
    roots, _ = type3_roots(101, 3, 4)
    geo = [r for r in roots if r['branch'] < 0]
    around(geo[0]['R2'], 'inserted-iii-101-(3,4)')
    return out
if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('omega')
    ap.add_argument('--corrupt', choices=['insert', 'rn-2pi'])
    ap.add_argument('--nmin', type=int, default=NMIN)
    ap.add_argument('--control', action='store_true')
    ap.add_argument('--out')
    ap.add_argument('--audit', help='JSON audit of every type-(iii) root checked')
    args = ap.parse_args()
    print('python', sys.version.split()[0], 'mpmath', mpmath.__version__, 'backend', mpmath.libmp.BACKEND, 'iv.prec', iv.prec)
    res = run(args.omega, corrupt=args.corrupt, nmin=args.nmin, control=args.control)
    if args.audit:
        with open(args.audit, 'w') as f:
            json.dump(dict(domain=[-1, 1], domain_open=True, categories=res['categories'], undecided=res['undecided'], roots=res['root_audit']), f, indent=2)
            f.write('\n')
    if args.out:
        with open(args.out, 'w') as f:
            f.write('\n'.join(res['log']) + '\n')
    if args.control:
        sys.exit(0 if not res['ctl_bad'] else 4)
    sys.exit(0 if not res['coinc'] else 3)
