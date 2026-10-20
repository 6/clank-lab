"""Independent checker for Case B step (P1), the family-polygon filter.

Written from CASEB.md ("Setting and notation", "s >= 2", "(P1)") only.
Interval arithmetic: mpmath.iv at 200 bits (no python-flint).  Exact
degeneracy / identity claims are confirmed with sympy (algebraic numbers).

Definitions used (all re-derived here):
  * a type-(i) configuration around a large n-gon F is a cyclic sequence
    c = (q_1..q_k), k >= 3, of polygon sizes; its rays x_i are unit vectors in
    L-perp (R^3) with |x_i - x_{i+1}| = l_i = 2cos(pi/q_i); the angle sum
    condition is sum(1 - 2/q_i) < 2.
  * the x_i lie on a circle of Euclidean radius S (angular radius rho,
    S = sin rho); closable = the circle centre lies strictly inside the
    inscribed polygon, i.e. all central angles 2 asin(l_i/(2S)) < pi with sum
    2 pi.  With l_max the largest chord this holds iff
        g := sum_{i != argmax} 2 asin(l_i / l_max) > pi
    (at S = l_max/2 the largest arc is pi; the sum of arcs decreases in S and
    is sum pi(1-2/q_i) < 2 pi at S = 1).  g = pi: degenerate.
  * centre: x_i . gamma = 1/2 with gamma on the circle axis, so
    R_c^2 = |gamma|^2 = 1/(4 cos^2 rho) = 1/(4(1 - S^2)).
  * family polygon: an entry q in {7, 9, 11..16}.  The cycle around Q is of
    type (ii)_q (then R_c^2 = R_{A_q}^2) or (i)_q with configuration (n, c'')
    (then R_c^2 - r_q^2 = delta_{c''}(n) := R_{(n,c'')}^2 - r_n^2), n >= 17.
"""
import functools
import itertools
import os
import sys
from fractions import Fraction

import sympy
from mpmath import iv, mp, mpf

iv.prec = 200
mp.prec = 200
PI = iv.pi
FAMILY = (7, 9, 11, 12, 13, 14, 15, 16)
QMAX = 16
NMIN = 17
# deliberate corruption hooks (run.sh): P1_CORRUPT=delta44 shifts the (4,4)
# value of delta by 1e-30; P1_CORRUPT=antiprism uses h^2/2 instead of h^2/4
# in R_{A_q}^2.
CORRUPT = os.environ.get("P1_CORRUPT", "")


def lo(x):
    return mpf(x.a)


def hi(x):
    return mpf(x.b)


def sign_of(x):
    """+1 / -1 if the interval excludes 0, else 0 (undecided)."""
    if lo(x) > 0:
        return 1
    if hi(x) < 0:
        return -1
    return 0


def asin(x):
    return iv.atan2(x, iv.sqrt(1 - x * x))


def chord(q):
    """2 cos(pi/q); q may be an iv interval of 1/q via chord_inv."""
    return 2 * iv.cos(PI / q)


def r_poly(q):
    """circumradius of the unit-edge regular q-gon."""
    return 1 / (2 * iv.sin(PI / q))


def R2_antiprism(q):
    """squared circumradius of the unit-edge antiprism A_q: r_q^2 + h_q^2/4,
    h_q^2 = 1 - 1/(4 cos^2(pi/(2q)))."""
    h2 = 1 - 1 / (4 * iv.cos(PI / (2 * q)) ** 2)
    if CORRUPT == "antiprism":
        return r_poly(q) ** 2 + h2 / 2
    return r_poly(q) ** 2 + h2 / 4


# --------------------------------------------------------------------------
# enumeration
def canonical(seq):
    k = len(seq)
    rots = [tuple(seq[i:] + seq[:i]) for i in range(k)]
    rev = list(reversed(seq))
    rots += [tuple(rev[i:] + rev[:i]) for i in range(k)]
    return min(rots)


def angle_ok(seq, extra=Fraction(0)):
    return extra + sum(1 - Fraction(2, q) for q in seq) < 2


def enumerate_configs():
    out = set()
    for k in range(3, 6):   # each term 1 - 2/q >= 1/3, so k <= 5
        for seq in itertools.product(range(3, QMAX + 1), repeat=k):
            if angle_ok(seq):
                out.add(canonical(list(seq)))
    return sorted(out, key=lambda c: (len(c), c))


# --------------------------------------------------------------------------
# closability and config radius for chords given as intervals
def closability(chords):
    """returns (+1 closable, -1 not, 0 undecided) and g - pi."""
    if len(chords) < 3:
        raise ValueError("a full-dimensional pointed 3-cone needs at least three rays")
    lm_i = max(range(len(chords)), key=lambda i: float(mpf(chords[i].a)))
    lm = chords[lm_i]
    # if another chord can equal l_max, the arcs at S = l_max/2 already sum
    # to >= 2 pi: closable (k >= 3 and all chords >= 1 > 0)
    g = iv.mpf(0)
    for i, l in enumerate(chords):
        if i == lm_i:
            continue
        ratio = l / lm
        if hi(ratio) >= 1:   # tie (or undecidable order): treat as tie
            ratio = iv.mpf([lo(ratio), 1])
        g += 2 * asin(ratio)
    d = g - PI
    s = sign_of(d)
    return s, d


def arc_sum(chords, S):
    return sum(2 * asin(l / (2 * S)) for l in chords)


def config_S(chords, iters=400):
    """enclosure of S in (l_max/2, 1) with arc_sum(S) = 2 pi (closable case).
    arc_sum is strictly decreasing in S; bisection on point values gives a
    bracket [Sa, Sb] with arc_sum(Sa) > 2pi > arc_sum(Sb) certified."""
    if len(chords) < 3:
        raise ValueError("a full-dimensional pointed 3-cone needs at least three rays")
    lm = max(hi(l) for l in chords)
    a = lm / 2
    b = mpf(1)
    # sanity: arcs at b sum to < 2 pi; at a (>= l_max/2) to > 2pi
    target = 2 * PI
    if not (sign_of(arc_sum(chords, iv.mpf(b)) - target) == -1):
        raise AssertionError()
    a = a * (1 + mpf(2) ** -150)  # stay inside the domain of asin
    if not (sign_of(arc_sum(chords, iv.mpf(a)) - target) == 1):
        raise AssertionError()
    for _ in range(iters):
        mid = (a + b) / 2
        v = sign_of(arc_sum(chords, iv.mpf(mid)) - target)
        if v == 1:
            a = mid
        elif v == -1:
            b = mid
        else:
            break
        if b - a < mpf(2) ** -130:
            break
    return iv.mpf([a, b])


def config_R2(chords):
    S = config_S(chords)
    return 1 / (4 * (1 - S * S))


def triangle_R2(l1, l2, l3):
    """k = 3 closed form: S = circumradius of the chord triangle."""
    s2 = (l1 * l1 + l2 * l2 + l3 * l3) ** 2 - 2 * (l1 ** 4 + l2 ** 4 + l3 ** 4)
    S2 = (l1 * l2 * l3) ** 2 / s2   # (abc)^2 / (16 K^2), 16K^2 = s2
    return 1 / (4 * (1 - S2))


# --------------------------------------------------------------------------
# c'' list (configurations (n, c'') around a family polygon Q), recomputed
def cpp_candidates():
    """linear sequences c'' (entries 3..16, up to reversal) such that (n, c'')
    satisfies the angle condition for some n >= 17; for each, the largest such
    n (None = all n)."""
    res = {}
    for k in range(2, 5):
        for seq in itertools.product(range(3, QMAX + 1), repeat=k):
            key = min(seq, tuple(reversed(seq)))
            if key in res:
                continue
            base = sum(1 - Fraction(2, q) for q in seq)
            # (1 - 2/n) + base < 2  <=>  2/n > base - 1
            if base - 1 < 0:
                res[key] = None          # all n
            elif base - 1 == 0:
                res[key] = None          # all finite n (2/n > 0)
            else:
                nmax = 0
                n = NMIN
                while Fraction(2, n) > base - 1:
                    nmax = n
                    n += 1
                if nmax >= NMIN:
                    res[key] = nmax
    return res


def delta_closed(cpp, cosn):
    """closed forms of delta_{c''}(n) for the three unbounded c'' (derived in
    README): cosn = cos(pi/n) (interval, may contain 1 = n infinite)."""
    if cpp == (4, 4):
        d = iv.mpf(1) / 4
        if CORRUPT == "delta44":
            d = d + mpf(10) ** -30
        return d
    if cpp == (3, 6):
        # cos^2/(4cos^2 - 1) written with one occurrence of cos (tight)
        return 1 / (4 - 1 / (cosn * cosn))
    if cpp == (3, 3, 3):
        # h_{A_n}^2/4, h^2 = 1 - 1/(4cos^2(pi/2n)) = 1 - 1/(2(1+cos(pi/n)))
        return (1 - 1 / (2 * (1 + cosn))) / 4
    raise KeyError(cpp)


@functools.lru_cache(maxsize=None)
def delta_general(cpp, n):
    chords = [chord(n)] + [chord(p) for p in cpp]
    s, _ = closability(chords)
    if s != 1:
        return None, s
    return config_R2(chords) - r_poly(n) ** 2, s


# --------------------------------------------------------------------------
def exact_zero(expr):
    x = sympy.Symbol("x")
    return sympy.minimal_polynomial(expr, x) == x


def sym_chord(q):
    return 2 * sympy.cos(sympy.pi / q)


def main():
    configs = enumerate_configs()
    print(f"cyclic configurations (entries 3..{QMAX}, angle sum < 2pi): {len(configs)}")
    # ---- c'' list
    cands = cpp_candidates()
    cpp_info = {}
    for cpp, nmax in sorted(cands.items(), key=lambda t: (len(t[0]), t[0])):
        ns = range(NMIN, (nmax if nmax else 60) + 1)
        stat = []
        for n in ns:
            _, s = delta_general(cpp, n)
            stat.append(s)
        if all(s == -1 for s in stat):
            kind = "not closable"
        elif all(s == 1 for s in stat):
            kind = "closable"
        else:
            kind = "mixed " + str(stat)
        cpp_info[cpp] = (nmax, kind)
    usable = {c: v for c, v in cpp_info.items() if v[1] != "not closable"}
    print("NON-PROOF CHECK: sampled tail and closed-form agreement; the written reductions and whole-interval bounds justify the tail.")
    print("c'' with (n,c'') angle-admissible for some n >= 17:")
    for c, (nmax, kind) in sorted(cpp_info.items(), key=lambda t: (len(t[0]), t[0])):
        rng = "all n >= 17" if nmax is None else f"17 <= n <= {nmax}"
        print(f"  {c}: {rng}; {kind} (tested n = 17..{nmax or 60})")
    # unbounded ones must be exactly the closed-form ones; check closed forms
    # against the general solver
    for c, (nmax, kind) in usable.items():
        if nmax is None:
            if not (c in ((4, 4), (3, 6), (3, 3, 3))):
                raise AssertionError(c)
            for n in list(range(NMIN, 80)) + [100, 1000, 10 ** 5]:
                dg, _ = delta_general(c, n)
                dc = delta_closed(c, iv.cos(PI / n))
                if CORRUPT != "delta44":
                    if not (sign_of(dg - dc) == 0 and hi(abs(dg - dc)) < mpf(10) ** -15):
                        raise AssertionError((c, n, dg, dc))
    # tail enclosures over all n >= 17 incl. infinity (monotone closed forms,
    # evaluated over the whole interval cos(pi/n) in [cos(pi/17), 1])
    cos_all = iv.mpf([lo(iv.cos(PI / NMIN)), 1])
    dranges = {c: delta_closed(c, cos_all) for c in usable if usable[c][0] is None}
    for c, d in dranges.items():
        print(f"  delta_{c}(n), n >= 17 incl. infinity, enclosed in [{float(lo(d)):.6f}, {float(hi(d)):.6f}]")

    # ---- classification
    counts = {"closable": 0, "not closable": 0, "degenerate": 0}
    fam_total = 0
    excluded = []
    survivors = []
    rows = []
    for c in configs:
        chords = [chord(q) for q in c]
        s, d = closability(chords)
        if s == 0:
            # exact check (sympy): g = pi exactly; only k = 3 expected
            if not (len(c) == 3):
                raise AssertionError(c)
            ls = sorted([sym_chord(q) for q in c], key=lambda e: float(e))
            if not (exact_zero(sympy.expand(ls[0] ** 2 + ls[1] ** 2 - ls[2] ** 2))):
                raise AssertionError(c)
            counts["degenerate"] += 1
            fam = [q for q in c if q in FAMILY]
            rows.append((c, "degenerate", "family polygon" if fam else "-"))
            continue
        if s == -1:
            counts["not closable"] += 1
            rows.append((c, "not closable", ""))
            continue
        counts["closable"] += 1
        R2 = config_R2(chords)
        if len(c) == 3:
            R2t = triangle_R2(*chords)
            if not (hi(abs(R2 - R2t)) < mpf(10) ** -30):
                raise AssertionError((c, R2, R2t))
        fam = sorted(set(q for q in c if q in FAMILY))
        if not fam:
            rows.append((c, "closable", "no family polygon"))
            continue
        fam_total += 1
        verdicts = []
        for q in fam:
            matches = []
            # (ii)_q
            if sign_of(R2 - R2_antiprism(q)) == 0:
                matches.append("(ii)_q")
            X = R2 - r_poly(q) ** 2
            for cpp, (nmax, kind) in usable.items():
                if nmax is None:
                    if sign_of(X - dranges[cpp]) == 0:
                        # inside the range: locate n (finite n by search,
                        # n >= 2000 incl. infinity by one enclosure)
                        hit = [n for n in range(NMIN, 2000)
                               if sign_of(X - delta_closed(cpp, iv.cos(PI / n))) == 0]
                        tail = delta_closed(cpp, iv.mpf([lo(iv.cos(PI / 2000)), 1]))
                        if sign_of(X - tail) == 0:
                            hit.append(">=2000")
                        if hit:
                            if len(hit) > 3:
                                matches.append(f"{cpp} n={hit[0]}..{hit[-2]},{hit[-1]}")
                            else:
                                matches.append(f"{cpp} n=" + ",".join(map(str, hit)))
                else:
                    for n in range(NMIN, nmax + 1):
                        dn, sc = delta_general(cpp, n)
                        if dn is not None and sign_of(X - dn) == 0:
                            matches.append(f"{cpp} n={n}")
            verdicts.append((q, matches))
        ok = all(m for _, m in verdicts)
        desc = "; ".join(f"Q={q}: " + (",".join(m) if m else "no match") for q, m in verdicts)
        if ok:
            survivors.append(c)
            rows.append((c, "closable", "SURVIVES " + desc))
        else:
            excluded.append(c)
            rows.append((c, "closable", "EXCLUDED " + desc))
    for c, k, d in rows:
        print(f"  {c}: {k} {d}")
    # survivors must be identities: (4,4,q) = vertex of the prism P_q
    # (delta_(4,4) = 1/4 exactly) and (3,3,3,q) = vertex of the antiprism A_q
    # (R_c = R_{A_q}); confirm exactly with sympy for (4,4,q)
    for c in survivors:
        q = [x for x in c if x in FAMILY]
        if not (len(q) == 1):
            raise AssertionError()
        q = q[0]
        if sorted(c) == sorted((4, 4, q)):
            l = sym_chord(q)
            S2 = (2 * 2 * l ** 2) / ((2 + 2 + l ** 2) ** 2 - 2 * (4 + 4 + l ** 4))
            R2s = 1 / (4 * (1 - S2))
            rq2 = 1 / (4 * sympy.sin(sympy.pi / q) ** 2)
            if not (exact_zero(sympy.nsimplify(0) + sympy.simplify(R2s - rq2 - sympy.Rational(1, 4)))):
                raise AssertionError(c)
        elif sorted(c) == sorted((3, 3, 3, q)):
            pass  # identity: the antiprism vertex realises (q,3,3,3) closably
        else:
            raise AssertionError(f"sporadic survivor {c}")
    print(f"closable {counts['closable']}, not closable {counts['not closable']}, "
          f"degenerate {counts['degenerate']}")
    print(f"closable with a family polygon: {fam_total}; excluded {len(excluded)}; "
          f"survive {len(survivors)}: {survivors}")
    with open(os.environ.get("P1_OUT", "p1_closable.txt"), "w") as f:
        for c, k, d in rows:
            if k == "closable" and not d.startswith("EXCLUDED"):
                f.write(",".join(map(str, c)) + "\n")
    with open(os.environ.get("P1_OUT_EXCL", "p1_excluded.txt"), "w") as f:
        for c in excluded:
            f.write(",".join(map(str, c)) + "\n")
    print("RESULT P1 total=%d closable=%d notclosable=%d degenerate=%d family=%d excluded=%d survivors=%s" % (
        len(configs), counts["closable"], counts["not closable"], counts["degenerate"],
        fam_total, len(excluded), ";".join("(" + ",".join(map(str, c)) + ")" for c in survivors)))


if __name__ == "__main__":
    main()
