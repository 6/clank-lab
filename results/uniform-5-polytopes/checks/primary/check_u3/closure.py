"""Step 2: the radius of a realisation is a single exact value.

For one polygon (VF-edge) of the realisation take the closure function of
CHECKER_SPEC_U1.md as a function of R:
    f(R) = sum_i theta_i(R) - 2 pi,
    cos theta_i = (x cos a_i - q_a q_b) / sqrt((x - q_a^2)(x - q_b^2)),
    x = R^2 - rho^2,  q_C = sqrt(R_C^2 - rho^2),
(the U1 formula with cos d = q / sqrt(x) substituted).  If f(R_lo) and
f(R_hi) have certified opposite signs and f' (forward-mode derivative,
evaluated on the whole interval) excludes 0, f has exactly one root in
[R_lo, R_hi]; every realisation using this polygon word closes there.
"""
from mpmath import iv
from ivla import ZERO, ONE, iacos, norm2
from search import polygon_word


def polygon_data(s, key):
    """[(alpha_i, RC2_prev, RC2_next)] around the polygon, in cyclic order."""
    a, b = tuple(key)
    inc = {}
    for fi, F in enumerate(s.facets):
        inv = {v: j for j, v in F.m.items()}
        if a in inv and b in inv:
            tk = frozenset((inv[a], inv[b]))
            if tk in F.T.polys:
                pd = F.T.polys[tk]
                cl = pd['cells']
                inc[fi] = (pd, [(frozenset(F.m[t] for t in F.T.cells[c]['poly']), c) for c in cl])
    # walk the cycle
    start = min(inc)
    seq = []
    f = start
    prev = None
    while True:
        pd, cl = inc[f]
        if prev is None:
            (k_in, c_in), (k_out, c_out) = cl[1], cl[0]
        else:
            (k_in, c_in), (k_out, c_out) = (cl[0], cl[1]) if cl[0][0] == prev else (cl[1], cl[0])
        T = s.facets[f].T
        seq.append((pd['alpha'], T.cells[c_in]['RC2'], T.cells[c_out]['RC2'], pd['p']))
        nxt = [g for g, _ in s.cells[k_out] if g != f][0]
        prev = k_out
        f = nxt
        if f == start:
            break
    return seq


def f_and_df(seq, R):
    p = seq[0][3]
    rho = 1 / (2 * iv.sin(iv.pi / p))
    x = R * R - rho * rho
    tot = ZERO
    dtot = ZERO
    for alpha, RCa, RCb, _ in seq:
        A = RCa - rho * rho
        B = RCb - rho * rho
        qa, qb = iv.sqrt(A), iv.sqrt(B)
        ca = iv.cos(alpha)
        D = (x - A) * (x - B)
        sD = iv.sqrt(D)
        num = x * ca - qa * qb
        h = num / sD
        tot += iacos(h)
        dD = 2 * x - A - B
        dh = (ca * sD - num * dD / (2 * sD)) / D
        dtot += -dh / iv.sqrt(1 - h * h)
    return tot - 2 * iv.pi, dtot * 2 * R


def certify(s, Rint):
    """returns (ok, info): ok if some polygon gives a unique certified root."""
    lo = iv.mpf(Rint.a)
    hi = iv.mpf(Rint.b)
    tried = 0
    for key in sorted(s.polys, key=lambda k: sorted(k)):
        tried += 1
        try:
            seq = polygon_data(s, key)
            flo, _ = f_and_df(seq, lo)
            fhi, _ = f_and_df(seq, hi)
            _, d = f_and_df(seq, Rint)
        except (ValueError, ZeroDivisionError):
            continue
        if ((flo.a > 0 and fhi.b < 0) or (flo.b < 0 and fhi.a > 0)) and (d.a > 0 or d.b < 0):
            from mpmath import mp
            return True, {'polygon_k': len(seq), 'p': seq[0][3],
                          'f_lo': mp.nstr(flo.mid, 6), 'f_hi': mp.nstr(fhi.mid, 6),
                          'df': [mp.nstr(d.a, 8), mp.nstr(d.b, 8)], 'tried': tried}
        if tried >= 6:
            break
    return False, {'tried': tried}
