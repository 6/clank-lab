"""Partner-radius filter for a paired type-(i) fan (m, c1) around the n-gon F.

From F:  R^2 = r_n^2 + R_{(m,c1)}^2 = r_n^2 + r_m^2 + delta_{c1}(m).
From the partner m-gon F2 (its cycle contains {n}x{m}; type (iii) would need
a duoprism parameter <= 5): type (i) with configuration (n, c2) gives
R^2 = r_m^2 + r_n^2 + delta_{c2}(n); type (ii) (q = n) gives
R^2 = R_{A_m}^2 + r_n^2 = r_m^2 + h_{A_m}^2/4 + r_n^2.
So delta_{c1}(m) must equal h_{A_m}^2/4 or delta_{c2}(n) for an admissible
(c2, n).  Returns the list of admissible (c2, n) with a possible equality
(interval overlap); everything else is excluded by certified disjointness.
"""
from mpmath import iv

import p1check
from p1check import PI, sign_of, delta_general, delta_closed, lo, hi

NMIN = 17


def allowed(m, c1):
    d1, s = delta_general(tuple(c1), m)
    if not (s == 1):
        raise AssertionError()
    out = []
    # partner of type (ii)
    hA = (1 - 1 / (2 * (1 + iv.cos(PI / m)))) / 4
    if sign_of(d1 - hA) == 0:
        out.append(("(ii)", "all n"))
    cands = p1check.cpp_candidates()
    for c2, nmax in cands.items():
        if nmax is None:
            # unbounded c'' : closed forms; non-closable ones carry no fan
            if c2 not in ((4, 4), (3, 6), (3, 3, 3)):
                for n in range(NMIN, 60):
                    if not (delta_general(c2, n)[1] == -1):
                        raise AssertionError()
                continue
            rng = delta_closed(c2, iv.mpf([lo(iv.cos(PI / NMIN)), 1]))
            if sign_of(d1 - rng) == 0:
                for n in range(NMIN, 2000):
                    if sign_of(d1 - delta_closed(c2, iv.cos(PI / n))) == 0:
                        out.append((c2, n))
                if sign_of(d1 - delta_closed(c2, iv.mpf([lo(iv.cos(PI / 2000)), 1]))) == 0:
                    out.append((c2, ">=2000"))
        else:
            for n in range(NMIN, nmax + 1):
                d2, s2 = delta_general(c2, n)
                if d2 is not None and sign_of(d1 - d2) == 0:
                    out.append((c2, n))
    return float(p1check.mpf(d1.a)), out
