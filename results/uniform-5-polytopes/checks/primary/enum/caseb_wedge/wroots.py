"""Type (iii): certified enclosure of ALL roots phi in (0, pi) of

    g(theta, phi) = w3 h_A/2 + w4/(2 cos(phi/2)) - 1/2,
    w4 = (C1 + C2)/(2 cos(phi/2)), w5 = (C1 - C2)/(2 sin(phi/2)),
    w3 = -sqrt(1 - w4^2 - w5^2),  C_j = cos(omega_j) = -cos(2 pi/q_j),

for every theta in [0, pi/17] (phi only where w4^2 + w5^2 <= 1).

Method: for each theta-box, bisect phi in [0, pi]; a phi-box is discarded if
w4^2 + w5^2 > 1 on it (monotone lower bounds, no division by intervals
containing 0) or if g certainly != 0 on theta-box x phi-box.  The surviving
boxes are merged into clusters; on each cluster's hull dg/dphi is certified
!= 0 (at most one root per theta) and g has certified opposite signs at the
hull's ends for all theta in the box (at least one root).  Then each theta
has exactly one root per cluster.
"""
from flint import arb

from wgeom import float_upper, float_lower, PI, ZERO, HALF, iv, sqrt_nn, antiprism_data, Undecided, OutOfDomain


def consts(q1, q2):
    return -(2 * PI / q1).cos(), -(2 * PI / q2).cos()


def wparts(C1, C2, equal, phi):
    c, s = (phi / 2).cos(), (phi / 2).sin()
    A, B = C1 + C2, C1 - C2
    w4 = A / (2 * c)
    w5 = ZERO if equal else B / (2 * s)
    rad = 1 - w4 * w4 - w5 * w5
    return c, s, A, B, w4, w5, rad


def g_val(C1, C2, equal, hA, phi):
    c, s, A, B, w4, w5, rad = wparts(C1, C2, equal, phi)
    w3 = -sqrt_nn(rad)
    return w3 * hA / 2 + w4 / (2 * c) - HALF


def g_der(C1, C2, equal, hA, phi):
    """dg/dphi; valid where rad > 0."""
    c, s, A, B, w4, w5, rad = wparts(C1, C2, equal, phi)
    dw4 = A * s / (4 * c * c)
    dw5 = ZERO if equal else -B * c / (4 * s * s)
    w3 = -rad.sqrt()
    dw3 = -(w4 * dw4 + w5 * dw5) / w3
    return dw3 * hA / 2 + A * s / (4 * c ** 3)


def domain_excluded(C1, C2, equal, p0, p1):
    """Certified: w4^2 + w5^2 > 1 for all phi in [p0, p1] (0 <= p0 < p1 <= pi)."""
    A, B = (C1 + C2).abs_lower(), (C1 - C2).abs_lower()
    cmax = (arb(p0) / 2).cos()          # cos(phi/2) <= cos(p0/2)
    smax = (arb(p1) / 2).sin()          # sin(phi/2) <= sin(p1/2)
    lb = (A / (2 * cmax)) ** 2
    if not equal:
        lb = lb + (B / (2 * smax)) ** 2
    return lb > 1


def roots_for_theta_box(q1, q2, tlo, thi, tol=1e-7):
    C1, C2 = consts(q1, q2)
    equal = q1 == q2
    theta = iv(tlo, thi)
    _, hA, _, _ = antiprism_data(theta)
    pmax = float_lower(PI)
    stack = [(0.0, pmax)]
    keep = []
    while stack:
        p0, p1 = stack.pop()
        if domain_excluded(C1, C2, equal, p0, p1):
            continue
        phi = iv(p0, p1)
        try:
            gv = g_val(C1, C2, equal, hA, phi)
        except OutOfDomain:          # 1 - w4^2 - w5^2 < 0 on the whole box
            continue
        if gv.is_finite() and (gv > 0 or gv < 0):
            continue
        if p1 - p0 < tol:
            keep.append((p0, p1))
            continue
        m = (p0 + p1) / 2
        stack += [(p0, m), (m, p1)]
    # the last bisection box ends at float(pi.lower()) < pi: check the gap
    if not domain_excluded(C1, C2, equal, pmax, float_upper(PI)):
        raise Undecided("phi near pi")
    keep.sort()
    clusters = []
    for p0, p1 in keep:
        if clusters and p0 <= clusters[-1][1]:
            clusters[-1][1] = max(clusters[-1][1], p1)
        else:
            clusters.append([p0, p1])
    out = []
    for p0, p1 in clusters:
        hull = iv(p0, p1)
        d = g_der(C1, C2, equal, hA, hull)
        g0 = g_val(C1, C2, equal, hA, arb(p0))
        g1 = g_val(C1, C2, equal, hA, arb(p1))
        mono = d > 0 or d < 0
        change = (g0 < 0 and g1 > 0) or (g0 > 0 and g1 < 0)
        if not (mono and change):
            raise Undecided("root cluster [%r, %r] for theta [%r, %r]" % (p0, p1, tlo, thi))
        out.append(hull)
    return out


def all_roots(q1, q2, nt=16):
    """Partition [0, pi/17] into nt theta-boxes; per box the list of root
    enclosures (each exactly one root per theta)."""
    T = float_upper(PI / 17)
    res = []
    for i in range(nt):
        tlo, thi = T * i / nt, T * (i + 1) / nt
        res.append((tlo, thi, roots_for_theta_box(q1, q2, tlo, thi)))
    return res


if __name__ == "__main__":
    for q1, q2 in ((3, 3), (3, 4), (3, 5)):
        rs = all_roots(q1, q2)
        print((q1, q2), "roots per theta-box:", sorted(set(len(r[2]) for r in rs)),
              "phi range", rs[0][2][0].str(8), rs[-1][2][0].str(8))
