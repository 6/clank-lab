"""Fan geometry for the wedge lemma (W), written from CASEB.md.

Coordinates (v = 0 in R^5): e1, e2 span the plane L of the large n-gon F,
the n-gon centre is r_n e1, a = (s, C, 0, 0, 0), b = (s, -C, 0, 0, 0) with
s = sin(pi/n), C = cos(pi/n) (n = infinity: s = 0).  The last three
coordinates xi are an orthonormal frame of L-perp.  A VF-vertex is a unit
vector p with p . c = 1/2 (c = P's centre); writing c = r_n e1 + gamma
(gamma in L-perp) gives p1 = s (1 - 2 gamma . xi).  The chart is xi (three
free coordinates), p1 from that formula, p2 = sign * sqrt(rad),
rad = 1 - p1^2 - |xi|^2.

Facet hyperplanes all contain a and b, hence L; the inner side of a facet
through the L-perp vectors u, u' is (u x u') . xi >= 0 up to orientation.

For the four paired families with m unbounded ((m,4,4), (m,3,3,3), (m,3,6),
type (ii) with q = m) gamma = r_m e_hat + gamma0 is unbounded; there the
chart is the "(tau, theta)" chart described in README.md: s = lam tau,
sigma = sin(pi/m) = om tau, lam = min(1, theta), om = min(1, 2 - theta),
free (Pi, f1, f2) with xi = (om Pi, f1, f2), p1 = lam (tau (1 - 2 gamma0.f) - Pi).
Facet functions are the true ones divided by om > 0 (or by sigma for the
facet through the partner m-gon), which keeps them non-degenerate at m = oo.
"""
import os
from fractions import Fraction
from numbers import Integral

import numpy as np
from mpmath import iv, mpf

import ia
from ia import I, sqrt, const, imin
import p1check

iv.prec = 200
PI = iv.pi
# deliberate corruption (corrupt.sh): W_CORRUPT=nodist drops the separation
# constraints |p - u| >= 1 (F1) for the fan vertices u (applied in bnb.py).
CORRUPT = os.environ.get("W_CORRUPT", "")
S17 = iv.sin(PI / 17)
KAPPA = iv.cos(2 * PI / 17)       # long edge <=> p.p' <= -KAPPA
BETA = iv.sin(PI / 17)            # pair test threshold for p.u (|u| = 1)


def cnst(x):
    return const(x)


HALF = I(0.5)
ZERO = I(0.0)
ONE = I(1.0)


def cross(u, v):
    return (u[1] * v[2] - u[2] * v[1], u[2] * v[0] - u[0] * v[2], u[0] * v[1] - u[1] * v[0])


def vec5(p1, p2, x):
    return (p1, p2, x[0], x[1], x[2])


def dot5(u, v):
    return ia.dot(u, v)


def n_quantities(s):
    """s = sin(pi/n) interval in [0, sin(pi/17)]: C, t = tan(pi/2n)/2,
    h = height of the unit antiprism A_n."""
    C = sqrt(1 - s.sq())
    t = s / (2 * (1 + C))
    h = sqrt(1 - 1 / (2 * (1 + C)))
    return C, t, h


# Bounded paired families are integer slices, not intervals of real m.
BOUNDED_LIMITS = {(3, 7): 41, (3, 8): 23, (3, 9): 17, (4, 5): 19}


def require_integer(q, minimum, label):
    if isinstance(q, bool) or not isinstance(q, Integral) or q < minimum:
        raise ValueError(f"{label} must be an integer >= {minimum}: {q!r}")


def integer_config(config):
    c = tuple(config)
    for q in c:
        require_integer(q, 3, "polygon parameter")
    if c and c[0] >= 17 and c[1:] in BOUNDED_LIMITS:
        require_integer(c[0], 17, "bounded-family m")
        if c[0] > BOUNDED_LIMITS[c[1:]]:
            raise ValueError(f"bounded-family integer m outside range: {c}")
    return c


def parameter_domain(fan):
    """Machine-readable scope, including exceptional integer n=m points."""
    n = {"kind": "real", "min": 17, "includes_infinity": True}
    if getattr(fan, "fixed_n", None) is not None:
        n = {"kind": "integer_point", "value": fan.fixed_n}
    out = {"n": n}
    if isinstance(fan, FanTypeI) and fan.config[0] >= 17 and fan.config[1:] in BOUNDED_LIMITS:
        c = integer_config(fan.config)
        out["m"] = {"kind": "integer_slice", "value": int(c[0]),
                    "min": 17, "max": BOUNDED_LIMITS[c[1:]]}
    elif isinstance(fan, FanFamily):
        out["m"] = {"kind": "real", "min": 17, "includes_infinity": True}
    return out


def certify_family_chart(fan, box):
    """G4: certify actual gamma0 on the entire parameter box before B&B.

    Unit sphere: |p1|, |xi_e|, |f| <= 1. theta<=1: om=1, Pi=xi_e.
    theta>=1: lam=1, Pi+p1=tau(1-2 gamma0.f). Thus |Pi| <=
    1+tau(1+2|gamma0|) < 1.41. See repair-caseb-w/REPAIR.md for
    the rational proof and the four actual gamma0 formulas.
    """
    pb = fan.param_box()
    if pb[0][0] != 0 or pb[1] != (0.0, 2.0):
        raise ValueError("family parameter chart must cover tau>=0, theta in [0,2]")
    tmax = pb[0][1]
    if not tmax >= ia._f_up(mpf(S17.b)) or Fraction(tmax) >= Fraction(23, 125):
        raise ValueError("family tau bound must enclose sin(pi/17) and be <23/125")
    st = fan.structure([I(0.0, tmax), I(0.0, 2.0)])
    g0 = st[8]
    norm = sqrt(g0[0].sq() + g0[1].sq())
    if not Fraction(float(norm.hi)) < Fraction(25, 43):
        raise ValueError("family gamma0 bound not certified")
    bound = 1 + I(tmax) * (1 + 2 * norm)
    if not Fraction(float(bound.hi)) < Fraction(141, 100):
        raise ValueError("family Pi bound not certified below 1.41")
    required = (Fraction(141, 100), Fraction(1), Fraction(1))
    if len(box) != 3 or any(Fraction(a) > -b or Fraction(c) < b
                            for (a, c), b in zip(box, required)):
        raise ValueError("family free-coordinate domain truncates certified coverage")
    return {"gamma0_norm_upper": float(norm.hi), "Pi_abs_upper": float(bound.hi),
            "theta_le_1_Pi_abs_upper": 1, "tau_upper": tmax}


class Geo:
    """what a fan returns for a batch of boxes."""
    __slots__ = ("p", "rad", "facets", "verts", "names")


# --------------------------------------------------------------------------
class FanTypeI:
    """type (i) fan with a fixed configuration (q_1..q_k) (unpaired, or a
    paired one with a fixed m).  Parameter: s = sin(pi/n)."""

    nparam = 1

    def __init__(self, config, corrupt=None):
        self.config = integer_config(config)
        config = self.config
        self.name = "(i)" + str(self.config).replace(" ", "")
        chords = [p1check.chord(q) for q in config]
        S = p1check.config_S(chords)
        cosr = iv.sqrt(1 - S * S)
        phis = [iv.mpf(0)]
        for l in chords[:-1]:
            phis.append(phis[-1] + 2 * p1check.asin(l / (2 * S)))
        xs = [(S * iv.cos(ph), S * iv.sin(ph), cosr) for ph in phis]
        if corrupt == "config":
            # deliberate corruption: move the last ray (breaks the fan)
            x = xs[-1]
            xs[-1] = (x[0] * mpf("0.97"), x[1] * mpf("0.97"), iv.sqrt(1 - (x[0] * mpf("0.97")) ** 2 - (x[1] * mpf("0.97")) ** 2))
        # closure check: the chord x_k x_1 is l_k
        lk = iv.sqrt(sum((a - b) ** 2 for a, b in zip(xs[-1], xs[0])))
        if not (p1check.sign_of(lk - chords[-1]) == 0 or corrupt):
            raise AssertionError((config, lk, chords[-1]))
        self.x = [tuple(const(c) for c in x) for x in xs]
        self.g3 = const(1 / (2 * cosr))   # gamma = (0, 0, g3)
        k = len(xs)
        normals = []
        for i in range(k):
            u, w = xs[i], xs[(i + 1) % k]
            nu = (u[1] * w[2] - u[2] * w[1], u[2] * w[0] - u[0] * w[2], u[0] * w[1] - u[1] * w[0])
            # orientation: the axis (0,0,1) is inside the cone (closable)
            if not (p1check.lo(nu[2]) > 0):
                raise AssertionError()
            # every other ray strictly inside
            for j in range(k):
                if j not in (i, (i + 1) % k):
                    if not (p1check.lo(sum(a * b for a, b in zip(nu, xs[j]))) > 0):
                        raise AssertionError((config, i, j))
            normals.append(tuple(const(c) for c in nu))
        self.normals = normals
        self.R2c = const(1 / (4 * (1 - S * S)))
        self.partner = None

    pbox = None

    def param_box(self):
        if self.pbox is not None:
            return self.pbox
        return [(0.0, ia._f_up(mpf(S17.b)))]

    def restrict_n(self, n):
        """parameter box = the single value s = sin(pi/n) (outward)."""
        require_integer(n, 17, "restricted n")
        self.fixed_n = int(n)
        e = const(iv.sin(PI / n))
        self.pbox = [(float(e.lo), float(e.hi))]
        self.name = self.name + f"@n={n}"

    def free_box(self):
        return [(-1.0, 1.0), (-1.0, 1.0), (0.0, 1.0)]

    def vertices(self, P):
        s = P[0]
        C = sqrt(1 - s.sq())
        z = ZERO
        V = [("a", (s, C, z, z, z)), ("b", (s, -C, z, z, z))]
        for i, x in enumerate(self.x):
            V.append((f"x{i+1}", (z, z, x[0], x[1], x[2])))
        return V

    def evaluate(self, P, F, sign):
        s = P[0]
        xi = F
        p1 = s * (1 - 2 * self.g3 * xi[2])
        rad = 1 - p1.sq() - xi[0].sq() - xi[1].sq() - xi[2].sq()
        r = sqrt(rad)
        p2 = r if sign > 0 else -r
        g = Geo()
        g.p = (p1, p2, xi[0], xi[1], xi[2])
        g.rad = rad
        g.facets = [ia.dot(nu, xi) for nu in self.normals]
        g.verts = self.vertices(P)
        return g

    def udir(self, P):
        """unit vector for the pair test: the cone axis (0,0,0,0,1)."""
        z = ZERO
        return (z, z, z, z, ONE)

    def describe(self):
        return f"type (i) {self.config}, R_c^2 = {self.R2c.mid:.9f}"


# --------------------------------------------------------------------------
class FanBounded(FanTypeI):
    """A bounded family at one integer m; n remains continuous until restricted."""

    def __init__(self, m, rest):
        rest = tuple(rest)
        require_integer(m, 17, "bounded-family m")
        if rest not in BOUNDED_LIMITS or m > BOUNDED_LIMITS[rest]:
            raise ValueError(f"unsupported bounded-family integer slice: {(m, *rest)}")
        super().__init__((int(m), *rest))
        self.partner, self.m = ("x1", "x2"), int(m)


# --------------------------------------------------------------------------
class FanTypeII:
    """type (ii): A_n x {}, A_n x {}, {n}x{q}, q fixed.  L-perp frame
    (e3 = antiprism axis, e4, e5 = M-perp).  Parameter s."""

    nparam = 1

    def __init__(self, q):
        self.q = q
        self.name = f"(ii)q={q}"
        self.sq_ = const(iv.sin(PI / q))
        self.cq = const(iv.cos(PI / q))
        self.rq = const(1 / (2 * iv.sin(PI / q)))
        self.partner = None

    def param_box(self):
        return [(0.0, ia._f_up(mpf(S17.b)))]

    def free_box(self):
        return [(0.0, 1.0), (-1.0, 1.0), (-1.0, 1.0)]

    def vertices(self, P):
        s = P[0]
        C, t, h = n_quantities(s)
        z = ZERO
        return [("a", (s, C, z, z, z)), ("b", (s, -C, z, z, z)),
                ("x", (t, HALF, h, z, z)), ("y", (t, -HALF, h, z, z)),
                ("z1", (z, z, z, self.sq_, self.cq)), ("z2", (z, z, z, self.sq_, -self.cq))]

    def evaluate(self, P, F, sign):
        s = P[0]
        C, t, h = n_quantities(s)
        xi = F
        p1 = s * (1 - h * xi[0] - 2 * self.rq * xi[1])
        rad = 1 - p1.sq() - xi[0].sq() - xi[1].sq() - xi[2].sq()
        r = sqrt(rad)
        p2 = r if sign > 0 else -r
        g = Geo()
        g.p = (p1, p2, xi[0], xi[1], xi[2])
        g.rad = rad
        # Pi_1 (through z1): normal (0, C_q, -sin_q); Pi_2: (0, C_q, sin_q);
        # T (through z1, z2): e3
        g.facets = [self.cq * xi[1] - self.sq_ * xi[2], self.cq * xi[1] + self.sq_ * xi[2], xi[0]]
        g.verts = self.vertices(P)
        return g

    u = None

    def udir(self, P):
        return tuple(I(c) for c in self.u)

    def describe(self):
        return f"type (ii) q = {self.q}"


# --------------------------------------------------------------------------
class FanTypeIII:
    """type (iii): A_n x {}, A_n x {}, {n}x{q1}, {n}x{q2}.  z1 = (0, cphi,
    sphi), z2 = (0, cphi, -sphi) in M-perp; w = (w3, w4, w5) in L-perp with
    w.z1 = k1 = -cos(2pi/q1), w.z2 = k2, w3 < 0 (convexity); the centre
    condition w.gamma = 1/2 gives h = (w4/cphi - 1)/|w3|, which must be the
    antiprism height h_n for some n >= 17.  Parameter: cphi."""

    nparam = 1

    def __init__(self, q1, q2):
        self.q = (q1, q2)
        self.name = f"(iii)({q1},{q2})"
        self.k1 = const(-iv.cos(2 * PI / q1))
        self.k2 = const(-iv.cos(2 * PI / q2))
        # h_n range: h^2 = 1 - 1/(2(1+C)), C in [cos(pi/17), 1]
        c17 = iv.cos(PI / 17)
        self.h17 = const(iv.sqrt(1 - 1 / (2 * (1 + c17))))
        self.hmax = const(iv.sqrt(iv.mpf(3)) / 2)
        self.C17 = const(c17)
        self.partner = None
        # end exclusions (see README): cphi <= 2^-20 gives w4 > 1, cphi >=
        # 1 - 2^-40 gives |w5| > 1 (q1 != q2) or h < 0 (q1 = q2)
        kk1, kk2 = -iv.cos(2 * PI / q1), -iv.cos(2 * PI / q2)
        if not (p1check.lo((kk1 + kk2) / 2 * 2 ** 20) > 1):
            raise AssertionError()
        if q1 != q2:
            if not (p1check.lo(abs(kk1 - kk2) / (2 * iv.sqrt(iv.mpf(2) * 2 ** -40))) > 1):
                raise AssertionError()
        else:
            # q1 = q2 = 3: w4/cphi - 1 = 1/(2 cphi^2) - 1 < 0 for cphi > 1/sqrt 2
            if not (q1 == 3 and p1check.hi(abs(kk1 - iv.mpf(1) / 2)) < mpf(10) ** -50):
                raise AssertionError()

    def param_box(self):
        return [(2.0 ** -20, 1.0 - 2.0 ** -40)]

    def free_box(self):
        return [(-1.0, 1.0), (-1.0, 1.0), (-1.0, 1.0)]

    def geometry(self, P):
        c = P[0]
        sp = sqrt(1 - c.sq())
        w4 = (self.k1 + self.k2) / (2 * c)
        w5 = (self.k1 - self.k2) / (2 * sp)
        rad3 = 1 - w4.sq() - w5.sq()
        w3a = sqrt(rad3)                 # |w3|
        num = w4 / c - 1                 # = h |w3|
        # feasibility of the parameter box: rad3 >= 0 and num in [h17, hmax]*|w3|
        ok = (rad3.hi >= 0) & (num.hi >= (self.h17 * w3a).lo) & (num.lo <= (self.hmax * w3a).hi)
        pos = w3a.lo > 0
        safe = I(ia.np.where(pos, w3a.lo, 1.0), ia.np.where(pos, w3a.hi, 1.0))
        hq = num / safe
        hlo = ia.np.where(pos, ia.np.maximum(hq.lo, self.h17.lo), self.h17.lo)
        hhi = ia.np.where(pos, ia.np.minimum(hq.hi, self.hmax.hi), self.hmax.hi)
        ok = ok & (hlo <= hhi)
        hlo = ia.np.minimum(hlo, hhi)
        h = I(hlo, hhi)
        # n from h: C = 1/(2(1-h^2)) - 1 clipped to [C17, 1]
        Cr = 1 / (2 * (1 - h.sq())) - 1
        C = I(ia.np.clip(Cr.lo, self.C17.lo, 1.0), ia.np.clip(Cr.hi, self.C17.lo, 1.0))
        s = sqrt(1 - C.sq())
        t = s / (2 * (1 + C))
        w = (-w3a, w4, w5)
        return ok, c, sp, w, h, C, s, t

    def vertices(self, P, geo=None):
        ok, c, sp, w, h, C, s, t = geo if geo is not None else self.geometry(P)
        z = ZERO
        return [("a", (s, C, z, z, z)), ("b", (s, -C, z, z, z)),
                ("x", (t, HALF, h, z, z)), ("y", (t, -HALF, h, z, z)),
                ("z1", (z, z, z, c, sp)), ("z2", (z, z, z, c, -sp)),
                ("w", (z, z, w[0], w[1], w[2]))]

    def evaluate(self, P, F, sign):
        geo = self.geometry(P)
        ok, c, sp, w, h, C, s, t = geo
        xi = F
        gam = (h / 2, 1 / (2 * c), ZERO)
        p1 = s * (1 - 2 * (gam[0] * xi[0] + gam[1] * xi[1]))
        rad = 1 - p1.sq() - xi[0].sq() - xi[1].sq() - xi[2].sq()
        # infeasible parameter boxes: force rad < 0
        rad = I(ia.np.where(ok, rad.lo, -1.0), ia.np.where(ok, rad.hi, -1.0))
        r = sqrt(rad)
        p2 = r if sign > 0 else -r
        z1 = (ZERO, c, sp)
        z2 = (ZERO, c, -sp)
        e3 = (ONE, ZERO, ZERO)
        g = Geo()
        g.p = (p1, p2, xi[0], xi[1], xi[2])
        g.rad = rad
        # orientations fixed in check_orientation(): Pi_1 = -(e3 x z1),
        # Pi_2 = e3 x z2, T1 = -(z1 x w)... signs stored in self.orient
        nus = [cross(e3, z1), cross(e3, z2), cross(z1, w), cross(w, z2)]
        g.facets = [ia.dot(nu, xi) * o for nu, o in zip(nus, self.orient)]
        g.verts = self.vertices(P, geo)
        return g

    orient = (1.0, 1.0, 1.0, 1.0)
    u = None

    def udir(self, P):
        return tuple(I(c) for c in self.u)

    def describe(self):
        return f"type (iii) {self.q}"


# --------------------------------------------------------------------------
class FanFamily:
    """the four paired families with m unbounded.  Parameters (tau, theta),
    tau in [0, sin(pi/17)], theta in [0, 2]; s = lam tau, sigma = om tau.
    Each L-perp fan vertex is stored as (chi, f) with xi = (sigma chi, f);
    non-L-perp vertices (type (ii): x, y) also carry (u1, u2)."""

    nparam = 2

    def __init__(self, kind):
        self.kind = kind
        self.name = {"44": "(m,4,4)", "333": "(m,3,3,3)", "36": "(m,3,6)", "ii": "(ii)q=m"}[kind]
        self.partner = "m"

    def param_box(self):
        return [(0.0, ia._f_up(mpf(S17.b))), (0.0, 2.0)]

    pi_box = (-1.5, 1.5)

    def free_box(self):
        box = [self.pi_box, (-1.0, 1.0), (-1.0, 1.0)]
        certify_family_chart(self, box)
        return box

    def structure(self, P):
        tau, th = P
        lam = imin(1.0, th)
        om = imin(1.0, 2 - th)
        s = lam * tau
        sig = om * tau
        Cn = sqrt(1 - s.sq())
        Cm = sqrt(1 - sig.sq())
        z = ZERO
        k = self.kind
        # L-perp vertices: name -> (u1, u2, chi, f1, f2)
        if k == "44":
            V = [("x1", z, z, ONE, Cm, z), ("x2", z, z, ONE, -Cm, z), ("x3", z, z, z, z, ONE)]
            g0 = (z, HALF)
            facets = [("x1", "x2", True), ("x2", "x3", False), ("x3", "x1", False)]
        elif k == "333":
            chi = 1 / (2 * (1 + Cm))
            hm = sqrt(1 - 1 / (2 * (1 + Cm)))
            V = [("x1", z, z, ONE, Cm, z), ("x2", z, z, ONE, -Cm, z),
                 ("x3", z, z, chi, -HALF, hm), ("x4", z, z, chi, HALF, hm)]
            g0 = (z, hm / 2)
            facets = [("x1", "x2", True), ("x2", "x3", False), ("x3", "x4", False), ("x4", "x1", False)]
        elif k == "36":
            dm = sqrt(1 - 1 / (4 * Cm.sq()))
            V = [("x1", z, z, ONE, Cm, z), ("x2", z, z, ONE, -Cm, z),
                 ("x3", z, z, z, -1 / (2 * Cm), dm)]
            g0 = (z, 1 / (2 * dm))
            facets = [("x1", "x2", True), ("x2", "x3", False), ("x3", "x1", False)]
        elif k == "ii":
            _, t, h = n_quantities(s)
            # frame (e_hat = e4, f1 = e3 antiprism axis, f2 = e5)
            V = [("x", t, HALF, z, h, z), ("y", t, -HALF, z, h, z),
                 ("z1", z, z, ONE, z, Cm), ("z2", z, z, ONE, z, -Cm)]
            g0 = (h / 2, z)
            facets = [("x", "z1", False), ("x", "z2", False), ("z1", "z2", True)]
        else:
            raise KeyError(k)
        return tau, lam, om, s, sig, Cn, Cm, V, g0, facets

    def vertices(self, P, st=None):
        tau, lam, om, s, sig, Cn, Cm, V, g0, facets = st if st is not None else self.structure(P)
        z = ZERO
        out = [("a", (s, Cn, z, z, z)), ("b", (s, -Cn, z, z, z))]
        for name, u1, u2, chi, f1, f2 in V:
            out.append((name, (u1, u2, sig * chi, f1, f2)))
        return out

    @staticmethod
    def facet_value(tau, uA, uB, partner, Pi, f):
        """(xi_A x xi_B) . xi divided by om (or by sigma for partner facets),
        with xi = (om Pi, f), xi_A = (sigma chi_A, fA)."""
        _, _, _, chiA, a1, a2 = uA
        _, _, _, chiB, b1, b2 = uB
        # e_hat x (0, g1, g2) = (0, -g2, g1)
        Nt1 = chiA * (-b2) - chiB * (-a2)
        Nt2 = chiA * b1 - chiB * a1
        if partner:
            return Nt1 * f[0] + Nt2 * f[1]
        Ne = a1 * b2 - a2 * b1
        return Ne * Pi + tau * (Nt1 * f[0] + Nt2 * f[1])

    def evaluate(self, P, F, sign):
        st = self.structure(P)
        tau, lam, om, s, sig, Cn, Cm, V, g0, facets = st
        Pi, f1, f2 = F
        p1 = lam * (tau * (1 - 2 * (g0[0] * f1 + g0[1] * f2)) - Pi)
        xe = om * Pi
        rad = 1 - p1.sq() - xe.sq() - f1.sq() - f2.sq()
        r = sqrt(rad)
        p2 = r if sign > 0 else -r
        g = Geo()
        g.p = (p1, p2, xe, f1, f2)
        g.rad = rad
        d = {v[0]: v for v in V}
        g.facets = [self.facet_value(tau, d[A], d[B], part, Pi, (f1, f2)) * o
                    for (A, B, part), o in zip(facets, self.orient)]
        g.verts = self.vertices(P, st)
        return g

    def facet_at_vertices(self, P):
        """values of each facet function at every fan vertex (orientation
        check); a vertex's chart coordinates are Pi = tau chi, f."""
        st = self.structure(P)
        tau, lam, om, s, sig, Cn, Cm, V, g0, facets = st
        d = {v[0]: v for v in V}
        out = []
        for (A, B, part), o in zip(facets, self.orient):
            row = {}
            for v in V:
                row[v[0]] = self.facet_value(tau, d[A], d[B], part, tau * v[3], (v[4], v[5])) * o
            out.append(((A, B), row))
        return out

    orient = None
    # pair-test direction g = (-lam, 0, om, k1 N, k2 N), N = |(lam, om)|:
    # in the (e1, e_hat) plane it is orthogonal to the VF normal (om, lam)
    UK = {"44": (0.0, 0.40625), "333": (0.0, 0.203125), "36": (0.0, 1.0), "ii": (0.25, 0.0)}

    def udir(self, P):
        tau, th = P
        lam = imin(1.0, th)
        om = imin(1.0, 2 - th)
        N = sqrt(lam.sq() + om.sq())
        k1, k2 = self.UK[self.kind]
        return (-lam, ZERO, om, N * k1, N * k2)

    def describe(self):
        return f"paired family {self.name}, m >= 17 incl. infinity"


# --------------------------------------------------------------------------
# orientation of facet normals (types (iii) and the families): fixed at a
# sample parameter, then verified over the parameter range by check_orient.
def _lperp_iii(fan, P):
    ok, c, sp, w, h, C, s, t = fan.geometry(P)
    z = ZERO
    V = {"a": (z, z, z), "b": (z, z, z), "x": (h, z, z), "y": (h, z, z),
         "z1": (z, c, sp), "z2": (z, c, -sp), "w": w}
    e3 = (ONE, z, z)
    nus = [cross(e3, V["z1"]), cross(e3, V["z2"]), cross(V["z1"], w), cross(w, V["z2"])]
    on = [{"a", "b", "x", "y", "z1"}, {"a", "b", "x", "y", "z2"}, {"a", "b", "z1", "w"}, {"a", "b", "w", "z2"}]
    return ok, V, nus, on


def orient_iii(fan, cphi):
    P = [I(cphi)]
    ok, V, nus, on = _lperp_iii(fan, P)
    if not (ok):
        raise AssertionError()
    o = []
    for nu, onf in zip(nus, on):
        vals = [float(ia.dot(nu, V[k]).mid) for k in V if k not in onf]
        if not (all(v > 0 for v in vals) or all(v < 0 for v in vals)):
            raise AssertionError(vals)
        o.append(1.0 if vals[0] > 0 else -1.0)
    fan.orient = tuple(o)


def check_orient_iii(fan, pieces=4096):
    """over all feasible parameter boxes: off-facet vertices strictly inside."""
    lo, hi = fan.param_box()[0]
    e = np.linspace(lo, hi, pieces + 1)
    P = [I(e[:-1], e[1:])]
    ok, V, nus, on = _lperp_iii(fan, P)
    nfeas = int(ok.sum())
    good = True
    for nu, onf, o in zip(nus, on, fan.orient):
        for k in V:
            if k in onf:
                continue
            val = ia.dot(nu, V[k]) * o
            good &= bool(np.all(val.lo[ok] > 0))
    return good, nfeas


def orient_family(fan, tau=0.1, theta=0.7):
    st = fan.structure([I(tau), I(theta)])
    fan.orient = tuple(1.0 for _ in st[9])
    o = []
    for (AB, row), (A, B, part) in zip(fan.facet_at_vertices([I(tau), I(theta)]), st[9]):
        vals = [float(v.mid) for k, v in row.items() if k not in (A, B) and not (fan.kind == "ii" and {k, A} == {"x", "y"}) and not (fan.kind == "ii" and {k, B} == {"x", "y"})]
        vals = [v for v in vals]
        if not (all(v > 0 for v in vals) or all(v < 0 for v in vals)):
            raise AssertionError((fan.name, AB, row))
        o.append(1.0 if vals[0] > 0 else -1.0)
    fan.orient = tuple(o)


def check_orient_family(fan, pieces=64):
    """tau-free form of each facet function at the off-facet fan vertices
    (value / tau for non-partner facets) is > 0 on a grid of parameter boxes
    covering tau in [0, sin(pi/17)], theta in [0, 2]."""
    (t0, t1), (h0, h1) = fan.param_box()
    te = np.linspace(t0, t1, pieces + 1)
    he = np.linspace(h0, h1, pieces + 1)
    T, H = np.meshgrid(np.arange(pieces), np.arange(pieces), indexing="ij")
    T, H = T.ravel(), H.ravel()
    P = [I(te[T], te[T + 1]), I(he[H], he[H + 1])]
    st = fan.structure(P)
    tau, lam, om, s, sig, Cn, Cm, V, g0, facets = st
    d = {v[0]: v for v in V}
    good = True
    for (A, B, part), o in zip(facets, fan.orient):
        for v in V:
            k = v[0]
            if k in (A, B) or (fan.kind == "ii" and "x" in (A, B) and k == "y"):
                continue
            if part:
                val = FanFamily.facet_value(tau, d[A], d[B], True, None, (v[4], v[5])) * o
            else:
                # (N_e chi_v + Nt . f_v): facet_value with tau -> 1 in both terms
                val = FanFamily.facet_value(ONE, d[A], d[B], False, v[3], (v[4], v[5])) * o
            good &= bool(np.all(val.lo > 0))
    return good
