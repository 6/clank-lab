"""Vectorised interval arithmetic on numpy float64 arrays with outward rounding.

Every elementary result is computed in IEEE-754 binary64 round-to-nearest
(numpy's +, -, *, /, sqrt are correctly rounded) and then widened by one ulp
outward with np.nextafter, so the true real result lies in [lo, hi].
Transcendental functions are never evaluated here: constants (pi, cos(pi/q),
...) are enclosed by mpmath.iv at high precision and converted outward with
`const`.
"""
import numpy as np
from mpmath import iv, mp, mpf, workprec

NINF = -np.inf
PINF = np.inf


def _dn(x):
    return np.nextafter(x, NINF)


def _up(x):
    return np.nextafter(x, PINF)


def _f_down(m):
    """largest float <= the mpf m (mpmath converts to nearest)."""
    f = float(m)
    if mpf(f) > m:
        f = float(np.nextafter(f, NINF))
    return f


def _f_up(m):
    f = float(m)
    if mpf(f) < m:
        f = float(np.nextafter(f, PINF))
    return f


class I:
    __slots__ = ("lo", "hi")
    __array_priority__ = 1000

    def __init__(self, lo, hi=None):
        if hi is None:
            hi = lo
        self.lo = np.asarray(lo, dtype=np.float64)
        self.hi = np.asarray(hi, dtype=np.float64)

    # ---- helpers
    @staticmethod
    def wrap(x):
        if isinstance(x, I):
            return x
        if isinstance(x, (int, np.integer)):
            f = float(x)
            if not (f == x):
                raise AssertionError()
            return I(f, f)
        if isinstance(x, float):
            # floats are taken as exact binary values; never pass decimals
            return I(x, x)
        raise TypeError(type(x))

    def __repr__(self):
        return f"I({self.lo}, {self.hi})"

    def __getitem__(self, k):
        return I(self.lo[k], self.hi[k])

    @property
    def mid(self):
        return 0.5 * (self.lo + self.hi)

    @property
    def wid(self):
        return self.hi - self.lo

    # ---- arithmetic
    def __add__(self, o):
        o = I.wrap(o)
        return I(_dn(self.lo + o.lo), _up(self.hi + o.hi))

    __radd__ = __add__

    def __neg__(self):
        return I(-self.hi, -self.lo)

    def __sub__(self, o):
        o = I.wrap(o)
        return I(_dn(self.lo - o.hi), _up(self.hi - o.lo))

    def __rsub__(self, o):
        return I.wrap(o) - self

    def __mul__(self, o):
        o = I.wrap(o)
        a, b, c, d = self.lo * o.lo, self.lo * o.hi, self.hi * o.lo, self.hi * o.hi
        lo = np.minimum(np.minimum(a, b), np.minimum(c, d))
        hi = np.maximum(np.maximum(a, b), np.maximum(c, d))
        # 0 * inf never occurs: all inputs finite in this code
        return I(_dn(lo), _up(hi))

    __rmul__ = __mul__

    def __truediv__(self, o):
        o = I.wrap(o)
        if np.any((o.lo <= 0) & (o.hi >= 0)):
            raise ZeroDivisionError("interval divisor contains 0")
        a, b, c, d = self.lo / o.lo, self.lo / o.hi, self.hi / o.lo, self.hi / o.hi
        lo = np.minimum(np.minimum(a, b), np.minimum(c, d))
        hi = np.maximum(np.maximum(a, b), np.maximum(c, d))
        return I(_dn(lo), _up(hi))

    def __rtruediv__(self, o):
        return I.wrap(o) / self

    def sq(self):
        a = self.lo * self.lo
        b = self.hi * self.hi
        hi = _up(np.maximum(a, b))
        lo = np.where((self.lo <= 0) & (self.hi >= 0), 0.0, _dn(np.minimum(a, b)))
        lo = np.maximum(lo, 0.0)
        return I(lo, hi)


def sqrt(x):
    """sqrt of the part of x that is >= 0 (callers have already discarded,
    or certified the infeasibility of, negative parts)."""
    lo = np.maximum(x.lo, 0.0)
    hi = np.maximum(x.hi, 0.0)
    return I(np.maximum(_dn(np.sqrt(lo)), 0.0), _up(np.sqrt(hi)))


def imin(x, y):
    x, y = I.wrap(x), I.wrap(y)
    return I(np.minimum(x.lo, y.lo), np.minimum(x.hi, y.hi))


def imax(x, y):
    x, y = I.wrap(x), I.wrap(y)
    return I(np.maximum(x.lo, y.lo), np.maximum(x.hi, y.hi))


def const(v):
    """outward float enclosure of an mpmath iv interval (or mpf).  The
    endpoints are converted at no less than iv.prec bits, so the result is
    outward whatever the global mp.prec (mpf(.) rounds to it)."""
    with workprec(max(mp.prec, iv.prec)):
        if hasattr(v, "a"):
            return I(_f_down(mpf(v.a)), _f_up(mpf(v.b)))
        m = mpf(v)
        return I(_f_down(m), _f_up(m))


def dot(u, v):
    s = u[0] * v[0]
    for a, b in zip(u[1:], v[1:]):
        s = s + a * b
    return s
