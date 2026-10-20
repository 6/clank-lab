"""Small independent outward interval helpers. No legacy implementation imports."""
from fractions import Fraction
from functools import lru_cache
from flint import arb, fmpq, ctx

ctx.prec = 256

class Undecided(RuntimeError):
    pass


def ball(x):
    if isinstance(x, arb):
        return x
    if isinstance(x, Fraction):
        return arb(fmpq(x.numerator, x.denominator))
    return arb(x)


def endpoints(x):
    """Exact rational endpoints of an Arb ball, including its rounding error."""
    x = ball(x)
    if not x.is_finite():
        raise Undecided('nonfinite interval')
    return Fraction(str(x.lower().fmpq())), Fraction(str(x.upper().fmpq()))


def hull(lo, hi):
    if lo > hi:
        raise ValueError('reversed interval')
    return ball(lo).union(ball(hi))


def sign(x):
    x = ball(x)
    if x > 0:
        return 1
    if x < 0:
        return -1
    if x.is_zero():
        return 0
    raise Undecided('sign straddles zero')


def acos_clip(x):
    """Enclose acos on intersection with [-1,1]. Caller proves domain.

    Evaluate exact endpoints separately, so outward ball rounding at +/-1
    cannot accidentally turn an admissible endpoint into an Arb NaN.
    Arb's acos itself is a certified inverse-trigonometric enclosure.
    """
    lo, hi = endpoints(x)
    lo, hi = max(lo, Fraction(-1)), min(hi, Fraction(1))
    if lo > hi:
        raise Undecided('empty inverse cosine domain')
    return ball(hi).acos().union(ball(lo).acos())


def decimal_bounds(x, digits=38):
    lo, hi = endpoints(x)
    scale = 10**digits
    a = (lo.numerator * scale) // lo.denominator
    b = -((-hi.numerator * scale) // hi.denominator)
    def dec(n):
        s = '-' if n < 0 else ''
        n = abs(n)
        return s + str(n // scale) + '.' + str(n % scale).zfill(digits)
    return [dec(a), dec(b)]


@lru_cache(None)
def evaluate(expr):
    """Evaluate a SymPy algebraic expression recursively in Arb.

    No decimal approximation is admitted as an exact algebraic input.
    """
    import sympy as sp
    expr = sp.sympify(expr)
    if expr.is_Rational:
        return arb(fmpq(int(expr.p), int(expr.q)))
    if expr == sp.pi:
        return arb.pi()
    if isinstance(expr, sp.CRootOf):
        interval=expr._get_interval().refine_size(sp.Rational(1,2**(ctx.prec+40)))
        return hull(Fraction(str(interval.a)),Fraction(str(interval.b)))
    if expr.func == sp.Add:
        return sum((evaluate(a) for a in expr.args), arb(0))
    if expr.func == sp.Mul:
        z = arb(1)
        for a in expr.args:
            z *= evaluate(a)
        return z
    if expr.func == sp.Pow:
        x, n = expr.args
        if n.is_Integer:
            return evaluate(x) ** int(n)
        if n.is_Rational:
            v=evaluate(x)
            if not v > 0:
                raise Undecided("nonpositive fractional-power base")
            return v.root(int(n.q)) ** int(n.p)
    if expr.func == sp.cos:
        return evaluate(expr.args[0]).cos()
    if expr.func == sp.sin:
        return evaluate(expr.args[0]).sin()
    raise ValueError('unsupported exact expression: ' + str(expr))
