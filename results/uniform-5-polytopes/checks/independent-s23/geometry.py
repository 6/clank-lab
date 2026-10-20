"""Directed ball linear algebra. No comparison interprets overlap as equality."""
from flint import arb, ctx

ctx.prec = 256


class Undecided(Exception):
    """Insufficient enclosure; must propagate to an OPEN result."""


class Impossible(Exception):
    """A certified necessary condition fails in a hypothetical polytope."""


def ball_interval(lo, hi):
    from fractions import Fraction
    if Fraction(lo) > Fraction(hi):
        raise ValueError('reversed interval')
    return arb(lo).union(arb(hi))


def dot(a, b):
    return sum((x*y for x, y in zip(a, b, strict=True)), arb(0))


def add(a, b):
    return tuple(x+y for x, y in zip(a, b, strict=True))


def sub(a, b):
    return tuple(x-y for x, y in zip(a, b, strict=True))


def scale(s, a):
    return tuple(s*x for x in a)


def norm2(a):
    return sum((x*x for x in a), arb(0))


def distance2(a, b):
    return norm2(sub(a,b))


def positive_sqrt(x):
    if x <= 0:
        raise Impossible('nonpositive squared length/height')
    if not x > 0:
        raise Undecided('squared length/height straddles zero')
    y = x.sqrt()
    if not y.is_finite():
        raise Undecided('nonfinite square root')
    return y


def unit(a):
    return scale(1/positive_sqrt(norm2(a)), a)


def gram_schmidt(vectors):
    result = []
    for v in vectors:
        q = tuple(v)
        for e in result:
            q = sub(q, scale(dot(q,e),e))
        result.append(unit(q))
    return tuple(result)


def cross(a, b):
    if not (len(a) == len(b) == 3):
        raise AssertionError()
    return (a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2], a[0]*b[1]-a[1]*b[0])


def identity(a, b):
    """Conditional on both points belonging to the same unit-edge polytope.

    Paper Cor. decision rule, with the stricter equality bound 1/4.
    An interval wholly in (0,1) is a contradiction, even if also <1/4.
    """
    d = distance2(a,b)
    if not d.is_finite():
        raise Undecided('nonfinite squared distance')
    if d > 0:
        if d < 1:
            raise Impossible('separation: squared distance strictly between 0 and 1')
        return False
    if d < arb(1)/4:
        return True
    raise Undecided('point identity permits equality and distinctness')


def resolve(point, points):
    found = []
    for i,q in enumerate(points):
        if identity(point,q):
            found.append(i)
    if len(found) > 1:
        raise Impossible('one vertex equals distinct indexed vertices')
    return found[0] if found else None


def encode_ball(x):
    """Roundtrip outward enclosure, for archival witnesses only."""
    return x.str(90, radius=True)


def encode_points(points):
    return [[encode_ball(x) for x in p] for p in points]
