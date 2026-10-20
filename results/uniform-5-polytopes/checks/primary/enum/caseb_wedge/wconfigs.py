"""Configurations around a large n-gon F (CASEB.md (F5)) and paired fans."""
from fractions import Fraction
from numbers import Integral


def canon(c):
    """Lexicographically least rotation / reflection of a cyclic tuple."""
    k = len(c)
    reps = []
    for s in (c, c[::-1]):
        for i in range(k):
            reps.append(tuple(s[i:] + s[:i]))
    return min(reps)


def type_i_configs(qmax=16):
    """Cyclic (q_1..q_k), k = 3, 4, 5, entries 3..qmax, sum(1 - 2/q_i) < 2,
    up to rotation and reflection."""
    out = set()

    def rec(pre, k):
        if len(pre) == k:
            if sum(1 - Fraction(2, q) for q in pre) < 2:
                out.add(canon(tuple(pre)))
            return
        for q in range(3, qmax + 1):
            rec(pre + [q], k)
    for k in (3, 4, 5):
        rec([], k)
    return sorted(out, key=lambda c: (len(c), c))


# paired type (i): (m, *rest); unbounded families (all m >= 17 and m = infinity)
PAIRED_UNBOUNDED = [(4, 4), (3, 6), (3, 3, 3)]
# bounded families: rest -> integer range of m
PAIRED_BOUNDED = {(3, 7): range(17, 42), (3, 8): range(17, 24), (3, 9): range(17, 18),
                  (4, 5): range(17, 20)}
PAIRED_NOT_CLOSABLE = [(3, 3), (3, 4), (3, 5)]
TYPE_III = [(3, 3), (3, 4), (3, 5)]

if __name__ == "__main__":
    cs = type_i_configs()
    print(len(cs), [len([c for c in cs if len(c) == k]) for k in (3, 4, 5)])


def require_bounded_slice(rest, m):
    """Reject noninteger and out-of-range m before constructing any geometry."""
    rest = tuple(rest)
    if isinstance(m, bool) or not isinstance(m, Integral):
        raise ValueError(f"bounded-family m must be an integer: {m!r}")
    if rest not in PAIRED_BOUNDED or m not in PAIRED_BOUNDED[rest]:
        raise ValueError(f"unsupported bounded-family integer slice: {(m, *rest)}")
    return int(m)


def domain_summary():
    return {"n": "real >=17, including infinity; seven exceptions use integer n=m",
            "bounded_m": [{"rest": list(rest), "kind": "integer_slices",
                           "values": list(ms)} for rest, ms in PAIRED_BOUNDED.items()],
            "unbounded_m": "real >=17, including infinity (four polar families)"}
