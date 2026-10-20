"""Independent Arb/Sturm check of B2's complete finite type-(iii) root lists.

Does not import b2check or the producer. Counts every real root in (-1,1)
by Sturm variations, then checks the exact dyadic brackets, derivative
signs and geometric labels. Omega comparisons remain b2check's job.
"""
import argparse
from collections import Counter, defaultdict
import copy
import json
from flint import arb, ctx

ctx.prec = 320


def sign(x):
    if x > 0:
        return 1
    if x < 0:
        return -1
    raise ValueError('uncertified strict sign')


def value(p, x):
    y = arb(0)
    for c in reversed(p):
        y = y * x + c
    return y


def derivative(p):
    return [i * p[i] for i in range(1, len(p))]


def sturm_count(p):
    chain = [p, derivative(p)]
    while len(chain[-1]) > 1:
        a, b = list(chain[-2]), chain[-1]
        sign(b[-1])  # division is legitimate only for a nonzero coefficient
        while len(a) >= len(b):
            offset = len(a) - len(b)
            q = a[-1] / b[-1]
            for i in range(len(b) - 1):
                a[offset + i] -= q * b[i]
            # The leading term cancels identically in polynomial division.
            a.pop()
        chain.append([-x for x in a])
    sign(chain[-1][0])  # no repeated roots / zero final remainder
    def variations(x):
        signs = [sign(value(p, arb(x))) for p in chain]
        return sum(a != b for a, b in zip(signs, signs[1:]))
    return variations(-1) - variations(1)


def polynomial(n, q1, q2):
    h2 = 1 - 1 / (4 * (arb.pi() / (2 * n)).cos() ** 2)
    def cosine(q):
        return {3: arb(1) / 2, 4: arb(0)}.get(q, -(2 * arb.pi() / q).cos())
    u, v = cosine(q1), cosine(q2)
    if q1 == q2:
        a = 1 - 2 * u
        return [h2 * (1 - 2 * u * u) - a * a,
                h2 * (2 - 2 * u * u) - 2 * a, h2 - 1], u + v
    a, d, e = 1 - u - v, 1 - u * u - v * v, 2 * u * v
    return [h2 * d - a * a, h2 * (d + e) - 2 * a + a * a,
            h2 * (e - 1) - 1 + 2 * a, 1 - h2], u + v


def dyadic(t):
    s, m, e, bc = t
    if any(type(v) is not int for v in (s, e, bc)) or not isinstance(m, str):
        raise ValueError('nonintegral exact binary endpoint')
    m = int(m)
    if s not in (0, 1) or m < 0 or bc != m.bit_length():
        raise ValueError('bad exact binary endpoint')
    return (-1 if s else 1) * arb(m) * arb(2) ** e


def check(data, nmin, nmax):
    if data['domain'] != [-1, 1] or not data['domain_open'] or data['undecided'] != 0:
        raise ValueError('wrong root domain or unresolved boxes')
    groups = defaultdict(list)
    for row in data['roots']:
        groups[(row['n'], *row['qs'])].append(row)
    expected = {(n, 3, q) for n in range(nmin, nmax + 1) for q in (3, 4, 5)}
    if set(groups) != expected:
        raise ValueError('missing or unexpected parameter pair')
    counts, negative = Counter(), Counter()
    for key in sorted(expected):
        p, uv = polynomial(*key)
        rows = groups[key]
        if sturm_count(p) != len(rows):
            raise ValueError(f'incomplete real-root list at {key}')
        boxes = []
        for row in rows:
            l, h = map(dyadic, row['c_dyadic'])
            if not (-1 < l and l <= h and h < 1):
                raise ValueError('root bracket outside (-1,1)')
            box = l.union(h)
            if sign(value(p, l)) != -sign(value(p, h)):
                raise ValueError('root bracket lacks opposite signs')
            sign(value(derivative(p), box))
            category = 'geo' if sign(1 - uv / (1 + box)) < 0 else 'nongeo'
            if category != row['category']:
                raise ValueError('wrong geometric label')
            counts[category] += 1
            negative[category] += int(h < 0)
            boxes.append((l, h))
        boxes.sort(key=lambda pair: pair[0])
        if any(not a[1] < b[0] for a, b in zip(boxes, boxes[1:])):
            raise ValueError('duplicate or overlapping root brackets')
    for category in ('geo', 'nongeo'):
        if counts[category] != data['categories'][category]['total'] \
                or negative[category] != data['categories'][category]['negative']:
            raise ValueError('root summary disagrees with brackets')
    return dict(parameter_pairs=len(expected), roots=sum(counts.values()),
                counts=dict(counts), negative=dict(negative), arb_precision=ctx.prec)


def corruptions(data, nmin, nmax):
    variants = {}
    bad = copy.deepcopy(data)
    index = next(i for i, row in enumerate(bad['roots'])
                 if row['category'] == 'nongeo' and dyadic(row['c_dyadic'][1]) < 0)
    bad['roots'].pop(index)
    variants['dropped_negative_nongeometric_root'] = bad
    bad = copy.deepcopy(data)
    bad['roots'].append(copy.deepcopy(bad['roots'][0]))
    variants['duplicated_root'] = bad
    bad = copy.deepcopy(data)
    bad['roots'][0]['category'] = 'nongeo' if bad['roots'][0]['category'] == 'geo' else 'geo'
    variants['wrong_branch'] = bad
    bad = copy.deepcopy(data)
    bad['roots'][0]['c_dyadic'][0] = [1, '1', 0, 1]
    variants['endpoint_instead_of_interior_bracket'] = bad
    rejected = {}
    for name, bad in variants.items():
        try:
            check(bad, nmin, nmax)
        except ValueError as exc:
            rejected[name] = str(exc)
        else:
            raise ValueError(f'root-audit corruption not rejected: {name}')
    return rejected


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('audit')
    ap.add_argument('--control', action='store_true')
    ap.add_argument('--corruptions', action='store_true')
    args = ap.parse_args()
    with open(args.audit) as f:
        data = json.load(f)
    nmin, nmax = (3, 16) if args.control else (17, 397)
    result = check(data, nmin, nmax)
    if args.corruptions:
        result['corruptions_rejected'] = corruptions(data, nmin, nmax)
    print(json.dumps(result, sort_keys=True))
