#!/usr/bin/env python3
"""Exact counts by a factorial formula and labeled-set / pivot recurrence."""
import copy
import json
from functools import cache
from math import comb, factorial
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def graph(b):
    n = 12 + 2 * b
    rows = [0] * n
    for v in range(n):
        for w in range(v + 1, n):
            edge = (v // 2 == w // 2 if w < 12 else
                    True if v < 12 else (v < 12 + b) == (w < 12 + b))
            if edge:
                rows[v] |= 1 << w
                rows[w] |= 1 << v
    return rows


def clique(n):
    return 0 if n % 2 else factorial(n) // (2 ** (n // 2) * factorial(n // 2))


def formula(b):
    def perfect(p, q, c, d):
        total = 0
        for s in range(p + 1):
            t = 2 * p + q - 2 * s
            for left in range(max(0, t - d), min(c, t) + 1):
                right = t - left
                total += (comb(p, s) * comb(t, left)
                          * (factorial(c) // factorial(c - left))
                          * (factorial(d) // factorial(d - right))
                          * clique(c - left) * clique(d - right))
        return total

    counts = [0] * (b + 7)
    cover = {'A:' + str(u): comb(6, u) * 2 ** u for u in range(7)}
    cover.update({'B:1': 2 * b, 'B:2': b * b})
    for u in range(0, 7, 2):
        counts[b + 6 - u // 2] += cover['A:' + str(u)] * perfect(6 - u, u, b, b)
    counts[b + 5] += b * b * perfect(6, 0, b - 1, b - 1)
    return counts, cover


def independent_sets(rows):
    stack = [((1 << len(rows)) - 1, 0)]
    while stack:
        available, chosen = stack.pop()
        if available == 0:
            yield chosen
            continue
        bit = available & -available
        rest = available ^ bit
        stack.append((rest, chosen))
        stack.append((rest & ~rows[bit.bit_length() - 1], chosen | bit))


def labeled_pivot(rows, b):
    # This computation uses neither formula() nor its cover multiplicities.
    pairs = [0] * (b + 1)
    pairs[0] = 1
    for size in range(2, b + 1, 2):
        pairs[size] = (size - 1) * pairs[size - 2]

    @cache
    def h(p, q, c, d):
        if (2 * p + q + c + d) % 2:
            return 0
        if p:
            return (h(p - 1, q, c, d)
                    + (c * h(p - 1, q + 1, c - 1, d) if c else 0)
                    + (d * h(p - 1, q + 1, c, d - 1) if d else 0))
        if q:
            return ((c * h(0, q - 1, c - 1, d) if c else 0)
                    + (d * h(0, q - 1, c, d - 1) if d else 0))
        return pairs[c] * pairs[d]

    full = (1 << len(rows)) - 1
    a = (1 << 12) - 1
    left = ((1 << b) - 1) << 12
    right = ((1 << b) - 1) << (12 + b)
    counts = [0] * (len(rows) // 2 + 1)
    cover = dict.fromkeys(['A:' + str(u) for u in range(7)] + ['B:1', 'B:2'], 0)
    for uncovered in independent_sets(rows):
        u = uncovered.bit_count()
        key = ('A:' if uncovered & ~a == 0 else 'B:') + str(u)
        require(key in cover, 'unexpected independent set')
        cover[key] += 1
        if u % 2:
            continue
        remaining = full ^ uncovered
        ar = remaining & a
        twice_p = sum((rows[v] & ar).bit_count() for v in range(12) if ar >> v & 1)
        p = twice_p // 2
        counts[remaining.bit_count() // 2] += h(p, ar.bit_count() - 2 * p,
                                               (remaining & left).bit_count(),
                                               (remaining & right).bit_count())
    return counts, cover


def generic(rows):
    # Small-graph baseline: actual vertex masks, no residual-state formula.
    @cache
    def perfect(mask):
        if not mask:
            return 1
        if mask.bit_count() % 2:
            return 0
        bit = mask & -mask
        rest = mask ^ bit
        neighbors = rows[bit.bit_length() - 1] & rest
        total = 0
        while neighbors:
            partner = neighbors & -neighbors
            neighbors ^= partner
            total += perfect(rest ^ partner)
        return total

    counts = [0] * (len(rows) // 2 + 1)
    full = (1 << len(rows)) - 1
    # Different independent-set enumeration: unique increasing extensions.
    def extend(start, chosen):
        rest = full ^ chosen
        if rest.bit_count() % 2 == 0:
            counts[rest.bit_count() // 2] += perfect(rest)
        for v in range(start, len(rows)):
            if not rows[v] & chosen:
                extend(v + 1, chosen | (1 << v))
    extend(0, 0)
    return counts


def verify(data, method):
    require(set(data) == {'n', 'adjacency', 'coefficients', 'cover'}, 'schema')
    require(data['n'] == 76, 'order')
    rows = [int(x, 16) for x in data['adjacency']]
    require(rows == graph(32), 'graph')
    actual, cover = formula(32) if method == 'formula' else labeled_pivot(rows, 32)
    require({k: str(v) for k, v in cover.items()} == data['cover'], 'cover')
    require([str(v) for v in actual] == data['coefficients'], 'coefficients')
    require(actual[36] ** 2 < actual[35] * actual[37], 'inequality')
    return actual


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'duplicate JSON key')
        result[key] = value
    return result


def main():
    data = json.loads((Path(__file__).resolve().parents[1] / 'data/graph.json').read_text(),
                      object_pairs_hook=unique_object)
    for method in ('formula', 'pivot'):
        counts = verify(data, method)
        for field in ('graph', 'coefficients', 'cover'):
            damaged = copy.deepcopy(data)
            if field == 'graph':
                damaged['adjacency'][0] = format(int(damaged['adjacency'][0], 16) ^ 2, 'x')
            elif field == 'coefficients':
                damaged['coefficients'][36] = str(int(damaged['coefficients'][36]) + 1)
            else:
                damaged['cover']['A:3'] = str(int(damaged['cover']['A:3']) - 1)
            try:
                verify(damaged, method)
            except ValueError as error:
                require(str(error) == field, 'unexpected corruption rejection')
            else:
                raise ValueError('corruption accepted')
    for b in (2, 4):
        rows = graph(b)
        expected = generic(rows)
        require(formula(b)[0] == expected == labeled_pivot(rows, b)[0], 'small graph')
    for rows, expected in (([2, 1], [0, 1]), ([2, 5, 10, 4], [0, 1, 1]),
                           ([14, 13, 11, 7], [0, 0, 3]),
                           ([28, 28, 3, 3, 3], [0, 0, 6])):
        require(generic(rows) == expected, 'known polynomial')
    print('PASS: graph, all coefficients, full independent-set cover, and strict inequality.')
    print('PASS: two counting methods, small graphs, and six corruption rejections.')
    for k, value in enumerate(counts):
        if value:
            print(f'm_{k} = {value}')


if __name__ == '__main__':
    main()
