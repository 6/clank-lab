#!/usr/bin/env python3
"""Exact degree-polynomial crosscheck of cyclic orbit counts."""
import gzip
import json
import math
from pathlib import Path
import sympy as s

ROOT = Path(__file__).resolve().parent.parent
DEGREES = {6: [2, 5, 6, 8, 9, 12], 7: [2, 6, 8, 10, 12, 14, 18],
           8: [2, 8, 12, 14, 18, 20, 24, 30]}


def check(folder, n):
    d = json.loads((folder / f'e{n}-result.json').read_text())
    c = json.loads(gzip.decompress((folder / f'e{n}-result.json.certificate.json.gz').read_bytes()))
    h = d['h']
    q = s.Symbol('q')
    cat = s.Poly(s.cancel(s.prod(1-q**(h+k) for k in DEGREES[n]) /
                         s.prod(1-q**k for k in DEGREES[n])), q)
    counts = []
    for exponent in range(h):
        fixed = sum(length for _, length in c['orbits'] if exponent % length == 0)
        factor = s.Poly(s.cyclotomic_poly(h // math.gcd(h, exponent), q), q)
        assert cat.rem(factor) == s.Poly(fixed, q), (n, exponent)
        counts.append(fixed)
    identity = next(i for i, m in enumerate(d['class_matrices'])
                    if m == [[int(i == j) for j in range(n)] for i in range(n)])
    assert d['character'][identity][0] == (h+1)**n
    assert counts[0] == d['nc_count']
    return {'rank': n, 'nc_count': counts[0], 'cyclic_fixed_counts': counts,
            'parking_cardinality': (h+1)**n, 'status': 'PASS'}


if __name__ == '__main__':
    print(json.dumps([check(ROOT/'data', n) for n in [6, 7, 8]], indent=2))
