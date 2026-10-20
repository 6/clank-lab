"""Own check of the lower-bound witness: a line-free subset of [3]^7 with 1302 points.

  python3 check_witness_fresh.py WITNESS [n] [size]

Reads the points (one word over {1,2,3} per line, '#' comments), requires
them to be distinct words of length n, counts them, and tests every
combinatorial line (a word over {1,2,3,*} with at least one *; 4^n - 3^n
of them) for having all three points in the set.  Also reports the
multiset of cell types (#1s, #2s, #3s) the points fall into.
"""
import itertools
import sys
from collections import Counter


def main():
    path = sys.argv[1]
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 7
    size = int(sys.argv[3]) if len(sys.argv) > 3 else 1302
    pts = [ln.strip() for ln in open(path) if ln.strip() and not ln.startswith('#')]
    assert all(len(p) == n and set(p) <= set('123') for p in pts), 'malformed point'
    A = set(pts)
    assert len(A) == len(pts), 'repeated point'
    lines = inside = 0
    for w in itertools.product('123*', repeat=n):
        if '*' not in w:
            continue
        lines += 1
        if all(''.join(v if c == '*' else c for c in w) in A for v in '123'):
            inside += 1
    cells = Counter((p.count('1'), p.count('2'), p.count('3')) for p in A)
    ok = len(A) == size and lines == 4 ** n - 3 ** n and inside == 0
    print('%s %d points, %d lines checked, %d inside; cells %s' % (
        'PASS' if ok else 'FAIL', len(A), lines, inside,
        ' '.join('%d%d%d:%d' % (k + (v,)) for k, v in sorted(cells.items()))))
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
