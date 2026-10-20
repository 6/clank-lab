"""Check a line-free set in {1,2,3}^n: distinct points, no combinatorial line.

usage: check_witness.py FILE n K   (passes iff >= K points and line-free)
"""
import itertools
import sys


def main():
    path, n, K = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    pts = [l.strip() for l in open(path) if l.strip() and not l.startswith('#')]
    if any(len(p) != n or set(p) - set('123') for p in pts):
        raise SystemExit('FAIL malformed point')
    s = set(pts)
    if len(s) != len(pts):
        raise SystemExit('FAIL repeated point')
    nlines = 0
    for w in itertools.product('123*', repeat=n):
        if '*' not in w:
            continue
        nlines += 1
        if all(''.join(v if c == '*' else c for c in w) in s for v in '123'):
            raise SystemExit('FAIL line inside: ' + ''.join(w))
    if nlines != 4 ** n - 3 ** n:
        raise SystemExit('FAIL line count')
    if len(s) < K:
        raise SystemExit('FAIL only %d points' % len(s))
    print('PASS %d points, %d lines checked, none inside' % (len(s), nlines))


if __name__ == '__main__':
    main()
