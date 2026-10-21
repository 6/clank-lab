#!/usr/bin/env python3
"""Check that a DIMACS file handed to the proof checker is exactly the
intended formula: the clauses of the base CNF, plus the clauses of each
listed clause file, plus one unit clause per cube literal, and nothing else
(compared as multisets of clauses, literal order ignored).  Written apart
from cnc.py's merge.

usage: check_inputs.py MERGED BASE_CNF [--add FILE]... [--units "l1 l2 ..."]
                       [--negcubes CUBEFILE]
  --negcubes adds, for each cube line, the one clause of its negated literals.
"""
import sys
from collections import Counter

def clauses(path):
    out, cur, header = [], [], None
    with open(path) as f:
        for line in f:
            if line.startswith('c'):
                continue
            if line.startswith('p'):
                header = line.split()
                continue
            for t in line.split():
                v = int(t)
                if v == 0:
                    out.append(tuple(sorted(cur))); cur = []
                else:
                    cur.append(v)
    if cur:
        sys.exit(f'{path}: unterminated clause')
    return out, header

def main():
    a = sys.argv[1:]
    merged, base = a[0], a[1]
    want = Counter(clauses(base)[0])
    i = 2
    while i < len(a):
        if a[i] == '--add':
            want.update(clauses(a[i + 1])[0]); i += 2
        elif a[i] == '--units':
            want.update((int(t),) for t in a[i + 1].split()); i += 2
        elif a[i] == '--negcubes':
            for line in open(a[i + 1]):
                lits = [int(t) for t in line.split()]
                assert lits and lits[-1] == 0
                want[tuple(sorted(-l for l in lits[:-1]))] += 1
            i += 2
        else:
            sys.exit(f'unknown argument {a[i]}')
    got, header = clauses(merged)
    if Counter(got) != want:
        extra = Counter(got) - want
        missing = want - Counter(got)
        sys.exit(f'MISMATCH: {sum(extra.values())} extra clauses (e.g. {next(iter(extra), None)}), '
                 f'{sum(missing.values())} missing (e.g. {next(iter(missing), None)})')
    if header is None or int(header[3]) != len(got):
        sys.exit('header clause count wrong')
    print(f'check_inputs: {merged} is exactly the intended {len(got)} clauses')

if __name__ == '__main__':
    main()
