"""Build the CNF formula of strict k-bicolorings of a triple system.

Usage: python3 checks/strict_cnf.py K [data/sts39.json] [--compare FILE.cnf]

The Boolean variable 1 + K*x + c (point x, color c in 0..K-1) means that
point x has color c. The clauses say:
  * each point has at least one color, and no two colors;
  * each color is used by some point;
  * for each block {x, y, z} and each assignment (a, b, c) of colors to
    x, y, z that gives the block one color or three colors, the clause
    (not x=a) or (not y=b) or (not z=c).
The satisfying assignments are therefore exactly the strict K-bicolorings.
The block clauses are produced by listing all K^3 color assignments, not by
a formula for them.

Without --compare the CNF is printed in DIMACS format. With --compare the
script checks that FILE.cnf has the same header and the same multiset of
clauses (each clause read as a set of literals), and exits with status 1
and a REJECT: line otherwise.
"""
import json
import sys
from collections import Counter
from itertools import combinations, product


def var(k, x, c):
    return 1 + k * x + c


def strict_cnf(v, blocks, k):
    clauses = []
    for x in range(v):
        lits = [var(k, x, c) for c in range(k)]
        clauses.append(lits)
        clauses.extend([-a, -b] for a, b in combinations(lits, 2))
    for c in range(k):
        clauses.append([var(k, x, c) for x in range(v)])
    for block in blocks:
        for colors in product(range(k), repeat=3):
            if len(set(colors)) != 2:
                clauses.append([-var(k, x, c) for x, c in zip(block, colors)])
    return v * k, clauses


def read_dimacs(path):
    header, clauses, current = None, [], []
    with open(path) as f:
        for line in f:
            words = line.split()
            if not words or words[0] == 'c':
                continue
            if words[0] == 'p':
                if header is not None or len(words) != 4 or words[1] != 'cnf':
                    raise ValueError('bad DIMACS header')
                header = (int(words[2]), int(words[3]))
                continue
            for w in words:
                lit = int(w)
                if lit == 0:
                    clauses.append(current)
                    current = []
                else:
                    current.append(lit)
    if header is None or current:
        raise ValueError('missing header or unterminated clause')
    return header, clauses


def key(clause):
    return tuple(sorted(set(clause)))


def main(argv):
    args = [a for a in argv[1:] if a != '--compare']
    compare = None
    if '--compare' in argv:
        compare = argv[argv.index('--compare') + 1]
        args.remove(compare)
    k = int(args[0])
    path = args[1] if len(args) > 1 else 'data/sts39.json'
    with open(path) as f:
        data = json.load(f)
    nvars, clauses = strict_cnf(data['points'], data['blocks'], k)
    if compare is None:
        print(f'p cnf {nvars} {len(clauses)}')
        for clause in clauses:
            print(' '.join(map(str, clause)), 0)
        return 0
    try:
        header, theirs = read_dimacs(compare)
    except ValueError as e:
        print(f'REJECT: {compare}: {e}')
        return 1
    if header != (nvars, len(clauses)) or len(theirs) != len(clauses):
        print(f'REJECT: {compare} has header {header}, expected {(nvars, len(clauses))}')
        return 1
    if any(len(set(c)) != len(c) for c in theirs):
        print(f'REJECT: {compare} has a clause with a repeated literal')
        return 1
    if Counter(map(key, theirs)) != Counter(map(key, clauses)):
        print(f'REJECT: {compare} differs from the strict {k}-bicoloring formula')
        return 1
    print(f'OK: {compare} is the strict {k}-bicoloring formula '
          f'({nvars} variables, {len(clauses)} clauses)')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
