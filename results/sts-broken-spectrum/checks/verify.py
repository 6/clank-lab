"""Run every check of the result. Run from the result's folder:

    python3 -I checks/verify.py

It needs Python 3.9 or later (standard library only) and a C compiler,
`cc` or the one named by the CC environment variable, to build DRAT-trim.
It exits with status 0 only if every check and every corruption test
behaves as expected.
"""
import json
import os
import shutil
import subprocess
import sys
import tempfile
from itertools import combinations, product

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
sys.dont_write_bytecode = True

import check_design  # noqa: E402
import strict_cnf  # noqa: E402

PY = sys.executable
# Paths relative to the result's folder, where every command runs.
DATA = 'data/sts39.json'
CNF = 'data/strict4.cnf'
DRAT = 'data/strict4.drat'


def run(cmd):
    p = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
    return p.returncode, (p.stdout + p.stderr).replace('\r', '\n')


def expect_ok(label, cmd, success_line=None):
    code, out = run(cmd)
    lines = [l.strip() for l in out.splitlines()]
    if code != 0 or (success_line and success_line not in lines):
        print(out)
        sys.exit(f'FAIL: {label}')
    for line in lines:
        if line.startswith('OK:'):
            print(line)
    print(f'OK: {label}')


def expect_reject(label, cmd, reject_line):
    code, out = run(cmd)
    lines = [l.strip() for l in out.splitlines()]
    if code != 1 or not any(l.startswith(reject_line) for l in lines):
        print(out)
        sys.exit(f'FAIL: corruption not rejected: {label}')
    print(f'OK: rejected {label}')


def fano():
    # Points 1..7 are the nonzero vectors of GF(2)^3; x, y, x XOR y is a line.
    return sorted({tuple(sorted((x - 1, y - 1, (x ^ y) - 1)))
                   for x in range(1, 8) for y in range(x + 1, 8)})


def affine_plane_3():
    # Points (i, j) of Z_3^2 as 3i + j; lines are {p, p + d, p + 2d}.
    lines = set()
    for i, j in product(range(3), repeat=2):
        for di, dj in ((0, 1), (1, 0), (1, 1), (1, 2)):
            pts = [((i + t * di) % 3) * 3 + (j + t * dj) % 3 for t in range(3)]
            lines.add(tuple(sorted(pts)))
    return sorted(lines)


def set_partitions(n):
    # Restricted growth strings: each set partition of 0..n-1 exactly once.
    def extend(prefix, top):
        if len(prefix) == n:
            yield prefix
            return
        for c in range(top + 2):
            yield from extend(prefix + [c], max(top, c))
    yield from extend([0], 0)


def feasible_set(v, blocks):
    return sorted({max(f) + 1 for f in set_partitions(v)
                   if all(len({f[x] for x in b}) == 2 for b in blocks)})


def satisfies(clauses, k, coloring):
    true = {strict_cnf.var(k, x, c) for x, c in enumerate(coloring)}
    return all(any((l > 0) == (abs(l) in true) for l in clause)
               for clause in clauses)


def calibrate():
    for name, blocks, v in (('Fano plane', fano(), 7),
                            ('affine plane of order 3', affine_plane_3(), 9)):
        check_design.check_sts(v, [list(b) for b in blocks])
        omega = feasible_set(v, blocks)
        if omega != [3]:
            sys.exit(f'FAIL: feasible set of the {name} is {omega}, not [3]')
        print(f'OK: the {name} has feasible set {{3}}, by listing all set partitions')
    blocks = fano()
    for k in (2, 3, 4):
        _, clauses = strict_cnf.strict_cnf(7, blocks, k)
        for coloring in product(range(k), repeat=7):
            strict = (set(coloring) == set(range(k)) and
                      all(len({coloring[x] for x in b}) == 2 for b in blocks))
            if satisfies(clauses, k, coloring) != strict:
                sys.exit(f'FAIL: strict {k}-bicoloring formula of the Fano plane '
                         f'disagrees with the definition at {coloring}')
    print('OK: on the Fano plane, the strict k-bicoloring formulas for k = 2, 3, 4 '
          'hold exactly at the strict k-bicolorings')


def main():
    work = tempfile.mkdtemp()
    try:
        cc = os.environ.get('CC', 'cc')
        dt = os.path.join(work, 'drat-trim')
        subprocess.run([cc, '-O2', '-o', dt, os.path.join(HERE, 'drat-trim.c')],
                       check=True, capture_output=True)

        calibrate()
        expect_ok('the design and both bicolorings satisfy the definitions',
                  [PY, '-I', 'checks/check_design.py', DATA])
        expect_ok('the CNF in data/ is the strict 4-bicoloring formula of this design',
                  [PY, '-I', 'checks/strict_cnf.py', '4', DATA, '--compare', CNF])
        expect_ok('DRAT-trim verifies the refutation of the strict 4-bicoloring formula',
                  [dt, CNF, DRAT], 's VERIFIED')
        expect_ok('the unit-propagation checker verifies the same refutation',
                  [PY, '-I', 'checks/rup_check.py', CNF, DRAT], 's VERIFIED')

        with open(os.path.join(ROOT, DATA)) as f:
            data = json.load(f)

        def corrupt(label, change):
            bad = json.loads(json.dumps(data))
            change(bad)
            path = os.path.join(work, 'bad.json')
            with open(path, 'w') as f:
                json.dump(bad, f)
            expect_reject(label, [PY, '-I', 'checks/check_design.py', path], 'REJECT:')

        def move_point(d):
            # Replace one point of a block by another: some pair now lies in
            # two blocks and another in none.
            b = d['blocks'][0]
            b[2] = next(x for x in range(d['points']) if x not in b)

        def recolor(key, color):
            def change(d):
                d[key][0] = color
            return change

        corrupt('a design with a pair in two blocks', move_point)
        corrupt('a design with a block removed', lambda d: d['blocks'].pop())
        c3 = data['coloring3']
        for color in range(3):
            if color != c3[0]:
                corrupt(f'the 3-bicoloring with point 0 recolored {color}',
                        recolor('coloring3', color))
        corrupt('a 5-bicoloring that misses a color',
                lambda d: d.__setitem__('coloring5', [min(c, 3) for c in d['coloring5']]))
        corrupt('a rainbow 3-coloring of a block',
                lambda d: d.__setitem__('coloring3', [0, 1, 2] + [0] * 36))

        with open(os.path.join(ROOT, CNF)) as f:
            lines = f.read().splitlines()
        bad_cnf = os.path.join(work, 'bad.cnf')
        with open(bad_cnf, 'w') as f:
            f.write('\n'.join(lines[:-1] + [lines[-1].replace('-', '', 1)]) + '\n')
        expect_reject('a CNF with one literal changed',
                      [PY, '-I', 'checks/strict_cnf.py', '4', DATA, '--compare', bad_cnf],
                      'REJECT:')

        with open(os.path.join(ROOT, DRAT)) as f:
            proof = f.read().splitlines()
        empty = os.path.join(work, 'empty.drat')
        with open(empty, 'w') as f:
            f.write('0\n')
        half = os.path.join(work, 'half.drat')
        with open(half, 'w') as f:
            f.write('\n'.join(proof[:len(proof) // 2]) + '\n')
        sat5 = os.path.join(work, 'strict5.cnf')
        with open(sat5, 'w') as f:
            subprocess.run([PY, '-I', 'checks/strict_cnf.py', '5', DATA],
                           cwd=ROOT, stdout=f, check=True)
        for label, formula, cert in (
                ('a proof that is only the empty clause', CNF, empty),
                ('the first half of the proof', CNF, half),
                ('the proof against the satisfiable strict 5-bicoloring formula',
                 sat5, DRAT)):
            expect_reject(f'{label} (DRAT-trim)', [dt, formula, cert], 's NOT VERIFIED')
            expect_reject(f'{label} (unit-propagation checker)',
                          [PY, '-I', 'checks/rup_check.py', formula, cert],
                          's NOT VERIFIED')
    finally:
        shutil.rmtree(work)
    print('All checks passed: the Steiner triple system has strict 3- and '
          '5-bicolorings and no strict 4-bicoloring.')


if __name__ == '__main__':
    main()
