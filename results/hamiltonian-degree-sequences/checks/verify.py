#!/usr/bin/env python3
"""Check the counterexamples and the small cases, from the bundle alone.

Usage, from the bundle's top folder:
  python3 checks/verify.py          witnesses, family, rejected inputs, n <= 5
  python3 checks/verify.py --n6     the same, plus the exhaustive search at n = 6

Steps:
1. Two independent checkers (check_a.py in Python, check_b.c in C) confirm that
   data/G6.txt, data/G7.txt and the family F(n-4,4) (8 <= n <= 18 in check_a,
   8 <= n <= 14 in check_b) are strongly connected, satisfy conditions (i) and
   (ii), and have no Hamilton cycle; check_a also confirms condition (iii) for
   G7 and the family.
2. Four altered witnesses must be rejected by both checkers: two gain a Hamilton
   cycle, one loses condition (ii), one has a loop.
3. Two independent enumerators (enum_a.c, enum_b.c) visit every digraph on
   n = 3, 4, 5 (and 6 with --n6) vertices and must print the expected counts.

Needs Python 3.10 or later and a C compiler (cc). Exit status 0 means every
check passed.
"""
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
G6 = Path('data/G6.txt')
G7 = Path('data/G7.txt')

EXPECTED = {
    3: 'n=3 digraphs=64 nw_hypothesis=7 nw_counterexamples=0 kot6_counterexamples=0',
    4: 'n=4 digraphs=4096 nw_hypothesis=186 nw_counterexamples=0 kot6_counterexamples=0',
    5: 'n=5 digraphs=1048576 nw_hypothesis=40140 nw_counterexamples=0 kot6_counterexamples=0',
    6: 'n=6 digraphs=1073741824 nw_hypothesis=44387496 nw_counterexamples=1080 kot6_counterexamples=0',
}

# (name, base witness, line replaced, replacement, why it must be rejected)
ALTERED = [
    ('G6 plus 2->3', G6, '2: 1 5', '2: 1 3 5', 'Hamiltonian'),
    ('G6 minus 4->3', G6, '4: 0 1 3 5', '4: 0 1 5', 'condition (ii) fails'),
    ('G7 plus 0->2', G7, '0: 1 4', '0: 1 2 4', 'Hamiltonian'),
    ('G6 with a loop at 0', G6, '0: 1 2 3 4 5', '0: 0 1 2 3 4 5', 'not a digraph'),
]


def run(cmd):
    shown = [Path(c).name if Path(str(c)).is_absolute() else str(c) for c in cmd]
    print('$ ' + ' '.join(shown), flush=True)
    return subprocess.run([str(c) for c in cmd], capture_output=True, text=True, cwd=ROOT)


def main(argv):
    full = '--n6' in argv
    work = Path(tempfile.mkdtemp())
    failures = []

    binaries = {}
    for name in ('check_b', 'enum_a', 'enum_b'):
        out = work / name
        r = run(['cc', '-O2', '-o', out, f'checks/{name}.c'])
        if r.returncode:
            print(r.stderr)
            return 1
        binaries[name] = out
    python = [sys.executable, '-I', '-B', 'checks/check_a.py']

    print('== witnesses and the family F(n-4,4)')
    for cmd in (python + [G6, G7, '--family', 8, 18],
                [binaries['check_b'], G6, G7, '-f', 8, 14]):
        r = run(cmd)
        print(r.stdout.rstrip())
        if r.returncode:
            failures.append('a witness was rejected')
        if cmd[0] == sys.executable:
            # G7 and the family must also satisfy condition (iii) (None: n odd).
            for line in r.stdout.splitlines():
                if line.startswith(('data/G7.txt', 'F(')) and not (
                        'cond_iii=True' in line or 'cond_iii=None' in line):
                    failures.append('condition (iii) fails: ' + line.split()[0])

    print('== altered witnesses (each must be rejected by both checkers)')
    for name, base, old, new, why in ALTERED:
        lines = (ROOT / base).read_text().splitlines()
        if old not in lines:
            failures.append(f'{name}: line "{old}" not found')
            continue
        path = work / 'altered.txt'
        path.write_text('\n'.join(new if l == old else l for l in lines) + '\n')
        accepted = [label for label, cmd in (('check_a', python + [path]),
                                             ('check_b', [binaries['check_b'], path]))
                    if subprocess.run([str(c) for c in cmd], capture_output=True,
                                      cwd=ROOT).returncode == 0]
        if accepted:
            failures.append(f'{name} accepted by ' + ', '.join(accepted))
        print(f'{name} ({why}): ' + ('ACCEPTED by ' + ', '.join(accepted) if accepted
                                     else 'rejected by both checkers'))

    print('== exhaustive search over all digraphs')
    for n in range(3, 7 if full else 6):
        outputs = []
        for name in ('enum_a', 'enum_b'):
            r = run([binaries[name], n])
            outputs.append(r.stdout.strip())
            if r.returncode:
                failures.append(f'{name} {n} exited with {r.returncode}')
        print(outputs[0])
        if outputs[0] != outputs[1]:
            failures.append(f'the enumerators disagree at n = {n}: {outputs[1]}')
        if outputs[0] != EXPECTED[n]:
            failures.append(f'unexpected counts at n = {n}')
    if not full:
        print('(n = 6 not run: add --n6, about 2.5 CPU-minutes per enumerator)')

    for f in failures:
        print('FAIL: ' + f)
    print('FAIL' if failures else 'PASS')
    return 1 if failures else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
