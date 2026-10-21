#!/usr/bin/env python3
"""Check the counterexample certificates with both independent checkers.

Usage, from the folder holding checks/ and data/:

    python3 checks/check.py

Both checkers must accept both witnesses, and must reject every corrupted
certificate in data/corrupt/ and the agreeing control, each for its intended
reason (a crash does not count as a rejection). A third, separately written
checker then recomputes every case with n <= 5 and confirms that the
counterexample is the smallest. Standard library only.
Exit status 0 means everything passed.
"""
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
DATA = HERE.parent / 'data'
CHECKERS = {
    'A': HERE / 'check_snf.py',
    'B': HERE / 'check_mod2.py',
}
WITNESSES = ['witness-311-k3.json', 'witness-52-k7.json']
# Each rejected input, with the reason each checker must give.
REJECTED = {
    'control-51-k5.json': ('no discrepancy: snf equals the prediction',
                           'no mod-2 discrepancy with Conjecture 7.4'),
    'corrupt/A-entry.json': ('column 3 of A is not X_k e_T',
                             'X_k e_T3 != sum_i A[i][3] e_Ti'),
    'corrupt/U-not-unimodular.json': ('U or V not unimodular',
                                      'U or V is not unimodular'),
    'corrupt/U-rational.json': ('U is not an f x f integer matrix',
                                'A, U, V must be f x f integer matrices'),
    'corrupt/basis-nonstandard.json': ('basis is not the set of SYT',
                                       'recorded basis is not the set of SYT'),
    'corrupt/prediction-altered.json': ('recorded prediction differs from the recomputed one',
                                        'recorded prediction differs from the recomputed one'),
    'corrupt/snf-claims-prediction.json': ('U A V != diag(snf)', 'U A V != diag(snf)'),
    'corrupt/snf-extra-zero.json': ('snf is not a list of f integers', 'snf must be f integers'),
}


def run(checker, name):
    proc = subprocess.run([sys.executable, str(CHECKERS[checker]), str(DATA / name)],
                          capture_output=True, text=True, timeout=600)
    return proc.returncode, proc.stdout.strip()


def main():
    failures = []
    listed = {p.relative_to(DATA).as_posix() for p in (DATA / 'corrupt').glob('*.json')}
    unlisted = listed - set(REJECTED)
    if unlisted:
        failures.append('corruptions without an expected reason: ' + ', '.join(sorted(unlisted)))
    for name in WITNESSES:
        for checker in CHECKERS:
            code, out = run(checker, name)
            print(f'checker {checker} {name}: {out}')
            if code != 0 or not out.startswith('ACCEPT '):
                failures.append(f'checker {checker} did not accept {name}')
    for name, reasons in REJECTED.items():
        for checker, reason in zip(CHECKERS, reasons):
            code, out = run(checker, name)
            print(f'checker {checker} {name}: {out}')
            if code == 0 or out != 'REJECT: ' + reason:
                failures.append(f'checker {checker} did not reject {name} as "{reason}"')
    proc = subprocess.run([sys.executable, str(HERE / 'check_small.py')],
                          capture_output=True, text=True, timeout=600)
    out = proc.stdout.strip()
    print(f'checker C n <= 5: {out}')
    if proc.returncode != 0 or not out.startswith('ACCEPT '):
        failures.append('checker C did not confirm the cases with n <= 5')
    if failures:
        for failure in failures:
            print('FAIL', failure)
        return 1
    print(f'PASS both checkers accept both witnesses and reject the agreeing control '
          f'and all {len(REJECTED) - 1} corruptions; every case with n <= 5 confirmed')
    return 0


if __name__ == '__main__':
    sys.exit(main())
