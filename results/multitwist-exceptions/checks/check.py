#!/usr/bin/env python3
"""Check the finite facts F0-F4 of the paper with both independent checkers.

Usage, from the folder holding checks/ and data/:

    python3 checks/check.py

Checker A (check_free_group.py) works in the free group pi_1 = F_4 with the
Artin action; checker B (check_dynnikov.py), written separately from the
paper's statement alone, works with Dynnikov coordinates of curves in the
four-punctured disc. Both must accept F0-F4 for k = 1..30 and both signs,
and both must reject the four corruptions K1-K4 (a crash does not count as a
rejection: each run must end with its JSON verdict line). Checker B also runs
with every twist reversed. Standard library only. Exit status 0 means
everything passed.
"""
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
DATA = HERE.parent / 'data'
A = HERE / 'check_free_group.py'
B = HERE / 'check_dynnikov.py'
KMAX = '30'
CORRUPTIONS = {
    'K1': 'K1-C-moved.json',
    'K2': 'K2-Cprime-moved.json',
    'K3': 'K3-C-Cprime-swapped.json',
    'K4': 'K4-c-moved.json',
}


def run(args):
    """Run a checker; return (exit status, parsed JSON verdict line or None)."""
    proc = subprocess.run([sys.executable, '-I'] + [str(a) for a in args],
                          capture_output=True, text=True, timeout=600)
    verdict = None
    for line in reversed(proc.stdout.strip().splitlines()):
        try:
            verdict = json.loads(line)
            break
        except ValueError:
            continue
    return proc.returncode, verdict


def expect(label, args, accept, failures):
    code, verdict = run(args)
    want = 'ACCEPT' if accept else 'REJECT'
    ok = (verdict is not None and verdict.get('verdict') == want
          and code == (0 if accept else 1)
          and (verdict.get('failures', 0) == 0) == accept)
    detail = (f"{verdict['checks']} checks, {verdict['failures']} failures"
              if verdict else 'no verdict line')
    print(f"{'ok  ' if ok else 'FAIL'} {label}: {want if ok else 'unexpected'} ({detail})")
    if not ok:
        failures.append(label)


def main():
    failures = []
    expect('checker A, F0-F4 for k <= 30', [A, '--kmax', KMAX, '--quiet'], True, failures)
    expect('checker B, F0-F4 for k <= 30', [B, '--kmax', KMAX], True, failures)
    expect('checker B, all twists reversed', [B, '--kmax', KMAX, '--mirror'], True, failures)
    for name, path in CORRUPTIONS.items():
        expect(f'checker A, corruption {name}',
               [A, '--kmax', '6', '--quiet', '--curves', DATA / 'corrupt' / path], False, failures)
        expect(f'checker B, corruption {name}', [B, '--kmax', '6', '--corrupt', name],
               False, failures)
    if failures:
        print(f'FAILED: {len(failures)} of the expected outcomes did not occur')
        return 1
    print('PASS: both checkers accept F0-F4 and reject every corruption')
    return 0


if __name__ == '__main__':
    sys.exit(main())
