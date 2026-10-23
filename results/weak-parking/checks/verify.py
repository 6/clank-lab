#!/usr/bin/env python3
"""Verify the complete weak-parking certificates and rejection controls."""
import argparse
import concurrent.futures
import copy
import gzip
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

import crosschecks
import replay
import structure

ROOT = Path(__file__).resolve().parent.parent
# The two most expensive steps occupy separate parts. Each full GAP checker
# is an indivisible check, including its own exhaustive cover verification.
STEPS = (
    ('primary E8', 'primary', 8),
    ('independent E8', 'independent', 8),
    ('primary E7', 'primary', 7),
    ('independent E7', 'independent', 7),
    ('primary E6', 'primary', 6),
    ('independent E6', 'independent', 6),
    ('both checkers reject both corruptions', 'corruptions', None),
    ('exact spectral and q-Catalan crosschecks', 'crosschecks', None),
)


def independent(data, certificate):
    return subprocess.run(
        [sys.executable, str(ROOT/'checks/independent.py'), str(data), str(certificate)],
        text=True, capture_output=True)


def corruptions(folder):
    replay.mutations(folder)
    data, cert = replay.read_pair(folder, 6)
    messages = []
    with tempfile.TemporaryDirectory(prefix='weak-parking-corruptions-') as tmp:
        for kind in ('character', 'cover'):
            bad_d, bad_c = copy.deepcopy(data), copy.deepcopy(cert)
            if kind == 'character':
                bad_d['character'][0][0] += 1
                expected = 'spectral character mismatch'
            else:
                bad_d['nc_count'] -= 1
                bad_c['parents'].pop()
                expected = 'descending NC cover gap'
            dp, cp = Path(tmp)/'data.json', Path(tmp)/'certificate.json.gz'
            dp.write_text(json.dumps(bad_d))
            cp.write_bytes(gzip.compress(json.dumps(bad_c).encode(), mtime=0))
            result = independent(dp, cp)
            if not result.returncode or expected not in result.stdout + result.stderr:
                raise RuntimeError('independent corruption did not fail as intended: ' + kind)
            messages.append('BOTH CHECKERS REJECT ' + kind)
    return '\n'.join(messages) + '\n'


def run_step(step, folder):
    name, kind, rank = step
    if kind == 'primary':
        return replay.check(folder, rank)['log']
    if kind == 'independent':
        data = folder/f'e{rank}-result.json'
        cert = folder/f'e{rank}-result.json.certificate.json.gz'
        result = independent(data, cert)
        if result.returncode:
            raise RuntimeError(result.stdout + result.stderr)
        return result.stdout
    if kind == 'corruptions':
        return corruptions(folder)
    output = []
    for n in (6, 7, 8):
        data, cert = replay.read_pair(folder, n)
        replay.spectral(data)
        fields = structure.check(data, cert)
        output.append('STRUCTURE AND SPECTRAL ' + json.dumps(fields))
        output.append('CYCLIC CATALAN CROSSCHECK ' + json.dumps(crosschecks.check(folder, n)))
    return '\n'.join(output) + '\n'


def part(value):
    try:
        number, total = map(int, value.split('/'))
        if not 1 <= number <= total <= len(STEPS):
            raise ValueError
        return number, total
    except ValueError:
        raise argparse.ArgumentTypeError('part must be K/N with 1 <= K <= N <= 8') from None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--data', type=Path, default=ROOT/'data')
    parser.add_argument('--part', type=part, help='run part K/N; K starts at 1')
    parser.add_argument('--list', action='store_true', help='list the selected steps without running')
    parser.add_argument('--workers', type=int, default=3, help='concurrent steps (default: 3)')
    args = parser.parse_args()
    if args.workers < 1:
        parser.error('--workers must be positive')
    selected = list(enumerate(STEPS))
    if args.part:
        number, total = args.part
        selected = [(i, step) for i, step in selected if i % total == number - 1]
    if args.list:
        for i, step in selected:
            print(f'{i + 1}: {step[0]}')
        return
    if shutil.which('gap') is None:
        parser.error('GAP is required; install gap-core, gap-libs, gap-smallgrp and gap-transgrp')
    with concurrent.futures.ThreadPoolExecutor(max_workers=min(args.workers, len(selected))) as pool:
        futures = {pool.submit(run_step, step, args.data.resolve()): step[0]
                   for _, step in selected}
        for future in concurrent.futures.as_completed(futures):
            print(future.result(), end='', flush=True)
    if args.part and args.part[1] > 1:
        print(f'PASS weak parking certificate verification part {args.part[0]}/{args.part[1]}')
    else:
        print('PASS weak parking full certificate replay: E7 1080; E8 3360; E6 300')


if __name__ == '__main__':
    main()
