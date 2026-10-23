#!/usr/bin/env python3
"""Reproduce the finite cover, exhaustion accounting, and controls."""
import argparse
import filecmp
import json
import lzma
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent.parent
STEPS = ['first-checker', 'second-checker', 'first-corruptions',
         'second-corruptions', 'published-counts', 'known-witnesses',
         'reduction-controls', 'discovery-controls']


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--part', help='one of eight independent CI parts, K/8')
    ap.add_argument('--list', action='store_true')
    ap.add_argument('--full-controls', action='store_true',
                    help='also rediscover order 55 and use unfiltered small-order baselines')
    ap.add_argument('--full-search', action='store_true', help='rerun all order-65 search units')
    ap.add_argument('--work', type=Path, help='new output directory to retain generated data')
    ap.add_argument('--threads', type=int, default=len(os.sched_getaffinity(0)))
    a = ap.parse_args()
    selected = STEPS
    if a.part:
        k, total = map(int, a.part.split('/'))
        if total != 8 or not 1 <= k <= 8:
            ap.error('--part must be K/8 with 1 <= K <= 8')
        selected = [STEPS[k-1]]
    if a.list:
        print('\n'.join(selected))
        return
    if a.threads < 1:
        ap.error('--threads must be positive')
    tmp = None
    if a.work:
        a.work.mkdir(parents=True, exist_ok=False)
        w = a.work.resolve()
    else:
        tmp = tempfile.TemporaryDirectory(prefix='williamson-check-')
        w = Path(tmp.name)
    env = dict(os.environ, OMP_NUM_THREADS=str(a.threads), OMP_DYNAMIC='FALSE')
    src = w/'src'
    shutil.copytree(ROOT/'checks', src)
    data = w/'data'; data.mkdir()
    receipts = w/'receipts'; receipts.mkdir()
    for name in ['classes65', 'units65']:
        (w/(name+'.tsv')).write_bytes(lzma.decompress((ROOT/'data'/(name+'.tsv.xz')).read_bytes()))
    for archive in sorted((ROOT/'data').glob('receipts-*.json.xz')):
        entries = json.loads(lzma.decompress(archive.read_bytes()))
        for name, value in entries.items():
            if Path(name).name != name or not isinstance(value, str):
                raise RuntimeError('invalid receipt container entry')
            path = receipts/name
            content = value.encode()
            if path.exists():
                if name != 'solutions.tsv':
                    raise RuntimeError('duplicate receipt batch')
                content = path.read_bytes()+content
            path.write_bytes(content)

    def run(args, output=None, reject=False):
        cmd = [str(x) for x in args]
        r = subprocess.run(cmd, env=env, cwd=src, text=True,
                           stdout=subprocess.PIPE if output is not None or reject else None,
                           stderr=subprocess.STDOUT if reject else None)
        if reject:
            if r.returncode != 1:
                raise RuntimeError('corruption must fail with validation exit status 1')
            print('PASS rejected planted cover gap', flush=True)
        elif r.returncode:
            raise subprocess.CalledProcessError(r.returncode, cmd)
        if output is not None:
            output.write_text(r.stdout)
        return r.stdout

    def py(name, *args, **kwargs):
        return run([sys.executable, '-I', src/name, *args], **kwargs)

    for name in ['rows', 'search', 'baseline']:
        run(['gcc', '-O3', '-fopenmp', '-o', src/name, src/(name+'.c'), '-lm'])
    first_ready = second_ready = False

    def first():
        nonlocal first_ready
        if first_ready:
            return
        run([src/'rows', 65, 5, '--cos'], output=w/'cos.txt')
        with (w/'cos.txt').open() as f:
            subprocess.run([sys.executable, '-I', src/'check_cos.py', '65'], stdin=f, env=env, check=True)
        run([src/'rows', 65, 5, data])
        py('units.py', 65, 5, data/'classes.tsv', data/'units.tsv')
        if (data/'units.tsv').read_bytes() != (w/'units65.tsv').read_bytes():
            raise RuntimeError('regenerated compressed cover differs')
        py('class_sha.py', data, output=w/'classes-generated.tsv')
        if (w/'classes-generated.tsv').read_bytes() != (w/'classes65.tsv').read_bytes():
            raise RuntimeError('regenerated class census differs')
        first_ready = True

    def second():
        nonlocal second_ready
        if second_ready:
            return
        py('checker2/coefficients.py')
        # coefficients.py writes relative to its current directory.
        shutil.copyfile(src/'coefficients.h', src/'checker2/coefficients.h')
        run(['g++', '-O3', '-std=c++17', '-fopenmp', src/'checker2/checker.cpp',
             '-lcrypto', '-o', src/'checker2/checker'])
        (w/'second').mkdir()
        for mode in ['rows', 'cover']:
            run([src/'checker2/checker', mode, w/'classes65.tsv', w/'units65.tsv', w/'second'])
        second_ready = True

    def check_second(corrupt=False, directory=receipts):
        args = ['--classes', w/'classes65.tsv', '--units', w/'units65.tsv',
                '--results', w/'second', '--receipts', directory]
        if corrupt:
            args.append('--corruptions')
        py('checker2/verify.py', *args)

    def check_order65(directory):
        report = w/'order65-summary.txt'
        py('check_receipts.py', 65, 5, data, data/'units.tsv', directory, output=report)
        text = report.read_text()
        for expected in ['units=70699/70699 ', 'pairs=70830746132488 ',
                         'survivors=1645891558124 ', 'matches=0 ', 'solutions=0 ',
                         'multipass_units=0 ']:
            if expected not in text:
                raise RuntimeError('order-65 exhaustion totals differ: '+expected)
        print(text.strip(), flush=True)

    def check_known(n, found):
        ref = ROOT/'data'/f'solutions{n}.txt'
        report = w/f'known-{n}.txt'
        py('closure.py', n, ref, found, output=report)
        text = report.read_text()
        count = {39: 96, 45: 144, 55: 240}[n]
        for expected in [f'reference={count} ', f'closure={count} ', 'classes=1 ']:
            if expected not in text:
                raise RuntimeError('known-case solution census differs: '+expected)
        print(text.strip(), flush=True)

    def discovery(n, m):
        d = w/f'discovery-{n}'; d.mkdir()
        o = w/f'found-{n}'; o.mkdir()
        run([src/'rows', n, m, d])
        py('units.py', n, m, d/'classes.tsv', d/'units.tsv')
        count = len((d/'units.tsv').read_text().splitlines())
        run([src/'search', n, m, d, d/'units.tsv', 0, count, o, '--threads', a.threads])
        py('check_receipts.py', n, m, d, d/'units.tsv', o)
        py('witness_check.py', n, o/'solutions.tsv')
        check_known(n, o/'solutions.tsv')

    start = time.monotonic()
    for step in selected:
        print('START '+step, flush=True)
        if step == 'first-checker':
            first()
            py('cover_check.py', 65, 5, data, data/'units.tsv')
            check_order65(receipts)
            py('witness_check.py', 65, receipts/'solutions.tsv')
        elif step == 'second-checker':
            second(); check_second()
            if first_ready and not filecmp.cmp(data/'rows.bin', w/'second/rows.bin', shallow=False):
                raise RuntimeError('independent row generators disagree')
            positive_data = w/'positive-data'; positive_data.mkdir()
            os.link(w/'second/rows.bin', positive_data/'rows.bin')
            (positive_data/'classes.tsv').write_text(''.join(
                '\t'.join(line.split('\t')[:6])+'\n'
                for line in (w/'classes65.tsv').read_text().splitlines()))
            shutil.copyfile(w/'units65.tsv', positive_data/'units.tsv')
            positive_out = w/'positive-join'; positive_out.mkdir()
            run([src/'search', 65, 5, positive_data, positive_data/'units.tsv',
                 5200, 5201, positive_out, '--keybits', 32, '--threads', a.threads])
            py('collision_check.py', positive_data, positive_out, '--corruptions')
        elif step == 'first-corruptions':
            first()
            run(['sh', src/'corruptions.sh', data, receipts, 0, 70699, w/'corrupt-first'])
        elif step == 'second-corruptions':
            second(); check_second(True)
            gap = w/'units-gap.tsv'
            gap.write_text('\n'.join((w/'units65.tsv').read_text().splitlines()[:-1])+'\n')
            run([src/'checker2/checker', 'cover', w/'classes65.tsv', gap, w/'second'], reject=True)
        elif step == 'published-counts':
            trivial = w/'order1.txt'
            trivial.write_text('0 0 0 0\n')
            py('witness_check.py', 1, trivial)
            print('PASS order 1: after independent row negations, the unique quadruple is (1,1,1,1)', flush=True)
            for line in (ROOT/'data/published-counts.tsv').read_text().splitlines()[1:]:
                n, expected = map(int, line.split())
                ref = w/f'baseline-{n}.txt'
                opts = [] if a.full_controls or n <= 23 else ['rowfilter']
                run([src/'baseline', n, *opts], output=ref)
                py('closure.py', n, ref, ref, output=w/f'classes-{n}.txt')
                text = (w/f'classes-{n}.txt').read_text()
                if not re.search(rf'classes={expected} ', text):
                    raise RuntimeError('published equivalence-class count differs')
                print(text.strip(), flush=True)
        elif step == 'known-witnesses':
            for n in [39, 45, 55]:
                ref = ROOT/'data'/f'solutions{n}.txt'
                py('witness_check.py', n, ref)
                check_known(n, ref)
        elif step == 'reduction-controls':
            for n, m in [(9, 3), (15, 3)] + ([(27, 9)] if a.full_controls else []):
                ref = w/f'control-ref-{n}.txt'
                run([src/'baseline', n], output=ref)
                py('controls.py', n, m, ref, w/f'variants-{n}')
                if n == 27:
                    count = 0
                    for batch in (w/f'variants-{n}/out_forced-multipass-cap64').glob('batch_*.tsv'):
                        count += sum(int(line.split('\t')[12]) > 1
                                     for line in batch.read_text().splitlines() if line.startswith('U\t'))
                    if count == 0:
                        raise RuntimeError('capacity control did not exercise repeated passes')
                    print(f'PASS repeated-pass control: {count} units used multiple passes', flush=True)
        elif step == 'discovery-controls':
            discovery(39, 3)
            discovery(45, 5)
    if a.full_controls and 'discovery-controls' in selected:
        discovery(55, 5)
    if a.full_search:
        first()
        out = w/'full-search'; out.mkdir()
        run([src/'search', 65, 5, data, data/'units.tsv', 0, 70699, out,
             '--threads', a.threads, '--batch', 64])
        check_order65(out)
        py('witness_check.py', 65, out/'solutions.tsv')
        second()
        check_second(directory=out)
    print(f'PASS selected checks; wall_seconds={time.monotonic()-start:.3f}', flush=True)
    if tmp:
        tmp.cleanup()


if __name__ == '__main__':
    main()
