#!/usr/bin/env python3
"""Observe the production decomposition; this is NOT its cover checker.

The separately authored checker receives opaque output only. Every decoder
statement comes from the production source. The only substitutions
replace mutable search states by traces which always accept options.
"""
import argparse
from pathlib import Path
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
INPUT = HERE.parent / 'data'


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output', type=Path, required=True,
                   help='new regenerable output directory outside keep')
    p.add_argument('--threads', type=int, required=True)
    args = p.parse_args()
    if args.threads < 1:
        raise ValueError('positive allocation required')
    source = HERE / 'campaign.cpp'
    text = source.read_text()
    snippets = {}
    a = text.index(' int ci=t.id/width;State s(m,ci);s.fixed();bool valid=true;')
    b = text.index('\n if(!t.initialized)', a)
    fast = text[a:b]
    if fast.count('State s(m,ci)') != 1:
        raise ValueError('unexpected fast prefix declaration')
    snippets['fast'] = fast.replace('State s(m,ci)', 'CoverTrace s(m,ci)')
    a = text.index(' int ci=task.id/width;Replay r(in,ci);r.singletons();')
    b = text.index('\n if(!task.initialized)', a)
    direct = text[a:b]
    if direct.count('Replay r(in,ci)') != 1:
        raise ValueError('unexpected direct prefix declaration')
    snippets['direct'] = direct.replace('Replay r(in,ci)', 'CoverTrace r')
    args.output.mkdir(parents=True, exist_ok=False)
    with tempfile.TemporaryDirectory(prefix='ds243-cover-observation-') as directory:
        build = Path(directory)
        for mode, snippet in snippets.items():
            (build / f'coverage-{mode}-prefix.inc').write_text(snippet + '\n')
        for mode in ('fast', 'direct'):
            binary = build / mode
            cmd = ['g++', '-O3', '-std=c++20', '-fopenmp', '-Wall', '-Wextra',
                   '-D' + mode.upper() + '_KERNEL', '-I' + str(build),
                   str(HERE / 'coverage_export.cpp'), '-o', str(binary)]
            subprocess.run(cmd, check=True)
            options = args.output / (mode + '-options.json')
            prefixes = args.output / (mode + '-prefixes.bin')
            subprocess.run([str(binary), str(INPUT / 'p243.txt'),
                            str(INPUT / 'cases.txt'), str(options),
                            str(prefixes), str(args.threads)], check=True)
    print('Exported actual production choices and every prefix; independent cover check still required.')


if __name__ == '__main__':
    main()
