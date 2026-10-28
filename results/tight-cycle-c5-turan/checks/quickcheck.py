#!/usr/bin/env python3
"""Independent exact certificate pairs and original semantic corruptions.

This checks finite certificates and covers, not the Lean asymptotic theorem.
"""
import argparse
import importlib.util
import json
import os
import re
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
_spec = importlib.util.spec_from_file_location('c5_materialization', ROOT / 'checks/materialize.py')
_materialization = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_materialization)
materialize = _materialization.materialize
STEPS = ['p32-original-A', 'p32-original-B', 'p32-corruptions', 'p32-feasibility',
         'p33-coefficient-1', 'p33-coefficient-3999']
TASK_GROUPS = {
    1: [('original', 'A'), ('non-PSD-block', 'A'), ('non-PSD-block', 'B'),
        ('negative-multiplier', 'B'), ('CL-predicate', 'B')],
    2: [('wrong-class-coefficient', 'A'), ('wrong-class-coefficient', 'B')],
    3: [('cover-gap', 'A')],
    4: [('negative-multiplier', 'A'), ('CL-predicate', 'A'),
        ('original', 'B'), ('cover-gap', 'B')],
}
# Measured whole-protocol task times put these groups near 40–60 seconds
# with two checker workers. Each original and each mutation occurs once.
PARTS = {
    1: ['p33-coefficient-1-group1'],
    2: ['p32-original-B', 'p33-coefficient-1-group2'],
    3: ['p32-original-A', 'p33-coefficient-1-group3'],
    4: ['p32-corruptions', 'p32-feasibility', 'p33-coefficient-1-group4'],
    5: ['p33-coefficient-3999-group1'],
    6: ['p33-coefficient-3999-group2'],
    7: ['p33-coefficient-3999-group3'],
    8: ['p33-coefficient-3999-group4'],
}


def run(argv, cwd=None, env=None):
    result = subprocess.run([str(x) for x in argv], cwd=cwd, env=env,
                            capture_output=True, text=True, check=True)
    return result.stdout


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--list', action='store_true')
    p.add_argument('--part', help='one of eight CI parts, K/8 with K from 1 through 8')
    p.add_argument('--cpus', type=int, default=1, help='actual allocated CPUs')
    p.add_argument('--output', type=Path, help='write results after each completed step')
    a = p.parse_args()
    if a.list:
        print(json.dumps(PARTS, sort_keys=True)); return
    assert a.cpus >= 1
    selected = STEPS
    if a.part:
        numerator, denominator = map(int, a.part.split('/'))
        assert denominator == 8 and 1 <= numerator <= 8
        selected = PARTS[numerator]
    materialize()
    records = []
    env = dict(os.environ, OMP_NUM_THREADS='1', OPENBLAS_NUM_THREADS='1',
               C5_CHECK_CPUS=str(a.cpus), PYTHONDONTWRITEBYTECODE='1')
    with tempfile.TemporaryDirectory(prefix='c5-certificates-') as tmp:
        tmp = Path(tmp)
        p32 = tmp / 'p32'; p32.mkdir()
        for source in (ROOT / 'checks/p32').glob('*.py'):
            shutil.copyfile(source, p32 / source.name)
        shutil.copyfile(ROOT / 'data/p32/certificate.json', p32 / 'certificate.json')
        positive = {}
        for step in selected:
            started = time.monotonic()
            if step.startswith('p32'):
                script = {'p32-original-A': 'check_masks.py', 'p32-original-B': 'check_embeddings.py',
                          'p32-corruptions': 'corruptions.py', 'p32-feasibility': 'feasibility.py'}[step]
                argv = [sys.executable, p32 / script]
                if 'original' in step:
                    argv.append(p32 / 'certificate.json')
                data = json.loads(run(argv, cwd=p32, env=env))
                if 'original' in step:
                    assert (data['classes'], data['labelled'], data['rho']) == (835, 371229, [2, 5])
                    assert data['margin_numerator'] * 10000 == data['margin_denominator']
                    positive[step] = data
                elif step == 'p32-corruptions':
                    assert data['count'] == 10
                else:
                    assert data['status'] == 'PASS'
            else:
                coefficient = '3999' if step.startswith('p33-coefficient-3999') else '1'
                group = int(step.rsplit('group', 1)[1]) if '-group' in step else None
                binary = tmp / 'check-exact'
                if not binary.exists():
                    run(['g++', '-O3', '-std=c++17', '-fopenmp', 'checks/p33/check_exact.cpp',
                         '-lgmpxx', '-lgmp', '-o', binary], cwd=ROOT, env=env)
                receipt = tmp / ('corruptions-' + coefficient + '.json')
                argv = [sys.executable, ROOT / 'checks/p33/corruptions.py', ROOT / ('data/p33-' + coefficient),
                        '--checker', binary, '--output', receipt]
                if group:
                    argv += ['--tasks', ','.join(c + ':' + k for c, k in TASK_GROUPS[group])]
                run(argv, env=env)
                data = json.loads(receipt.read_text())
                if a.output:
                    a.output.parent.mkdir(parents=True, exist_ok=True)
                    (a.output.parent / ('protocol-' + coefficient + '.json')).write_text(
                        json.dumps(data, indent=2) + '\n')
                expected = (TASK_GROUPS[group] if group else
                            [(c, k) for tasks in TASK_GROUPS.values() for c, k in tasks])
                assert data['status'] == ('PASS_SELECTED_CERTIFICATE_CORRUPTIONS' if group else
                                          'PASS_EXACT_CERTIFICATE_CORRUPTIONS')
                assert len(data['records']) == len(expected) and all(x['pass'] for x in data['records'])
                assert {(x['case'], x['checker']) for x in data['records']} == set(expected)
                for rejection in data['records']:
                    if rejection['case'] != 'original':
                        assert rejection['returncode'] == 1 and rejection['output'].startswith('REJECT:'), rejection
                        assert not rejection['error'], 'setup errors are not semantic rejections'
                        if rejection['case'] == 'cover-gap':
                            message = rejection['output'].lower()
                            if rejection['checker'] == 'A':
                                # The unchanged C++ checker asserts that orbit membership
                                # equals C5-freeness. Its loader wraps that diagnostic
                                # in an explicit REJECT, without the word "cover".
                                assert 'semantic checker rejection:' in message
                                assert 'bool(seen[(e<<6)|c])==allowed' in message
                            else:
                                assert 'coloured class cover gap or duplicate orbit' in message
                originals = [x for x in data['records'] if x['case'] == 'original']
                assert {x['checker'] for x in originals} == {k for c, k in expected if c == 'original'}
                for entry in originals:
                    answer = json.loads(entry['output'])
                    assert answer['status'] == 'EXACT_B1_CHECKER_' + entry['checker']
                    if entry['checker'] == 'A':
                        answer = answer['semantic']
                    assert answer['classes'] == 40547 and answer['labelled'] == 23758656
                    assert answer['bound'] == [0, 1]
                    assert answer['coefficient'] == ([1, 1] if coefficient == '1' else [3999, 4000])
            records.append({'step': step, 'status': 'PASS',
                            'wall_seconds': time.monotonic() - started,
                            'result': data})
            if a.output:
                a.output.parent.mkdir(parents=True, exist_ok=True)
                a.output.write_text(json.dumps({'status': 'RUNNING', 'Lean_compilation': False,
                                               'steps': records}, indent=2) + '\n')
        if len(positive) == 2:
            a32, b32 = positive.values()
            for key in ['classes', 'labelled', 'rho', 'margin_numerator', 'margin_denominator', 'min_slack_numerator']:
                assert a32[key] == b32[key]
    result = {'status': 'PASS_FINITE_CERTIFICATES', 'Lean_compilation': False,
              'steps': records, 'part': a.part}
    if a.output:
        a.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, sort_keys=True))


if __name__ == '__main__':
    main()
