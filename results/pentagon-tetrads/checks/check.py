#!/usr/bin/env python3
"""Check the computer-assisted part of the proof that no holeless tetrad of
four congruent pentagons exists. Run from the result's folder:

    python3 checks/check.py                 # quick check, a few minutes
    python3 checks/check.py --full          # also rerun the exact angle screen
    python3 checks/check.py --full --part 3/8   # one eighth of that screen

Quick check:
  1. the boundary-map classification reproduces data/maps-h0.jsonl (3 maps),
     and a separate enumeration of the primal maps also finds 3;
  2. the 116 closure cases are exactly the length-feasible angle survivors
     (exact rational LP), they form 22 relabeling groups, every case has an
     explicit relabeling onto its group's closing member, and every group
     has a closing member; and every case's angle family and length cone,
     rederived exactly, match the stored ones;
  3. the closure verifier checks every certificate in data/certificates/
     (it does not import the enumeration code), and both proofs of the
     group closed by an identity run;
  4. a corrupted certificate is rejected.
--full also reruns the exact angle screen for triangles and quadrilaterals
(no survivor) and for pentagons over all 54,938 placements, and compares the
pentagon survivors with data/angle-survivors-n5.jsonl (about 5 CPU-hours;
--part K/N runs the K-th of N parts, 0 <= K < N, and the parts' survivors
together must equal the file).
"""
import argparse
import json
import os
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ENUM = os.path.join(ROOT, 'checks', 'enumeration')
VERIFIER = os.path.join(ROOT, 'checks', 'verifier')
DATA = os.path.join(ROOT, 'data')
PY = sys.executable


def run(args, cwd=ROOT, **kw):
    return subprocess.run([PY] + args, cwd=cwd, check=True, text=True, capture_output=True, **kw).stdout


def fail(msg):
    print('FAIL', msg)
    sys.exit(1)


def key(r):
    return (r['map'], r['placement'], json.dumps(r['labs']), json.dumps(r['pattern']))


def angle_screen(n, out, part=None):
    args = [os.path.join(ENUM, 'angles_exact.py'), os.path.join(DATA, 'maps-h0.jsonl'), str(n), out, '-']
    if part:
        args.append(part)
    run(args, cwd=ENUM)
    return [json.loads(l) for l in open(out)]


def quick(tmp):
    maps = run([os.path.join(ENUM, 'maps.py'), '0', '9'], cwd=ENUM)
    if maps != open(os.path.join(DATA, 'maps-h0.jsonl')).read():
        fail('map classification differs from data/maps-h0.jsonl')
    print('PASS map classification (3 maps)')
    primal = run([os.path.join(ENUM, 'maps_primal.py')], cwd=ENUM)
    if json.loads(primal.splitlines()[0])['classes'] != 3:
        fail('primal map enumeration does not find 3 maps')
    print('PASS primal map enumeration (3 maps)')

    try:
        out = run([os.path.join(ENUM, 'check_cover.py')], cwd=ENUM)
    except subprocess.CalledProcessError as e:
        print(e.stdout)
        fail('cover check')
    print(out.strip().splitlines()[-1].replace('COVER CHECK PASS', 'PASS cover: 116 cases, 22 groups, each closed'))
    try:
        run([os.path.join(ENUM, 'all_cones.py')], cwd=ENUM)
    except subprocess.CalledProcessError as e:
        print(e.stdout[-2000:], e.stderr[-2000:])
        fail('angle families and length cones')
    print('PASS angle families and length cones of all 116 cases')

    certs = sorted(os.listdir(os.path.join(DATA, 'certificates')))
    for c in certs:
        try:
            run([os.path.join(VERIFIER, 'verifier.py'), os.path.join(DATA, 'certificates', c),
                 '--output', os.path.join(tmp, 'v-' + c)], cwd=VERIFIER)
        except subprocess.CalledProcessError as e:
            print(e.stdout[-2000:])
            fail('closure verifier on ' + c)
        print('PASS closure verifier:', c)
    run([os.path.join(ENUM, 'group4.py')], cwd=ENUM)
    run([os.path.join(VERIFIER, 'check_group4.py')], cwd=VERIFIER)
    print('PASS the group closed by an identity (two separate proofs)')

    # flip the sign of one factorization constant: the verifier must reject it
    d = json.loads(open(os.path.join(DATA, 'certificates', 'certs-batch3.jsonl')).readline())
    q = d['cert']['quantities']
    name = sorted(q)[0]
    k = q[name][0]
    q[name][0] = k[1:] if k.startswith('-') else '-' + k
    bad = os.path.join(tmp, 'bad.jsonl')
    open(bad, 'w').write(json.dumps(d) + '\n')
    r = subprocess.run([PY, os.path.join(VERIFIER, 'verifier.py'), bad, '--output', os.path.join(tmp, 'vbad')],
                       cwd=VERIFIER, capture_output=True, text=True)
    if r.returncode == 0:
        fail('a corrupted certificate was accepted')
    print('PASS corrupted certificate rejected')


def full(tmp, part):
    if part is None or part.split('/')[0] == '0':
        for n in (3, 4):
            if angle_screen(n, os.path.join(tmp, 'a%d.jsonl' % n)):
                fail('an angle-feasible placement for n = %d' % n)
            print('PASS exact angle screen, n = %d: no survivor' % n)
    got = {key(r) for r in angle_screen(5, os.path.join(tmp, 'a5.jsonl'), part)}
    want = [json.loads(l) for l in open(os.path.join(DATA, 'angle-survivors-n5.jsonl'))]
    if part:
        k, m = (int(x) for x in part.split('/'))
        want = [r for r in want if r['placement'] % m == k]
    if got != {key(r) for r in want}:
        fail('exact angle screen, n = 5: %d survivors, file has %d' % (len(got), len(want)))
    print('PASS exact angle screen, n = 5%s: %d survivors, as in the file'
          % (' (part %s)' % part if part else '', len(got)))


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--full', action='store_true', help='also rerun the exact angle screen')
    ap.add_argument('--part', help='with --full: run part K/N of the pentagon angle screen only')
    a = ap.parse_args()
    with tempfile.TemporaryDirectory() as tmp:
        if not a.part:
            quick(tmp)
        if a.full:
            full(tmp, a.part)
    print('ALL CHECKS PASSED')


if __name__ == '__main__':
    main()
