#!/usr/bin/env python3
"""Check every computational statement of the paper, from the result's folder.

Usage: python3 -I checks/check.py [--part K/N] [--list]

Runs each check below as a separate process (no program imports another) and
prints one PASS line per check, or stops at the first failure with exit 1.
--part K/N runs only checks K, K+N, K+2N, ... of the list (for CI); --list
prints the list. Needs Python 3.12 or newer with numpy and scipy
(requirements.txt) and a C++17 compiler (c++, or the one named by CXX).
"""
import itertools, json, os, shutil, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
DATA = os.path.join(ROOT, 'data')
B_P = os.path.join(DATA, 'B.json')
PY = sys.executable
CXX = os.environ.get('CXX', 'c++')


def fail(msg):
    print('FAIL:', msg)
    sys.exit(1)


def run(args, ok=True, **kw):
    """Run a program; return its output. ok=False requires it to fail."""
    r = subprocess.run(args, capture_output=True, text=True, **kw)
    if ok and r.returncode != 0:
        fail(' '.join(map(str, args)) + '\n' + r.stdout[-2000:] + r.stderr[-2000:])
    if not ok and r.returncode == 0:
        fail('accepted a corrupted input: ' + ' '.join(map(str, args)))
    return r.stdout


def py(name, *args, ok=True, **kw):
    return run([PY, '-I', os.path.join(HERE, name), *map(str, args)], ok=ok, **kw)


def compile_cpp(name, w):
    exe = os.path.join(w, name[:-4])
    run([CXX, '-O2', '-std=c++17', '-o', exe, os.path.join(HERE, name)])
    return exe


def det(M):
    if len(M) == 1:
        return M[0][0]
    return sum((-1) ** j * M[0][j] * det([r[:j] + r[j + 1:] for r in M[1:]]) for j in range(len(M)) if M[0][j])


def write_B(w, B):
    path = os.path.join(w, 'B.json')
    with open(path, 'w') as f:
        json.dump({'B': B}, f)
    return path


def family_B(p):
    return [[1, 0, 0, 1], [0, 1, 0, 2], [0, 0, 1, 2], [0, 0, 0, p]]


def prune_both(w, B_path, prune_check):
    """Generate the pruning certificate and check it with both checkers."""
    cert = os.path.join(w, 'prune.json')
    py('prune.py', B_path, cert)
    out = py('check_prune.py', B_path, cert)
    txt = os.path.join(w, 'prune.txt')
    py('prune_prep.py', B_path, cert, txt)
    if 'ACCEPT' not in run([prune_check], stdin=open(txt)).splitlines():
        fail('prune_check.cpp did not accept ' + B_path)
    return out.strip(), cert


# ---------------------------------------------------------------- the checks

def hand_proof(w):
    tex = os.path.join(ROOT, 'paper', 'paper.tex')
    out = py('check_hand_proof.py', tex)
    text = open(tex, encoding='utf-8').read()
    # corruptions: a wrong identity (Step 2) and a missing case (Step 3)
    bad1 = text.replace('$2A_{00}+B_{11}+2I_3=2A_{11}+3I_2$', '$2A_{00}+B_{11}+2I_3=2A_{11}+2I_2$', 1)
    lines = text.split('\n')
    k = next(i for i, l in enumerate(lines) if l.startswith('$A_{01}+B_{00}+B_{01}+D_{11}$'))
    bad2 = '\n'.join(lines[:k] + lines[k + 1:])
    for bad in (bad1, bad2):
        assert bad != text
        path = os.path.join(w, 'bad.tex')
        open(path, 'w', encoding='utf-8').write(bad)
        py('check_hand_proof.py', path, ok=False)
    return out.strip() + '\nPASS: hand-proof checker rejects a wrong identity and a missing case'


def pruning(w):
    pc = compile_cpp('prune_check.cpp', w)
    out, cert = prune_both(w, B_P, pc)
    c = json.load(open(cert))
    d = c['deletions']
    bad = os.path.join(w, 'bad.json')
    json.dump({'B': c['B'], 'deletions': [d[-1]] + d[:-1]}, open(bad, 'w'))
    py('check_prune.py', B_P, bad, ok=False)
    txt = os.path.join(w, 'bad.txt')
    py('prune_prep.py', B_P, cert, txt, 'movelast')
    r = subprocess.run([pc], stdin=open(txt), capture_output=True, text=True)
    if r.returncode == 0 or not any(l.startswith('REJECT') for l in r.stdout.splitlines()):
        fail('prune_check.cpp accepted a corrupted certificate')
    return (out + '\nPASS: second pruning checker accepts; both checkers reject the certificate '
            'with its last deletion moved first')


def cover(w):
    cert = os.path.join(DATA, 'cover.txt')
    out = py('check_cover.py', B_P, cert)
    bad = os.path.join(w, 'bad.txt')
    lines = open(cert).read().rstrip('\n').split('\n')
    open(bad, 'w').write('\n'.join(lines[:-1]) + '\n')
    py('check_cover.py', B_P, bad, ok=False)
    return out.strip() + '\nPASS: truncated cover certificate rejected'


def vertex_cones(w):
    compat = compile_cpp('compat.cpp', w)
    fans = os.path.join(DATA, 'fans.jsonl')
    out = py('check_fans.py', B_P, fans, compat) + py('fans_check.py', B_P, fans)
    lines = open(fans).read().rstrip('\n').split('\n')
    f0 = json.loads(lines[0])
    assert f0['vertex'] == [0, 0, 0, 0]
    # corruptions of the fan at 0: its last cone dropped; its first cone replaced by the first
    # other unimodular cone on nonzero lattice points of P (which must overlap the rest)
    drop = dict(f0, cones=f0['cones'][:-1])
    rays = sorted({tuple(p) for c in f0['cones'] for p in c})
    have = {frozenset(map(tuple, c)) for c in f0['cones']}
    new = next(list(map(list, c)) for c in itertools.combinations(rays, 4)
               if frozenset(c) not in have and abs(det(c)) == 1)
    swap = dict(f0, cones=[new] + f0['cones'][1:])
    for name, bad in (('one cone dropped', drop), ('one cone replaced', swap)):
        path = os.path.join(w, 'bad.jsonl')
        open(path, 'w').write('\n'.join([json.dumps(bad)] + lines[1:]) + '\n')
        py('check_fans.py', B_P, path, compat, ok=False)
        py('fans_check.py', B_P, path, ok=False)
    return out.strip() + '\nPASS: both fan checkers reject the fan at 0 with one cone dropped or replaced'


EXPECT = {2: (4, 0), 3: (4, 0), 4: (16, 0), 5: (8, 1), 6: (26, 0), 7: (12, 1), 8: (61, 2)}
UNSAT = {5: [family_B(5)], 7: [family_B(7)],
         8: [[[1, 0, 0, 1], [0, 1, 0, 2], [0, 0, 1, 3], [0, 0, 0, 8]],
             [[1, 0, 0, 1], [0, 1, 0, 3], [0, 0, 1, 3], [0, 0, 0, 8]]]}


def classes_a(D):
    """Checker A: completeness, triangulations (compat.cpp), pruning of the rest."""
    def check(w):
        compat = compile_cpp('compat.cpp', w)
        pc = compile_cpp('prune_check.cpp', w)
        path = os.path.join(DATA, 'classes', f'n4_D{D}.jsonl')
        out = py('check_classes.py', path, compat)
        unsat = [json.loads(l.split(':', 1)[1]) for l in out.splitlines() if l.startswith('UNSAT class')]
        n = sum(1 for _ in open(path))
        if (n, len(unsat)) != EXPECT[D]:
            fail(f'det {D}: {n} classes, {len(unsat)} without a triangulation')
        lines = [l for l in out.splitlines() if l.startswith('PASS')]
        for B in unsat:
            res, _ = prune_both(w, write_B(w, B), pc)
            lines.append(res + f' [B = {json.dumps(B)}]')
        return '\n'.join(lines)
    return check


def classes_b(D):
    """Checker B, written separately: completeness and every triangulation (exact LP separation)."""
    def check(w):
        path = os.path.join(DATA, 'classes', f'n4_D{D}.jsonl')
        out = py('classes_check.py', D, path)
        if 'completeness/uniqueness: True' not in out or 'FAIL' in out:
            fail(f'det {D}: second classes checker\n' + out[-2000:])
        n, u = EXPECT[D]
        if f'D={D} classes={n} verified_triangulations={n - u} unsat={u}' not in out:
            fail(f'det {D}: second classes checker counts\n' + out[-2000:])
        return f'PASS: det {D}: second checker: {n} classes complete and distinct; {n - u} triangulations verified'
    return check


def classes_unsat_match(w):
    """The classes without a triangulation are the ones the paper names."""
    for D, Bs in UNSAT.items():
        got = [json.loads(l)['B'] for l in open(os.path.join(DATA, 'classes', f'n4_D{D}.jsonl'))
               if json.loads(l)['status'] == 'UNSAT']
        if got != Bs:
            fail(f'det {D}: classes without a triangulation are {got}')
    return 'PASS: the classes without a triangulation are P[1,2,2,5], P[1,2,2,7], P[1,2,3,8], P[1,3,3,8]'


def family(ps):
    def check(w):
        pc = compile_cpp('prune_check.cpp', w)
        lines = []
        for p in ps:
            res, _ = prune_both(w, write_B(w, family_B(p)), pc)
            lines.append(f'p={p}: ' + res)
        return '\n'.join(lines)
    return check


CHECKS = [
    ('hand proof of Theorem 1.1', hand_proof),
    ('pruning certificate of P', pruning),
    ('unimodular cover of P', cover),
    ('vertex cones of P', vertex_cones),
    ('classes without a triangulation', classes_unsat_match),
] + [(f'classes of determinant {D}, checker A', classes_a(D)) for D in range(2, 9)] \
  + [(f'classes of determinant {D}, checker B', classes_b(D)) for D in range(2, 9)] \
  + [('family, p = 7..17', family([7, 9, 11, 13, 15, 17])),
     ('family, p = 19..25', family([19, 21, 23, 25])),
     ('family, p = 27', family([27])), ('family, p = 29', family([29])), ('family, p = 31', family([31]))]


def main():
    args = sys.argv[1:]
    if args == ['--list']:
        for i, (name, _) in enumerate(CHECKS, 1):
            print(i, name)
        return
    k, n = 1, 1
    if args[:1] == ['--part'] and len(args) == 2:
        k, n = map(int, args[1].split('/'))
    elif args:
        fail(__doc__)
    if shutil.which(CXX) is None:
        fail(f'no C++ compiler ({CXX})')
    for i, (name, fn) in enumerate(CHECKS):
        if i % n != k - 1:
            continue
        with tempfile.TemporaryDirectory() as w:
            print(f'== {name}', flush=True)
            print(fn(w), flush=True)
    print('ALL CHECKS PASSED' + (f' (part {k}/{n})' if n > 1 else ''))


if __name__ == '__main__':
    main()
