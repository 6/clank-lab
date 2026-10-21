#!/usr/bin/env python3
"""Executable checks for R(P10, P10, P10) = 18.

  check.py quick [--work DIR] [--jobs J] [--part K/N] [--list]
                 [--sample S] [--seed X]
  check.py full  [--work DIR] [--jobs J] [--lean-jobs L] [--chunks LIST]
                 [--cross-check]

The Lean proof lives in ../lean. Its default `lake build` checks everything
that needs no generated data. The certificates of the nine UNSAT facts it
rests on (seven ladder rungs, the cover of the K_18 cube list, and the
15,956 cubes) are too large to ship, so this script regenerates them with
the bundled solver and hands them to Lean, which checks each one with its
verified LRAT checker:

  quick  the seven rungs and the cover, checked in Lean (`lake build
         R3P10Ladder`) and by drat-trim and cake_lpr; a random sample of
         K_18 cubes, checked the same way (`lake build R3P10Sample`);
         planted certificate errors and planted errors in the Lean
         statements, each of which must be rejected; and the checks that
         use no Lean: the inputs regenerate, the path-clause, input and
         coloring checkers reject their bad controls, the independent
         encoding auditor passes and rejects its corruptions.
         --part K/N runs the K-th of N balanced parts; --list shows them.
  full   every cube (about 250 CPU-hours), in chunks of up to 200 cubes,
         one Lean module each (`R3P10Cubes.C<k>`), resuming from records
         in the work directory; then `lake build R3P10Final`, whose
         `R3_P10_eq_18 : ramsey3Path 10 = 18` must print exactly the
         axioms propext, Classical.choice, Lean.ofReduceBool,
         Lean.trustCompiler and Quot.sound. --chunks restricts the run to
         some chunks (e.g. 0-40,77); --cross-check also runs check_paths,
         check_inputs and cake_lpr on every cube.

The work directory (default: a directory under the system's temporary
directory) holds the solver tools, built from pinned upstream sources, and
per-cube temporaries. Certificates and generated Lean modules are written to
../lean/generated/, which is not part of the bundle.

Requirements: Python 3.9+, git, a C/C++ compiler and make, and Lean through
elan (`lake` on PATH; ../lean/lean-toolchain pins the version).
"""
import argparse
import glob
import json
import os
import random
import shutil
import subprocess
import sys
import tempfile
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
DATA = os.path.join(ROOT, 'data')
LEAN = os.path.join(ROOT, 'lean')
GEN = os.path.join(LEAN, 'generated')
CERTS = os.path.join(GEN, 'certs')
PY = sys.executable
# keep the bundle free of __pycache__ (the auditor's scripts import one another)
os.environ['PYTHONDONTWRITEBYTECODE'] = '1'
sys.dont_write_bytecode = True

# The ladder R_3(P_m) <= n, each rung (n, m, k) solved whole; k is the
# length of the fixed path, which the rung below justifies.
LADDER = [(5, 3, 0), (6, 4, 3), (9, 5, 4), (10, 6, 5), (13, 7, 6), (14, 8, 7), (17, 9, 8)]
K18 = (18, 10, 9)
NCUBES = 15956

# Pinned upstream sources of the tools (built into WORK/bin).
TOOLS = [
    ('cadical', 'https://github.com/arminbiere/cadical.git', 'c60730422e758ef1cebe7aeddf2dda31c996bf04'),
    ('drat-trim', 'https://github.com/marijnheule/drat-trim.git', '2e3b2dc0ecf938addbd779d42877b6ed69d9a985'),
    ('cake_lpr', 'https://github.com/tanyongkiam/cake_lpr.git', 'a36874a8b750b43fe4b385b8ddbf5b033e46a3fa'),
]

AXIOMS5 = 'propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound'
lock = threading.Lock()


class CheckFailed(Exception):
    pass


def need(ok, msg):
    if not ok:
        raise CheckFailed(msg)


def say(msg):
    with lock:
        print(msg, flush=True)


def run(cmd, **kw):
    kw.setdefault('capture_output', True)
    kw.setdefault('text', True)
    return subprocess.run([str(c) for c in cmd], **kw)


def cnf_path(n, m):
    return os.path.join(DATA, 'cnf', f'k{n}p{m}.cnf')


# ------------------------------------------------------------------ tools

class Tools:
    def __init__(self, work):
        self.work = work
        self.src = os.path.join(work, 'src')
        self.bin = os.path.join(work, 'bin')
        self.cadical = os.path.join(self.bin, 'cadical')
        self.drat_trim = os.path.join(self.bin, 'drat-trim')
        self.cake_lpr = os.path.join(self.bin, 'cake_lpr')
        self.p3path = os.path.join(self.bin, 'p3path')

    def fetch(self, name, url, commit):
        d = os.path.join(self.src, name)
        if os.path.isdir(os.path.join(d, '.git')):
            r = run(['git', '-C', d, 'rev-parse', 'HEAD'])
            if r.stdout.strip() == commit:
                return d
            shutil.rmtree(d)
        os.makedirs(d)
        run(['git', 'init', '-q', d], check=True)
        r = run(['git', '-C', d, 'fetch', '-q', '--depth', '1', url, commit])
        if r.returncode != 0:            # servers that refuse fetching by commit
            shutil.rmtree(d)
            run(['git', 'clone', '-q', url, d], check=True)
        run(['git', '-C', d, 'checkout', '-q', commit if r.returncode else 'FETCH_HEAD'], check=True)
        need(run(['git', '-C', d, 'rev-parse', 'HEAD']).stdout.strip() == commit, f'{name}: wrong commit')
        return d

    def build(self):
        os.makedirs(self.bin, exist_ok=True)
        src = {name: self.fetch(name, url, commit) for name, url, commit in TOOLS}
        cad = src['cadical']
        if not os.path.exists(os.path.join(cad, 'build', 'libcadical.a')):
            run(['./configure'], cwd=cad, check=True)
            run(['make', f'-j{os.cpu_count() or 1}'], cwd=cad, check=True)
        shutil.copyfile(os.path.join(cad, 'build', 'cadical'), self.cadical)
        os.chmod(self.cadical, 0o755)
        run(['gcc', '-O2', '-D_GNU_SOURCE', '-o', self.drat_trim,
             os.path.join(src['drat-trim'], 'drat-trim.c')], check=True)
        asm = {'x86_64': 'cake_lpr.S', 'amd64': 'cake_lpr.S', 'aarch64': 'cake_lpr_arm8.S',
               'arm64': 'cake_lpr_arm8.S'}.get(os.uname().machine)
        need(asm is not None, f'cake_lpr has no build for {os.uname().machine}')
        run(['gcc', '-O2', '-std=c99', '-o', self.cake_lpr, os.path.join(src['cake_lpr'], 'basis_ffi.c'),
             os.path.join(src['cake_lpr'], asm)], check=True)
        run(['g++', '-O3', '-std=c++17', '-I', os.path.join(cad, 'src'), '-o', self.p3path,
             os.path.join(HERE, 'p3path.cpp'), os.path.join(cad, 'build', 'libcadical.a')], check=True)
        say(f'tools built in {self.bin}: CaDiCaL, drat-trim, cake_lpr (pinned commits), p3path')


# ------------------------------------------------------------------ formulas

def merged(cnf, extra_files, units, out):
    """Write CNF + clause files + unit clauses (the file the checkers read)."""
    hdr, body = None, []
    with open(cnf) as f:
        for line in f:
            if line.startswith('p'):
                hdr = line.split()
            elif not line.startswith('c'):
                body.append(line)
    extra = 0
    for p in extra_files:
        with open(p) as f:
            extra += sum(1 for _ in f)
    with open(out, 'w') as o:
        o.write(f'p cnf {hdr[2]} {int(hdr[3]) + extra + len(units)}\n')
        o.writelines(body)
        for p in extra_files:
            with open(p) as f:
                shutil.copyfileobj(f, o)
        for u in units:
            o.write(f'{u} 0\n')


def load_cubes(path):
    out = []
    for line in open(path):
        lits = [int(t) for t in line.split()]
        need(lits and lits[-1] == 0, f'{path}: bad cube line')
        out.append(lits[:-1])
    return out


def final_cubes():
    """The depth-10 cubes without the 16 split parents, then the children
    (the list `finalCubes` in ../lean/R3P10/Cubes.lean)."""
    cubes = load_cubes(os.path.join(DATA, 'k18', 'cubes.txt'))
    par = [int(t) for t in open(os.path.join(DATA, 'k18', 'split', 'parents.txt')).read().split()]
    children = load_cubes(os.path.join(DATA, 'k18', 'split', 'children.txt'))
    need(len(set(par)) == len(par) and all(0 <= i < len(cubes) for i in par), 'bad split parents')
    out = [c for i, c in enumerate(cubes) if i not in set(par)] + children
    need(len(out) == NCUBES, f'final list has {len(out)} cubes, expected {NCUBES}')
    return out


def write_lines(path, cubes, negate=False):
    with open(path, 'w') as f:
        for c in cubes:
            f.write(' '.join(str(-l if negate else l) for l in c) + ' 0\n')


# ------------------------------------------------------------------ one refutation

def refute(tools, d, n, m, cnf, cube=(), timeout=None, cross_check=True):
    """Solve CNF (+ cube) with p3path and turn its DRAT proof into LRAT.
    With cross_check, also check the clause log (check_paths.py and the
    independent auditor), the exact input (check_inputs.py) and the LRAT
    proof (cake_lpr). Returns (status, info)."""
    os.makedirs(d, exist_ok=True)
    drat, log, full, lrat = (os.path.join(d, x) for x in ('p.drat', 'p.log', 'full.cnf', 'p.lrat'))
    cmd = [tools.p3path, cnf, n, m, '--proof', drat, '--log', log, '--model', os.path.join(d, 'model')]
    if cube:
        cmd[4:4] = ['--cube', ' '.join(map(str, cube))]
    t0 = time.time()
    try:
        r = run(cmd, timeout=timeout)
    except subprocess.TimeoutExpired:
        return 'TIMEOUT', {'solve_s': round(time.time() - t0, 1)}
    info = {'solve_s': round(time.time() - t0, 1)}
    if r.returncode == 10:
        c = run([PY, os.path.join(HERE, 'check_colouring.py'), n, m, os.path.join(d, 'model')])
        return 'SAT', dict(info, coloring=c.stdout.strip())
    if r.returncode != 20:
        return 'UNKNOWN', dict(info, rc=r.returncode)
    if cross_check:
        need(run([PY, os.path.join(HERE, 'check_paths.py'), n, m, log]).returncode == 0,
             f'{d}: check_paths rejected the clause log')
        need(run([PY, os.path.join(HERE, 'audit', 'audit.py'), 'paths', n, m, log]).returncode == 0,
             f'{d}: the encoding auditor rejected the clause log')
    merged(cnf, [log], list(cube), full)
    if cross_check:
        cmd = [PY, os.path.join(HERE, 'check_inputs.py'), full, cnf, '--add', log]
        if cube:
            cmd += ['--units', ' '.join(map(str, cube))]
        need(run(cmd).returncode == 0, f'{d}: check_inputs rejected the merged formula')
    t1 = time.time()
    r = run([tools.drat_trim, full, drat, '-L', lrat, '-t', '200000'], errors='replace')
    info['drat_trim_s'] = round(time.time() - t1, 1)
    need('s VERIFIED' in r.stdout, f'{d}: drat-trim did not verify the proof')
    if cross_check:
        r = run([tools.cake_lpr, full, lrat])
        need('s VERIFIED UNSAT' in r.stdout, f'{d}: cake_lpr did not verify the proof')
    return 'UNSAT', info


def pack(cnf, log, nunits, lrat, cert):
    os.makedirs(os.path.dirname(cert), exist_ok=True)
    prefix = cert[:-len('.cert')] + '.tmp'
    r = run([PY, os.path.join(HERE, 'pack.py'), cnf, log, nunits, lrat, prefix, '--compact'])
    need(r.returncode == 0, f'pack.py failed: {r.stderr[-300:]}')
    os.replace(prefix + '.cert', cert)


# ------------------------------------------------------------------ Lean

def lake(*args, check=True):
    need(shutil.which('lake') is not None, 'lake not found: install elan (see ../lean/README.md)')
    r = run(['lake', *args], cwd=LEAN)
    if check and r.returncode != 0:
        tail = '\n'.join((r.stdout + r.stderr).strip().splitlines()[-40:])
        raise CheckFailed(f'lake {" ".join(args)} failed:\n{tail}')
    return r


_cache_done = []


def lean_ready():
    if not _cache_done:
        lake('exe', 'cache', 'get')
        _cache_done.append(True)


def forget(*modules):
    """Remove Lake's build outputs of these modules, so that the next build
    checks them again (Lake does not track the certificate files they read)."""
    for mod in modules:
        rel = mod.replace('.', '/')
        for p in glob.glob(os.path.join(LEAN, '.lake', 'build', '**', rel + '.*'), recursive=True):
            os.unlink(p)


def lake_build(target, modules=None):
    lean_ready()
    forget(*(modules or [target]))
    r = lake('build', target)
    return r.stdout + r.stderr


# ------------------------------------------------------------------ quick steps

def step_inputs(tools, args):
    """The inputs regenerate: encode.py prints every formula file byte
    for byte, lower_bound.py the K_17 coloring, and the final cube list has
    15,956 cubes."""
    for n, m, k in LADDER + [K18]:
        r = run([PY, os.path.join(HERE, 'encode.py'), n, m, '--fix', k])
        need(r.returncode == 0 and r.stdout == open(cnf_path(n, m)).read(),
             f'encode.py {n} {m} --fix {k} differs from data/cnf/k{n}p{m}.cnf')
    say('encode.py regenerates the 8 formulas in data/cnf byte for byte')
    r = run([PY, os.path.join(HERE, 'lower_bound.py')])
    need(r.stdout == open(os.path.join(DATA, 'k17-coloring.txt')).read(),
         'lower_bound.py differs from data/k17-coloring.txt')
    say('lower_bound.py regenerates data/k17-coloring.txt byte for byte')
    final_cubes()
    say(f'final cube list: {NCUBES} cubes (depth-10 list without the 16 split parents, then the 656 children)')


def step_checkers(tools, args):
    """Checker controls: check_paths.py accepts a good log and rejects ten
    kinds of bad path clause; check_inputs.py rejects a merged formula with
    an extra unit; check_colouring.py accepts the K_17 coloring for P_10,
    finds a P_9, and finds a P_10 after one edge is recolored."""
    ctl = os.path.join(HERE, 'controls')
    need(run([PY, os.path.join(HERE, 'check_paths.py'), 10, 6, os.path.join(ctl, 'paths-good.txt')]).returncode == 0,
         'check_paths rejected the good control')
    bad = sorted(glob.glob(os.path.join(ctl, 'paths-bad-*.txt')))
    need(len(bad) == 10, 'expected ten bad path controls')
    for p in bad:
        need(run([PY, os.path.join(HERE, 'check_paths.py'), 10, 6, p]).returncode != 0,
             f'check_paths accepted {os.path.basename(p)}')
    say(f'check_paths.py: good control accepted, all {len(bad)} bad controls rejected')
    with tempfile.TemporaryDirectory() as t:
        good = os.path.join(ctl, 'paths-good.txt')
        m = os.path.join(t, 'm.cnf')
        merged(cnf_path(10, 6), [good], [1], m)
        ci = [PY, os.path.join(HERE, 'check_inputs.py'), m, cnf_path(10, 6), '--add', good]
        need(run(ci + ['--units', '1']).returncode == 0, 'check_inputs rejected the exact merged formula')
        need(run(ci).returncode != 0, 'check_inputs accepted a merged formula with an extra unit')
        merged(cnf_path(10, 6), [good], [], m)
        need(run(ci + ['--units', '1']).returncode != 0, 'check_inputs accepted a merged formula missing a unit')
        say('check_inputs.py: exact formula accepted; extra and missing unit rejected')
        col = os.path.join(DATA, 'k17-coloring.txt')
        cc = os.path.join(HERE, 'check_colouring.py')
        need(run([PY, cc, 17, 10, col]).returncode == 0, 'check_colouring rejected the K_17 coloring')
        need(run([PY, cc, 17, 9, col]).returncode != 0, 'check_colouring missed a monochromatic P_9')
        txt = open(col).read()
        need(txt.count('0 9 1\n') == 1, 'k17 coloring: edge line not found')
        planted = os.path.join(t, 'k17-planted.txt')
        open(planted, 'w').write(txt.replace('0 9 1\n', '0 9 0\n'))
        need(run([PY, cc, 17, 10, planted]).returncode != 0, 'check_colouring accepted a recolored coloring')
        say('check_colouring.py: K_17 coloring has no monochromatic P_10; a P_9 found; '
            'recoloring edge {0, 9} gives a P_10, found')


def step_audit(tools, args):
    """The independent encoding auditor (audit/): every clause of every
    formula against a direct reading of the problem, the reductions as
    checked lemmas, small instances exhaustively; its 30 corruption
    controls; and 12,000 mutated clauses on small instances."""
    a = os.path.join(HERE, 'audit')
    r = run([PY, os.path.join(a, 'audit.py'), 'all'])
    need(r.returncode == 0 and r.stdout.strip().endswith('PASS'), 'audit.py all failed:\n' + r.stdout[-2000:])
    say('encoding audit: every clause of the 8 formulas valid, inventories equal, ladder premises, '
        'small instances exhaustive: PASS')
    with tempfile.TemporaryDirectory() as t:
        r = run([PY, os.path.join(a, 'corruptions.py'), t])
        need(r.returncode == 0, 'audit corruption controls failed:\n' + r.stdout[-2000:])
        say('encoding audit corruptions: ' + r.stdout.strip().splitlines()[-1])
    r = run([PY, os.path.join(a, 'soundness_fuzz.py')])
    need(r.returncode == 0, 'audit soundness fuzz failed:\n' + r.stdout[-2000:])
    say('encoding audit fuzz: no invalid mutant accepted (4 small instances, 3,000 mutants each)')


def step_cubes(tools, args):
    """The cube list regenerates: p3path --gencubes 10 gives data/k18/cubes.txt
    and its generation log; splitting the 16 parents gives the children and
    their log."""
    n, m, _ = K18
    with tempfile.TemporaryDirectory(dir=args.work) as t:
        c, g = os.path.join(t, 'cubes.txt'), os.path.join(t, 'genlog.txt')
        r = run([tools.p3path, cnf_path(n, m), n, m, '--gencubes', 10, c, '--log', g])
        need(open(c).read() == open(os.path.join(DATA, 'k18', 'cubes.txt')).read() and
             open(g).read() == open(os.path.join(DATA, 'k18', 'genlog.txt')).read(),
             'the depth-10 cube list or its log does not regenerate')
        cubes = load_cubes(os.path.join(DATA, 'k18', 'cubes.txt'))
        ch, cl = [], []
        for i in open(os.path.join(DATA, 'k18', 'split', 'parents.txt')).read().split():
            run([tools.p3path, cnf_path(n, m), n, m, '--cube', ' '.join(map(str, cubes[int(i)])),
                 '--gencubes', 4, c, '--log', g], check=True)
            ch.append(open(c).read())
            cl.append(open(g).read())
        need(''.join(ch) == open(os.path.join(DATA, 'k18', 'split', 'children.txt')).read() and
             ''.join(cl) == open(os.path.join(DATA, 'k18', 'split', 'genlog.txt')).read(),
             'the split of the 16 parents does not regenerate')
    say(f'cube list regenerates: {len(cubes)} depth-10 cubes and the 656 children of the 16 split parents')


def make_ladder_certs(tools, args, cross_check=True):
    """Certificates of the seven rungs and the cover, into generated/certs."""
    os.makedirs(CERTS, exist_ok=True)

    def rung(r):
        n, m, k = r
        d = os.path.join(args.work, 'ladder', f'k{n}p{m}')
        shutil.rmtree(d, ignore_errors=True)
        st, info = refute(tools, d, n, m, cnf_path(n, m), cross_check=cross_check)
        need(st == 'UNSAT', f'K_{n}, P_{m}: {st}')
        pack(cnf_path(n, m), os.path.join(d, 'p.log'), 0, os.path.join(d, 'p.lrat'),
             os.path.join(CERTS, f'k{n}p{m}.cert'))
        shutil.rmtree(d)
        say(f'R_3(P_{m}) <= {n}: UNSAT in {info["solve_s"]} s'
            + (', path clauses, input, drat-trim and cake_lpr checked' if cross_check else '')
            + f'; certificate {os.path.getsize(os.path.join(CERTS, f"k{n}p{m}.cert")):,} bytes')

    with ThreadPoolExecutor(max(1, min(args.jobs, len(LADDER)))) as pool:
        for f in as_completed([pool.submit(rung, r) for r in sorted(LADDER, key=lambda r: -r[0])]):
            f.result()

    # the cover: base + both generation logs + the negation of every final cube
    n, m, _ = K18
    d = os.path.join(args.work, 'cover')
    shutil.rmtree(d, ignore_errors=True)
    os.makedirs(d)
    logs = [os.path.join(DATA, 'k18', 'genlog.txt'), os.path.join(DATA, 'k18', 'split', 'genlog.txt')]
    genlog = os.path.join(d, 'genlog.txt')
    with open(genlog, 'w') as o:
        for p in logs:
            o.write(open(p).read())
    cubes = final_cubes()
    cl, neg = os.path.join(d, 'final.txt'), os.path.join(d, 'neg.txt')
    write_lines(cl, cubes)
    write_lines(neg, cubes, negate=True)
    full, drat, lrat = (os.path.join(d, x) for x in ('cover.cnf', 'cover.drat', 'cover.lrat'))
    merged(cnf_path(n, m), [genlog, neg], [], full)
    if cross_check:
        need(run([PY, os.path.join(HERE, 'check_paths.py'), n, m, *logs]).returncode == 0,
             'check_paths rejected a generation log')
        need(run([PY, os.path.join(HERE, 'check_inputs.py'), full, cnf_path(n, m), '--add', genlog,
                  '--negcubes', cl]).returncode == 0, 'check_inputs rejected the cover formula')
    r = run([tools.cadical, '-q', '--no-binary', full, drat])
    need(r.returncode == 20, f'cover formula not refuted by CaDiCaL (rc {r.returncode})')
    r = run([tools.drat_trim, full, drat, '-L', lrat, '-t', '200000'], errors='replace')
    need('s VERIFIED' in r.stdout, 'drat-trim did not verify the cover proof')
    if cross_check:
        need('s VERIFIED UNSAT' in run([tools.cake_lpr, full, lrat]).stdout, 'cake_lpr did not verify the cover')
    pack(cnf_path(n, m), genlog, len(cubes), lrat, os.path.join(CERTS, 'cover.cert'))
    shutil.rmtree(d)
    say(f'cover: base + generation logs + {len(cubes):,} negated cubes refuted by CaDiCaL'
        + (', input, drat-trim and cake_lpr checked' if cross_check else ''))


def step_ladder(tools, args):
    """The seven rungs R_3(P_3) <= 5, ..., R_3(P_9) <= 17 re-solved whole and
    the cover of the final cube list re-derived; each certificate checked by
    drat-trim and cake_lpr, and by Lean's LRAT checker (lake build
    R3P10Ladder)."""
    make_ladder_certs(tools, args)
    lake_build('R3P10Ladder')
    say('lake build R3P10Ladder: the 7 rungs and the cover checked by Lean\'s LRAT checker; '
        'axioms ' + AXIOMS5)


def cube_job(tools, args, i, lits, timeout, cross_check):
    n, m, _ = K18
    d = os.path.join(args.work, 'cubes', f'c{i:06d}')
    shutil.rmtree(d, ignore_errors=True)
    st, info = refute(tools, d, n, m, cnf_path(n, m), lits, timeout=timeout, cross_check=cross_check)
    rec = dict(info, cube=i, result=st)
    if st == 'UNSAT':
        cert = os.path.join(CERTS, f'c{i:06d}.cert')
        pack(cnf_path(n, m), os.path.join(d, 'p.log'), len(lits), os.path.join(d, 'p.lrat'), cert)
        rec.update(result='CERT', cert_bytes=os.path.getsize(cert))
    shutil.rmtree(d, ignore_errors=True)
    return rec


def step_sample(tools, args):
    """A random sample of K_18 cubes re-solved; each certificate checked by
    drat-trim and cake_lpr and by Lean's LRAT checker (lake build
    R3P10Sample)."""
    cubes = final_cubes()
    seed = args.seed if args.seed is not None else random.SystemRandom().randrange(10 ** 6)
    order = random.Random(seed).sample(range(NCUBES), NCUBES)
    say(f'cube sample: seed {seed}, {args.sample} cubes, each solve limited to {args.cube_timeout} s '
        f'(a cube over the limit is skipped and another drawn; the full check does every cube)')
    for p in glob.glob(os.path.join(CERTS, 'c*.cert')):
        os.unlink(p)
    done, skipped = [], []
    it = iter(order)
    with ThreadPoolExecutor(max(1, args.jobs)) as pool:
        futs = {pool.submit(cube_job, tools, args, i, cubes[i], args.cube_timeout, True): i
                for i in (next(it) for _ in range(args.sample))}
        while futs:
            f = next(as_completed(futs))
            i = futs.pop(f)
            rec = f.result()
            if rec['result'] == 'CERT':
                done.append(i)
                say(f'cube {i}: UNSAT in {rec["solve_s"]} s; path clauses, input, drat-trim and cake_lpr checked')
            else:
                need(rec['result'] == 'TIMEOUT', f'cube {i}: {rec}')
                skipped.append(i)
                need(len(skipped) <= 4 * args.sample, 'too many cubes over the time limit')
                j = next(it)
                futs[pool.submit(cube_job, tools, args, j, cubes[j], args.cube_timeout, True)] = j
    done.sort()
    os.makedirs(GEN, exist_ok=True)
    with open(os.path.join(GEN, 'R3P10Sample.lean'), 'w') as f:
        f.write('import R3P10.Base\n\n/-! Sampled cubes of the final list, each checked by Lean\'s LRAT checker. -/\n\n'
                'namespace R3P10.Sample\nopen R3P10\n\n')
        for i in done:
            f.write(f'lrat_cube_c c{i} {i} "generated/certs/c{i:06d}.cert"\n'
                    f'example : CubeOK {i} := c{i}\n\n')
        f.write(f'/-- info: \'R3P10.Sample.c{done[0]}\' depends on axioms: [{AXIOMS5}] -/\n'
                f'#guard_msgs in #print axioms c{done[0]}\n\nend R3P10.Sample\n')
    lake_build('R3P10Sample')
    say(f'lake build R3P10Sample: cubes {", ".join(map(str, done))} checked by Lean\'s LRAT checker'
        + (f' (skipped over the limit: {", ".join(map(str, skipped))})' if skipped else ''))


def step_planted_certs(tools, args):
    """Planted certificate errors: from the K_10 / P_6 rung's certificate, a
    corrupted lemma, a dropped hint, a non-path, the certificate against the
    K_13 / P_7 formula, and the K_18 formula compared with the wrong file,
    each rejected by Lean (the unchanged certificate accepted); and a
    corrupted lemma and a swapped formula rejected by cake_lpr."""
    n, m = 10, 6
    d = os.path.join(args.work, 'planted', f'k{n}p{m}')
    shutil.rmtree(d, ignore_errors=True)
    st, _ = refute(tools, d, n, m, cnf_path(n, m))
    need(st == 'UNSAT', f'K_{n}, P_{m}: {st}')
    full, lrat = os.path.join(d, 'full.cnf'), os.path.join(d, 'p.lrat')
    lines = open(lrat).read().splitlines(True)
    adds = [k for k, l in enumerate(lines) if l.split()[1] != 'd' and l.split()[1] != '0']
    k = adds[len(adds) // 2]
    t = lines[k].split()
    t[1] = str(-int(t[1]))
    bad = os.path.join(d, 'bad.lrat')
    open(bad, 'w').writelines(lines[:k] + [' '.join(t) + '\n'] + lines[k + 1:])
    need('s VERIFIED UNSAT' not in run([tools.cake_lpr, full, bad]).stdout, 'cake_lpr accepted a corrupted lemma')
    other = os.path.join(d, 'other.cnf')
    st2, _ = refute(tools, os.path.join(d, 'k13'), 13, 7, cnf_path(13, 7), cross_check=False)
    merged(cnf_path(13, 7), [os.path.join(d, 'k13', 'p.log')], [], other)
    need('s VERIFIED UNSAT' not in run([tools.cake_lpr, other, lrat]).stdout,
         'cake_lpr accepted the K_10 proof for the K_13 formula')
    say('cake_lpr: a corrupted lemma and a swapped formula rejected')
    cert = os.path.join(d, 'k10p6.cert')
    pack(cnf_path(n, m), os.path.join(d, 'p.log'), 0, lrat, cert)
    lean_ready()
    lake('build', 'R3P10')
    r = run([PY, os.path.join(HERE, 'planted_certs.py'), cert, os.path.join(GEN, 'planted')])
    for line in r.stdout.strip().splitlines():
        say('  ' + line)
    need(r.returncode == 0, 'a planted certificate error was not rejected')
    shutil.rmtree(d)


def step_planted_lean(tools, args):
    """Planted errors in the Lean development: each unsound change (a path
    clause missing an edge, a dropped clause, a generator that moves the
    fixed path, a fixed path one edge too long, the lex comparison
    reversed, a skip test ignoring the color map, a recolored K_17 edge)
    makes `lake build` fail in the expected declaration."""
    lean_ready()
    r = run([PY, os.path.join(HERE, 'planted_lean.py')])
    for line in r.stdout.strip().splitlines():
        say('  ' + line)
    need(r.returncode == 0, 'a planted Lean error was not caught')


# name, function, needs the solver tools, rough seconds (for --part)
STEPS = [
    ('inputs', step_inputs, False, 2),
    ('checkers', step_checkers, False, 2),
    ('audit', step_audit, False, 30),
    ('cubes', step_cubes, True, 30),
    ('ladder', step_ladder, True, 450),
    ('sample', step_sample, True, 120),
    ('planted-certs', step_planted_certs, True, 60),
    ('planted-lean', step_planted_lean, False, 100),
]


def parts(n):
    """Balanced assignment of the steps to n parts (longest first)."""
    load = [[0, []] for _ in range(n)]
    for name, _, _, w in sorted(STEPS, key=lambda s: -s[3]):
        p = min(range(n), key=lambda k: (load[k][0], k))
        load[p][0] += w
        load[p][1].append(name)
    return [[s[0] for s in STEPS if s[0] in names] for _, names in load]


def quick(args):
    names = [s[0] for s in STEPS]
    if args.part:
        k, n = map(int, args.part.split('/'))
        need(1 <= k <= n, '--part K/N needs 1 <= K <= N')
        names = parts(n)[k - 1]
    if args.list:
        for name in names:
            print(name)
        return
    if not names:
        print('this part has no steps')
        return
    tools = Tools(args.work)
    if any(s[2] for s in STEPS if s[0] in names):
        tools.build()
    t0 = time.time()
    for name, fn, _, _ in STEPS:
        if name in names:
            t = time.time()
            say(f'== {name}')
            fn(tools, args)
            say(f'== {name}: PASS ({time.time() - t:.0f} s)')
    say(f'PASS quick check{" part " + args.part if args.part else ""} ({time.time() - t0:.0f} s after building the tools)')


# ------------------------------------------------------------------ full

def chunk_list(spec, plan):
    if not spec:
        return sorted(plan)
    out = set()
    for part in spec.split(','):
        a, _, b = part.partition('-')
        out.update(range(int(a), int(b or a) + 1))
    need(out <= set(plan), 'unknown chunk number')
    return sorted(out)


def load_records(path, key):
    out = {}
    if os.path.exists(path):
        for line in open(path):
            if line.strip():
                try:
                    r = json.loads(line)
                except ValueError:
                    continue            # a torn last line: that item reruns
                out[r[key]] = r
    return out


def append(path, rec):
    with lock:
        with open(path, 'a') as f:
            f.write(json.dumps(rec) + '\n')
            f.flush()
            os.fsync(f.fileno())


def olean(mod):
    return os.path.join(LEAN, '.lake', 'build', 'lib', 'lean', *mod.split('.')) + '.olean'


def write_all(chunks):
    """Write generated/R3P10Cubes.lean: the chunk ranges joined into
    `R3P10.K18.all : ∀ i, 0 ≤ i → i < N → CubeOK i`."""
    order_c = sorted(chunks, key=lambda c: c['a'])
    n = order_c[-1]['b']
    with open(os.path.join(GEN, 'R3P10Cubes.lean'), 'w') as f:
        f.write('import R3P10.Base\n')
        for c in order_c:
            f.write(f'import R3P10Cubes.C{c["chunk"]:03d}\n')
        f.write(f'\n/-! All {n} cubes of the final list: the chunk ranges joined. -/\n\nnamespace R3P10.K18\n\n'
                f'theorem all : ∀ i, 0 ≤ i → i < {n} → CubeOK i :=\n')
        term = f'r{order_c[-1]["chunk"]}'
        for c in reversed(order_c[:-1]):
            term = f'(@range_join CubeOK {c["a"]} {c["b"]} {n} r{c["chunk"]} {term})'
        f.write('  ' + term + '\n\nend R3P10.K18\n')


def full(args):
    plan = {c['chunk']: c for c in json.load(open(os.path.join(DATA, 'chunks.json')))}
    spans = sorted((c['a'], c['b']) for c in plan.values())
    need(spans[0][0] == 0 and spans[-1][1] == NCUBES and all(x[1] == y[0] for x, y in zip(spans, spans[1:])),
         'data/chunks.json does not cover the cube list contiguously')
    want = chunk_list(args.chunks, plan)
    tools = Tools(args.work)
    tools.build()
    cubes = final_cubes()
    rec_dir = os.path.join(args.work, 'records')
    os.makedirs(rec_dir, exist_ok=True)
    os.makedirs(os.path.join(GEN, 'R3P10Cubes'), exist_ok=True)
    os.makedirs(CERTS, exist_ok=True)
    cube_rec, chunk_rec = os.path.join(rec_dir, 'cubes.jsonl'), os.path.join(rec_dir, 'chunks.jsonl')
    lean_ready()
    lake('build', 'R3P10')

    def built(k):
        r = chunks_done.get(k)
        return r is not None and r['status'] == 'OK' and os.path.exists(olean(f'R3P10Cubes.C{k:03d}'))

    chunks_done = load_records(chunk_rec, 'chunk')
    cubes_done = load_records(cube_rec, 'cube')

    def have(i):
        r = cubes_done.get(i)
        p = os.path.join(CERTS, f'c{i:06d}.cert')
        return r is not None and r['result'] == 'CERT' and os.path.exists(p) and os.path.getsize(p) == r['cert_bytes']

    todo = sorted((k for k in want if not built(k)), key=lambda k: -plan[k]['est_cpu_s'])
    say(f'full check: {len(want)} chunks requested, {len(want) - len(todo)} already built, {len(todo)} to do')
    remaining = {k: {i for i in range(plan[k]['a'], plan[k]['b']) if not have(i)} for k in todo}
    ready, failed = [], []
    cv = threading.Condition()
    finished = threading.Event()

    def write_chunk(k):
        c = plan[k]
        with open(os.path.join(GEN, 'R3P10Cubes', f'C{k:03d}.lean'), 'w') as f:
            f.write(f'import R3P10.Base\n\n/-! Cubes {c["a"]} to {c["b"] - 1} of the final list (chunk {k}). -/\n\n'
                    'namespace R3P10.K18\n\n')
            for i in range(c['a'], c['b']):
                f.write(f'lrat_cube_c c{i} {i} "generated/certs/c{i:06d}.cert"\n')
            f.write(f'\ncube_range r{k} c {c["a"]} {c["b"]}\n\nend R3P10.K18\n')

    def lean_worker():
        while True:
            with cv:
                while not ready and not finished.is_set():
                    cv.wait()
                if not ready:
                    return
                batch = [ready.pop(0) for _ in range(min(args.lean_jobs, len(ready)))]
            mods = [f'R3P10Cubes.C{k:03d}' for k in batch]
            for k in batch:
                write_chunk(k)
            forget(*mods)
            t = time.time()
            r = lake('build', *mods, check=False)
            dt = round(time.time() - t, 1)
            for k, mod in zip(batch, mods):
                ok = r.returncode == 0 and os.path.exists(olean(mod))
                append(chunk_rec, {'chunk': k, 'status': 'OK' if ok else 'FAILED', 'lean_s': dt})
                if ok:
                    for i in range(plan[k]['a'], plan[k]['b']):
                        p = os.path.join(CERTS, f'c{i:06d}.cert')
                        if os.path.exists(p):
                            os.unlink(p)     # the olean holds the certificate now
                    say(f'chunk {k} (cubes {plan[k]["a"]}..{plan[k]["b"] - 1}): checked by Lean')
                else:
                    failed.append(f'chunk {k}')
                    say(f'chunk {k}: Lean FAILED\n' + '\n'.join((r.stdout + r.stderr).splitlines()[-30:]))

    def chunk_ready(k):
        with cv:
            ready.append(k)
            cv.notify()

    lw = threading.Thread(target=lean_worker)
    lw.start()
    for k in todo:
        if not remaining[k]:
            chunk_ready(k)
    owner = {i: k for k in todo for i in remaining[k]}
    order = [i for k in todo for i in sorted(remaining[k])]
    try:
        with ThreadPoolExecutor(max(1, args.jobs)) as pool:
            futs = {pool.submit(cube_job, tools, args, i, cubes[i], None, args.cross_check): i for i in order}
            for f in as_completed(futs):
                i = futs[f]
                try:
                    rec = f.result()
                except Exception as e:      # a failed check is reported, not hidden
                    rec = {'cube': i, 'result': 'ERROR', 'error': str(e)[-500:]}
                append(cube_rec, rec)
                if rec['result'] != 'CERT':
                    failed.append(f'cube {i}: {rec["result"]}')
                    say(f'cube {i}: {json.dumps(rec)}')
                    continue
                k = owner[i]
                with lock:
                    remaining[k].discard(i)
                    last = not remaining[k]
                if last:
                    chunk_ready(k)
    finally:
        finished.set()
        with cv:
            cv.notify()
        lw.join()
    need(not failed, 'failures: ' + '; '.join(failed[:20]))
    chunks_done = load_records(chunk_rec, 'chunk')
    missing = [k for k in sorted(plan) if not built(k)]
    if missing:
        say(f'{len(plan) - len(missing)} of {len(plan)} chunks built, {len(missing)} still to do; '
            'R3P10Final needs all of them.')
        return
    # all chunks: join the ranges, check the ladder, and build the main theorem
    write_all(plan.values())
    make_ladder_certs(tools, args, cross_check=args.cross_check)
    out = lake_build('R3P10Final', ['R3P10Ladder', 'R3P10Cubes', 'R3P10Final'])
    say(out.strip().splitlines()[-1])
    say('lake build R3P10Final: R3_P10_eq_18 : ramsey3Path 10 = 18, from every cube, the ladder and the '
        'cover, each checked by Lean\'s LRAT checker; axioms ' + AXIOMS5)
    say('PASS full check')


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n\n')[0])
    ap.add_argument('mode', choices=['quick', 'full'])
    ap.add_argument('--work', default=os.path.join(tempfile.gettempdir(), 'path-ramsey-work'),
                    help='work directory for the tools and temporaries (outside the bundle)')
    ap.add_argument('--jobs', type=int, default=len(os.sched_getaffinity(0)) if hasattr(os, 'sched_getaffinity')
                    else os.cpu_count() or 1, help='parallel solver jobs (default: all cores)')
    ap.add_argument('--threads', type=int, dest='jobs', help=argparse.SUPPRESS)
    ap.add_argument('--part', help='quick: run part K of N (e.g. 3/8)')
    ap.add_argument('--list', action='store_true', help='quick: list the steps (of --part)')
    ap.add_argument('--sample', type=int, default=8, help='quick: number of K_18 cubes to check (default 8)')
    ap.add_argument('--seed', type=int, help='quick: sample seed (default: random, printed)')
    ap.add_argument('--cube-timeout', type=float, default=300, help='quick: solve time limit per sampled cube')
    ap.add_argument('--lean-jobs', type=int, default=2, help='full: chunk modules per Lean build (memory: '
                    'up to about 7 GB each)')
    ap.add_argument('--chunks', help='full: only these chunks of data/chunks.json, e.g. 0-40,77')
    ap.add_argument('--cross-check', action='store_true',
                    help='full: also check every cube with check_paths, check_inputs and cake_lpr')
    args = ap.parse_args()
    args.work = os.path.abspath(args.work)
    need(not args.work.startswith(ROOT + os.sep), '--work must be outside the bundle')
    os.makedirs(args.work, exist_ok=True)
    (quick if args.mode == 'quick' else full)(args)


if __name__ == '__main__':
    try:
        main()
    except CheckFailed as e:
        sys.exit(f'FAIL {e}')
