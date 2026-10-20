"""Single entry point for quick audits or full streaming proof verification."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import threading

sys.dont_write_bytecode = True

HERE = Path(__file__).resolve().parent
DATA = HERE.parent / 'data'


def run_python(script, *args, expected=True):
    result = subprocess.run([sys.executable, str(HERE / script), *map(str, args)])
    if (result.returncode == 0) != expected:
        raise RuntimeError('unexpected result: ' + script)


def cases():
    rows = json.loads((DATA / 'cases.json').read_text())
    expected = [('L1', ['1', '3']), ('L4', ['4', '53', '--caps', '2,6,18']),
                ('L5', ['5', '151', '--caps', '2,6,18,52'])]
    expected += [('k1303_s' + str(s), ['7', '1303', '--caps', '2,6,18,52,150,450', '--s0', str(s)])
                 for s in range(450, 434, -1)]
    if [(r['name'], r['args']) for r in rows] != expected:
        raise RuntimeError('case list does not match the theorem')
    return rows


def encode(row, path):
    subprocess.run([sys.executable, str(HERE / 'encode.py'), *row['args'], '-o', str(path)], check=True)


def checker_commands(tools, cnf, proof, cake):
    result = [('frat-rs', [str(tools / 'frat-rs'), 'lratchk', str(cnf), str(proof)]),
              ('lrat-check', [str(tools / 'lrat-check'), str(cnf), str(proof)])]
    if cake:
        result.append(('cake_lpr', [str(tools / 'cake_lpr'), '--CML_HEAP_SIZE=5000',
                                    '--CML_STACK_SIZE=1024', str(cnf), str(proof)]))
    return result


def accepted(name, rc, log):
    s = log.read_text(errors='replace')
    return rc == 0 and (name == 'frat-rs' or
                       ('s VERIFIED UNSAT' in s if name == 'cake_lpr' else 'c VERIFIED' in s))


def proof_controls(tools, work):
    row = cases()[2]
    cnf, proof = work / 'control.cnf', work / 'control.lrat'
    encode(row, cnf)
    rc = subprocess.run([str(tools / 'cadical'), '-q', '--lrat=true', '--binary=false', str(cnf), str(proof)],
                        stdout=subprocess.DEVNULL).returncode
    if rc != 20:
        raise RuntimeError('control solver did not return UNSAT')
    original = proof.read_text().splitlines(keepends=True)
    controls = {'valid': original}
    for mode in ('literal', 'hint'):
        lines = list(original)
        for i, line in enumerate(lines):
            f = line.split()
            if len(f) > 2 and f[1] != 'd':
                z = f.index('0', 1)
                if mode == 'literal' and z >= 3:
                    f[1] = str(-int(f[1]))
                elif mode == 'hint' and len(f[z + 1:-1]) >= 2:
                    del f[z + 1]
                else:
                    continue
                lines[i] = ' '.join(f) + '\n'
                break
        else:
            raise RuntimeError('no suitable corruption point')
        controls[mode] = lines
    controls['truncated'] = []
    for mode, lines in controls.items():
        altered = work / (mode + '.lrat')
        altered.write_text(''.join(lines))
        for name, cmd in checker_commands(tools, cnf, altered, True):
            log = work / (mode + '-' + name + '.log')
            with log.open('w') as f:
                rc = subprocess.run(cmd, stdout=f, stderr=subprocess.STDOUT).returncode
            ok = accepted(name, rc, log)
            if ok != (mode == 'valid'):
                raise RuntimeError('proof control failed: ' + mode + ' ' + name)
    print('PASS L5 valid proof and literal/hint/truncation controls: all three checkers', flush=True)


def stream_case(row, tools, work):
    directory = work / row['name']
    directory.mkdir()
    # Audit and replay the very same file, with no regeneration between.
    import reduction
    record = next(r for r in reduction.receipts() if r['name'] == row['name'])
    n = record['n']
    reduction.LINES[n] = set(reduction.Cube(n, {}).lines())
    result = reduction.audit(record, {1: 3, 4: 53, 5: 151}, str(directory), keep_cnf=True)
    if not result['ok']:
        raise RuntimeError('semantic audit failed: ' + row['name'])
    cnf = directory / (row['name'] + '.cnf')
    # Each checker receives the same bytes through its own FIFO. A checker
    # may stop at the empty clause; its closed pipe is then simply drained.
    cake = row['name'].startswith('L') or int(row['name'][-3:]) >= 443
    solver_fifo = directory / 'solver.fifo'
    os.mkfifo(solver_fifo)
    processes = []
    destinations = []
    opened = []
    for name, cmd in checker_commands(tools, cnf, directory / 'unused', cake):
        fifo = directory / (name + '.fifo')
        os.mkfifo(fifo)
        cmd[-1] = str(fifo)
        log = directory / (name + '.log')
        handle = log.open('w')
        opened.append(handle)
        processes.append((name, subprocess.Popen(cmd, stdout=handle, stderr=subprocess.STDOUT), log))
        destinations.append(fifo)
    errors = []
    byte_count = [0]

    def relay():
        sinks = []
        try:
            with solver_fifo.open('rb', buffering=0) as source:
                sinks = [p.open('wb', buffering=0) for p in destinations]
                while True:
                    block = source.read(1 << 20)
                    if not block:
                        break
                    byte_count[0] += len(block)
                    for sink in list(sinks):
                        try:
                            view = memoryview(block)
                            while view:
                                count = sink.write(view)
                                view = view[count:]
                        except BrokenPipeError:
                            sink.close()
                            sinks.remove(sink)
        except BaseException as e:
            errors.append(repr(e))
        finally:
            for sink in sinks:
                sink.close()

    thread = threading.Thread(target=relay, daemon=True)
    thread.start()
    with (directory / 'solver.log').open('w') as log:
        solver = subprocess.Popen([str(tools / 'cadical'), '-q', '--lrat=true', '--binary=false',
                                   str(cnf), str(solver_fifo)], stdout=log, stderr=subprocess.STDOUT)
        rc = solver.wait()
    if rc != 20:
        for name, proc, log in processes:
            proc.terminate()
        raise RuntimeError('solver failed; inspect solver.log (exit ' + str(rc) + ')')
    thread.join()
    verdicts = {name: accepted(name, proc.wait(), log) for name, proc, log in processes}
    for handle in opened:
        handle.close()
    if errors or rc != 20 or not all(verdicts.values()):
        raise RuntimeError('proof failed: ' + row['name'] + ' ' + repr((errors, rc, verdicts)))
    for fifo in directory.glob('*.fifo'):
        fifo.unlink()
    cnf.unlink()
    result = dict(case=row['name'], accepted=True, checkers=verdicts, proof_bytes=byte_count[0])
    temporary = directory / 'result.tmp'
    temporary.write_text(json.dumps(result) + '\n')
    temporary.replace(directory / 'result.json')
    print('PASS', row['name'], verdicts, byte_count[0], 'proof bytes streamed', flush=True)


def quick_audits(work):
    cases()
    run_python('symmetry.py')
    run_python('reduction.py', work / 'reduction.json')
    for script in ('witness.py', 'witness_independent.py'):
        run_python(script, DATA / 'line-free-1302.txt', 7, 1302)
        points = [p for p in (DATA / 'line-free-1302.txt').read_text().splitlines() if p and not p.startswith('#')]
        for label, altered in [('drop', points[:-1]), ('line', ['1111111'] + points[1:])]:
            path = work / (label + '.txt')
            path.write_text('\n'.join(altered) + '\n')
            run_python(script, path, 7, 1302, expected=False)
    print('PASS quick reduction, symmetry and witness audits; no main SAT proofs replayed', flush=True)


def reduction_steps(work):
    """reduction.py's audits as independent steps, for --part.

    They mirror its main(): lemmas in order of dimension, each audited with
    the lemmas before it; the main cases with all three; the cover; and the
    four controls, each of which must be rejected. Its whole run is the
    `reduction` step.
    """
    import reduction
    recs = reduction.receipts()
    lemma_rows = sorted((r for r in recs if r['s0'] is None), key=lambda r: r['n'])
    main_rows = sorted((r for r in recs if r['s0'] is not None), key=lambda r: -r['s0'])
    lemmas = {r['n']: r['K'] for r in lemma_rows}

    def lines():
        for n in sorted({r['n'] for r in recs}):
            if n not in reduction.LINES:
                reduction.LINES[n] = set(reduction.Cube(n, {}).lines())
                assert len(reduction.LINES[n]) == 4 ** n - 3 ** n

    def audit(rec, proved, label, expect_ok=True, **kw):
        lines()
        directory = work / ('reduction-' + label.replace(' ', '-'))
        directory.mkdir()
        result = reduction.audit(rec, dict(proved), str(directory), **kw)
        if result['ok'] != expect_ok:
            raise RuntimeError(('semantic audit failed: ' if expect_ok else 'control not rejected: ') + label)
        print(label, 'ok' if expect_ok else 'rejected', flush=True)

    def cover():
        n, K = 7, main_rows[0]['K']
        if not all(r['n'] == n and r['K'] == K for r in main_rows):
            raise RuntimeError('main cases differ in dimension or size')
        c6 = reduction.proved_table(lemmas, n)[6]
        need = [s for s in range(0, c6 + 1) if 3 * s >= K]
        if sorted(r['s0'] for r in main_rows) != need:
            raise RuntimeError('main cases do not cover s0 = %d..%d' % (need[0], need[-1]))
        print('cover ok: s0 = %d..%d' % (need[0], need[-1]), flush=True)

    def drop_first_line(path):
        with open(path) as f:
            hdr = f.readline().split()
            body = f.readlines()
        del body[0]
        with open(path, 'w') as f:
            f.write('p cnf %s %d\n' % (hdr[2], len(body)))
            f.writelines(body)

    s440 = next(r for r in main_rows if r['s0'] == 440)
    L5 = next(r for r in lemma_rows if r['n'] == 5)
    steps = []
    for i, r in enumerate(lemma_rows):
        before = {x['n']: x['K'] for x in lemma_rows[:i]}
        steps.append(('reduction-' + r['name'], 1, lambda r=r, before=before: audit(r, before, r['name'])))
    for r in main_rows:
        steps.append(('reduction-' + r['name'], 12, lambda r=r: audit(r, lemmas, r['name'])))
    steps.append(('reduction-cover', 1, cover))
    steps += [
        ('reduction-control-drop-line', 12, lambda: audit(
            s440, lemmas, 'drop-line s440', False, cnf_override=drop_first_line)),
        ('reduction-control-cap-loose', 1, lambda: audit(
            L5, {1: 3, 4: 54}, 'cap-loose L5 audited with c_4 <= 53', False)),
        ('reduction-control-s0-shift', 12, lambda: audit(
            s440, lemmas, 's0-shift s440 audited as s0 = 441', False, as_s0=441)),
        ('reduction-control-K-low', 12, lambda: audit(
            s440, lemmas, 'K-low s440 audited as K = 1302', False, as_K=1302)),
    ]
    return steps


def witness_step(script, work):
    def run():
        run_python(script, DATA / 'line-free-1302.txt', 7, 1302)
        points = [p for p in (DATA / 'line-free-1302.txt').read_text().splitlines() if p and not p.startswith('#')]
        for label, altered in [('drop', points[:-1]), ('line', ['1111111'] + points[1:])]:
            path = work / (script + '-' + label + '.txt')
            path.write_text('\n'.join(altered) + '\n')
            run_python(script, path, 7, 1302, expected=False)
    return run


# Wall seconds of each full-mode obligation in the accepted independent replay.
CASE_SECONDS = {'L1': 1, 'L4': 1, 'L5': 1, 'k1303_s450': 78, 'k1303_s449': 428, 'k1303_s448': 736,
                'k1303_s447': 1371, 'k1303_s446': 1927, 'k1303_s445': 2686, 'k1303_s444': 3575,
                'k1303_s443': 4533, 'k1303_s442': 6678, 'k1303_s441': 11349, 'k1303_s440': 19414,
                'k1303_s439': 23986, 'k1303_s438': 28409, 'k1303_s437': 37433, 'k1303_s436': 39081,
                'k1303_s435': 76928}


TOOL_STEPS = {'proof-controls'}


def plan(full, tools, work):
    """Every independent step of a quick (or full) run, in order, with its
    rough time in seconds on a two-core GitHub-hosted runner."""
    steps = [('symmetry', 1, lambda: run_python('symmetry.py'))]
    steps += reduction_steps(work)
    steps += [('witness', 1, witness_step('witness.py', work)),
              ('witness-independent', 1, witness_step('witness_independent.py', work)),
              ('proof-controls', 2, lambda: proof_controls(tools, work))]
    if full:
        steps += [('case-' + r['name'], CASE_SECONDS[r['name']], lambda r=r: stream_case(r, tools, work))
                  for r in cases()]
    return steps


def share(steps, k, n):
    """Part k of n: longest steps first, each to the part with the least time
    so far; returned in run order."""
    load = [0] * (n + 1)
    owner = {}
    for i in sorted(range(len(steps)), key=lambda i: (-steps[i][1], i)):
        best = min(range(1, n + 1), key=lambda p: (load[p], p))
        owner[i] = best
        load[best] += steps[i][1]
    return [step for i, step in enumerate(steps) if owner[i] == k]


def part_arg(text):
    try:
        k, n = (int(x) for x in text.split('/'))
    except ValueError:
        raise argparse.ArgumentTypeError('expected K/N, such as 3/8')
    if not 1 <= k <= n:
        raise argparse.ArgumentTypeError('expected 1 <= K <= N')
    return k, n


def main():
    if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):
        raise SystemExit('proof checks require assertions: unset PYTHONOPTIMIZE and do not use -O')
    ap = argparse.ArgumentParser(description=__doc__)
    group = ap.add_mutually_exclusive_group(required=True)
    group.add_argument('--quick', action='store_true', help='audits plus small proof/corruption controls')
    group.add_argument('--full', action='store_true', help='audits and all 19 streaming proof replays')
    group.add_argument('--case', choices=[r['name'] for r in cases()], help='one SAT obligation only')
    ap.add_argument('--part', type=part_arg, metavar='K/N',
                    help='with --quick or --full, run only share K of N of the independent steps')
    ap.add_argument('--list', action='store_true', help="print the steps --part would run, and stop")
    ap.add_argument('--tools', type=Path, help='directory built with build_tools.py (a part with no proof step needs none)')
    ap.add_argument('--work', type=Path, help='new empty output directory outside this bundle')
    a = ap.parse_args()
    if a.case and (a.part or a.list):
        ap.error('--part and --list go with --quick or --full')
    if a.list:
        k, n = a.part or (1, 1)
        for name, _, _ in share(plan(a.full, None, None), k, n):
            print(name)
        return
    # A part with no proof step needs no tools.
    needs_tools = not a.part or any(name in TOOL_STEPS or name.startswith('case-')
                                    for name, _, _ in share(plan(a.full, None, None), *a.part))
    if a.work is None or (needs_tools and a.tools is None):
        ap.error('--work is required, and --tools for any proof step')
    a.work = a.work.resolve()
    a.work.mkdir(parents=True, exist_ok=True)
    if any(a.work.iterdir()):
        ap.error('--work must be empty (each run is independent)')
    if needs_tools:
        a.tools = a.tools.resolve()
        for tool in ('cadical', 'frat-rs', 'lrat-check', 'cake_lpr'):
            if not os.access(a.tools / tool, os.X_OK):
                ap.error('missing executable: ' + tool)
    if a.part:
        k, n = a.part
        mine = share(plan(a.full, a.tools, a.work), k, n)
        for name, _, run in mine:
            print('==', name, flush=True)
            run()
        print('PASS PART %d/%d ONLY: %s; every part from 1/%d to %d/%d must pass'
              % (k, n, ' '.join(name for name, _, _ in mine) or 'no steps', n, n, n))
        if not a.full:
            print('PASS QUICK ONLY: the full upper-bound proof requires --full')
        return
    if not a.case:
        quick_audits(a.work)
        proof_controls(a.tools, a.work)
    if a.full or a.case:
        rows = cases() if a.full else [r for r in cases() if r['name'] == a.case]
        for row in rows:
            stream_case(row, a.tools, a.work)
        print('PASS full theorem computation (19 UNSAT obligations)' if a.full else 'PASS single obligation only')
    else:
        print('PASS QUICK ONLY: the full upper-bound proof requires --full')


if __name__ == '__main__':
    main()
