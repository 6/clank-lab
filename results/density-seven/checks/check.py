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


def main():
    if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):
        raise SystemExit('proof checks require assertions: unset PYTHONOPTIMIZE and do not use -O')
    ap = argparse.ArgumentParser(description=__doc__)
    group = ap.add_mutually_exclusive_group(required=True)
    group.add_argument('--quick', action='store_true', help='audits plus small proof/corruption controls')
    group.add_argument('--full', action='store_true', help='audits and all 19 streaming proof replays')
    group.add_argument('--case', choices=[r['name'] for r in cases()], help='one SAT obligation only')
    ap.add_argument('--tools', type=Path, required=True, help='directory built with build_tools.py')
    ap.add_argument('--work', type=Path, required=True, help='new empty output directory outside this bundle')
    a = ap.parse_args()
    a.tools = a.tools.resolve()
    a.work = a.work.resolve()
    a.work.mkdir(parents=True, exist_ok=True)
    if any(a.work.iterdir()):
        ap.error('--work must be empty (each run is independent)')
    for tool in ('cadical', 'frat-rs', 'lrat-check', 'cake_lpr'):
        if not os.access(a.tools / tool, os.X_OK):
            ap.error('missing executable: ' + tool)
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
