#!/usr/bin/env python3
"""Check the graph, encoding, certificates, and rejection controls.

No solver or search implementation is imported. Downloads are restricted
to the pinned checker dependencies in requirements.txt.
"""
import hashlib
import lzma
import platform
from pathlib import Path
import subprocess
import tempfile
import sys
import urllib.request

sys.dont_write_bytecode = True

from semantics import check, exact_graph, load, require, witnesses, Reject

ROOT = Path(__file__).resolve().parents[1]


def execute(command):
    proc = subprocess.run([str(x) for x in command], stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT, text=True, timeout=540)
    return proc.returncode, proc.stdout


def build(work):
    arch = platform.machine().lower()
    require(arch in ('x86_64', 'amd64', 'aarch64', 'arm64'), 'unsupported architecture')
    assembly = 'cake_lpr_arm8.S' if arch in ('aarch64', 'arm64') else 'cake_lpr.S'
    for line in (ROOT / 'checks/requirements.txt').read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        name, url, digest = line.split()
        if name.endswith('.S') and name != assembly:
            continue
        with urllib.request.urlopen(url, timeout=60) as response:
            data = response.read()
        require(hashlib.sha256(data).hexdigest() == digest, 'dependency digest: ' + name)
        (work / name).write_bytes(data)
    for command in (
        ['gcc', '-O2', work / 'drat-trim.c', '-o', work / 'drat-trim'],
        ['gcc', '-std=c99', work / assembly, work / 'basis_ffi.c', '-o', work / 'cake_lpr'],
    ):
        code, output = execute(command)
        require(code == 0, 'checker compilation failed: ' + output)


def proof(work, kind, cnf, certificate, output=None):
    if kind == 'drat':
        command = [work / 'drat-trim', cnf, certificate]
        if output is not None:
            command += ['-L', output]
        marker = 's VERIFIED'
    else:
        command = [work / 'cake_lpr', '--CML_HEAP_SIZE=1024', '--CML_STACK_SIZE=128',
                   cnf, certificate]
        marker = 's VERIFIED UNSAT'
    code, text = execute(command)
    return code == 0 and marker in text.splitlines(), code, text


def reject_truncated(work, kind, cnf, certificate):
    # Stop after the first added nonempty clause. No final contradiction remains.
    lines = []
    index = 0 if kind == 'drat' else 1
    for line in certificate.read_text().splitlines(keepends=True):
        lines.append(line)
        fields = line.split()
        if len(fields) > index and fields[index] not in ('d', '0'):
            break
    broken = work / ('truncated.' + kind)
    broken.write_text(''.join(lines))
    accepted, code, text = proof(work, kind, cnf, broken)
    if kind == 'drat':
        intended = code == 1 and 's NOT VERIFIED' in text.splitlines() and any(
            reason in text for reason in ('failed at proof line',
                'conflict claimed, but not detected', 'ERROR: no conflict'))
    else:
        intended = code == 0 and 'empty clause not derived at end of proof' in text
    require(not accepted and intended, 'truncated certificate did not fail as intended')


def semantic_corruptions():
    graph = load(ROOT / 'data/graph.json')
    edges, _ = exact_graph(graph)
    graph['edges'].pop()
    try:
        exact_graph(graph)
    except Reject as exc:
        require(str(exc) == 'graph: exact adjacency', 'unexpected graph rejection')
    else:
        raise Reject('deleted edge accepted')
    paths = load(ROOT / 'data/paths.json')
    paths[0]['path'] = [paths[0]['path'][0]] * 3
    try:
        witnesses(paths, edges)
    except Reject as exc:
        require(str(exc) == 'path: vertex distinctness/range', 'unexpected path rejection')
    else:
        raise Reject('non-path accepted')


def main():
    checked = check(ROOT)
    require(checked['status'] == 'PASS', 'semantic checks failed')
    semantic_corruptions()
    print('PASS graph, 775 induced-path witnesses, six formulas, catalogues and controls', flush=True)
    with tempfile.TemporaryDirectory(prefix='monophonic-check-') as directory:
        work = Path(directory)
        build(work)
        for name in ('h-catalogue', 'complement-catalogue', 'h7', 'complement14'):
            cnf = ROOT / 'data' / (name + '.cnf')
            drat = ROOT / 'data' / (name + '.drat')
            if name == 'h7':
                drat = work / 'h7.drat'
                drat.write_bytes(lzma.decompress((ROOT / 'data/h7.drat.xz').read_bytes()))
            lrat = work / (name + '.lrat')
            require(proof(work, 'drat', cnf, drat, lrat)[0], name + ': DRAT rejected')
            require(proof(work, 'lrat', cnf, lrat)[0], name + ': LRAT rejected')
            reject_truncated(work, 'drat', cnf, drat)
            reject_truncated(work, 'lrat', cnf, lrat)
            print('PASS ' + name + ': both checkers and both truncation controls', flush=True)
    print('PASS: chi_mp_i(H) >= 8; chi_mp_i(complement H) >= 15; sum >= 23 > 22')


if __name__ == '__main__':
    main()
