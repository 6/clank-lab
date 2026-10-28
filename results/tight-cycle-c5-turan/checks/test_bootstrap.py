#!/usr/bin/env python3
"""Storage/recipe corruption controls only; no compiler or SDP check."""
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import sys
import tempfile
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]


def load(root):
    spec = importlib.util.spec_from_file_location('materialization', root / 'checks/materialize.py')
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


def rejected(action):
    try:
        action()
    except (ValueError, FileNotFoundError):
        return
    raise AssertionError('planted storage/recipe defect was accepted')


def main():
    tests = []
    with tempfile.TemporaryDirectory(prefix='c5-bootstrap-') as tmp:
        tmp = Path(tmp)
        src, out = tmp / 'package', tmp / 'outputs'
        shutil.copytree(ROOT, src, ignore=shutil.ignore_patterns('__pycache__', '*.pyc'))
        m = load(src)
        result = m.materialize(out)
        m.materialize(out, check=True)
        tests.extend(['clean materialization', 'existing complete tree'])
        proof = out / 'lean/P33ReplayEndpoint.lean'
        original = proof.read_bytes()
        proof.write_bytes(original + b'\n')
        rejected(lambda: m.materialize(out)); rejected(lambda: m.materialize(out, check=True))
        proof.write_bytes(original); tests.append('changed existing proof fails closed')
        proof.unlink(); rejected(lambda: m.materialize(out, check=True)); m.materialize(out)
        assert proof.read_bytes() == original
        tests.append('missing proof detected; regeneration exact')
        extra = out / 'lean/Unexpected.lean'; extra.write_text('')
        rejected(lambda: m.materialize(out)); extra.unlink(); tests.append('extra proof rejected')
        proof.unlink(); proof.symlink_to(out / 'lean/FinalAcceptance.lean')
        rejected(lambda: m.materialize(out)); proof.unlink(); m.materialize(out)
        tests.append('linked proof rejected')
        adapter = out / 'lean/PublicGuard.lean'
        adapter.write_bytes((src / 'lean/PublicGuard.lean').read_bytes())
        m.materialize(out, check=True)
        adapter.write_bytes(adapter.read_bytes() + b'\n')
        rejected(lambda: m.materialize(out, check=True))
        adapter.unlink()
        tests.append('changed alternate-tree guard adapter rejected')
        manifest = m.manifest()
        targets = [manifest['payloads']['lean-sources']['members'][0]['file'],
                   manifest['payloads']['certificates']['parts'][0]['file'],
                   next(iter(manifest['recipes'].values()))['file'],
                   'checks/materialized-sources.json', 'checks/guard_endpoint.py',
                   'lean/lakefile.toml', 'lean/lean-toolchain',
                   'lean/PublicGuard.lean', 'checks/generate_public_guard.py']
        for target in targets:
            p = src / target; raw = p.read_bytes(); p.write_bytes(raw + b'\n')
            rejected(lambda: m.materialize(out))
            p.write_bytes(raw); tests.append('changed input rejected: ' + target)
        m.materialize(out, check=True)
    print(json.dumps({'status': 'PASS_BOOTSTRAP_CONTROLS', 'Lean_compilation': False,
                      'semantic_certificate_check': False, 'controls': tests,
                      'materialized': result}, sort_keys=True))


if __name__ == '__main__':
    main()
