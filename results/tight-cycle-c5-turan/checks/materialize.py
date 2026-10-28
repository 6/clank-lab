#!/usr/bin/env python3
"""Materialize the fixed proof and exact inputs; never invoke Lean or Lake."""
import argparse
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import tempfile
import sys
sys.dont_write_bytecode = True

ROOT = Path(__file__).resolve().parents[1]
MANIFEST_SHA256 = 'eabd015f56713789808e8f0ad49d23ca66192df36a6e5acd8ca339e0797c2332'


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def require(ok, message):
    if not ok:
        raise ValueError(message)


def record(raw, expected, label):
    require(len(raw) == expected['bytes'] and digest(raw) == expected['sha256'],
            'size/hash mismatch: ' + label)


def manifest():
    raw = (ROOT / 'checks/materialized-sources.json').read_bytes()
    require(digest(raw) == MANIFEST_SHA256, 'materialization manifest changed')
    return json.loads(raw)


def load_payload(name, spec):
    if 'members' in spec:
        result = {}
        for item in spec['members']:
            path = ROOT / item['file']
            require(not path.is_symlink(), 'linked source input')
            compressed = path.read_bytes()
            record(compressed, item, item['file'])
            raw = gzip.decompress(compressed)
            require(len(raw) == item['raw_bytes'] and digest(raw) == item['raw_sha256'],
                    'source input expansion changed')
            require(item['name'] not in result, 'duplicate stored source')
            result[item['name']] = raw.decode()
        return result
    parts = []
    for item in spec['parts']:
        path = ROOT / item['file']
        require(not path.is_symlink(), 'linked input')
        raw = path.read_bytes()
        record(raw, item, item['file'])
        parts.append(raw)
    compressed = b''.join(parts)
    require(digest(compressed) == spec['gzip_sha256'], 'compressed payload changed')
    raw = gzip.decompress(compressed)
    require(len(raw) == spec['json_bytes'] and digest(raw) == spec['json_sha256'],
            'payload bytes changed: ' + name)
    return json.loads(raw)


def recipe(name, item):
    path = ROOT / item['file']
    require(not path.is_symlink(), 'linked recipe')
    record(path.read_bytes(), item, name)
    spec = importlib.util.spec_from_file_location(name[:-3], path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def materialize(out=None, check=False):
    m = manifest()
    out = Path(out).resolve() if out is not None else ROOT
    for name, expected in m['stored_support'].items():
        path = ROOT / name
        require(not path.is_symlink(), 'linked checker')
        record(path.read_bytes(), expected, name)
    source = load_payload('lean-sources', m['payloads']['lean-sources'])
    cert = load_payload('certificates', m['payloads']['certificates'])
    for name, item in m['recipes'].items():
        generator = recipe(name, item)
        results = generator.sources(0, 634) if 'checkpoints' in name else generator.sources()
        for file, text in results.items():
            if not file.endswith('.lean'):
                continue
            module = file[:-5]
            if module in m['modules']:
                require(file not in source, 'duplicate generated module')
                require(m['modules'][module].get('recipe') == name, 'unexpected generator role')
                source[file] = text
    require(set(source) == {n + '.lean' for n in m['modules']}, 'source set changed')
    require(set(cert) == set(m['certificates']), 'certificate set changed')
    outputs = {}
    for name, text in source.items():
        require(re.fullmatch(r'[A-Za-z0-9_]+\.lean', name) is not None, 'unsafe module path')
        raw = text.encode()
        record(raw, m['modules'][name[:-5]], name)
        outputs['lean/' + name] = raw
    for name, text in cert.items():
        require(re.fullmatch(r'p(?:32|33-(?:1|3999))/[A-Za-z0-9_.-]+\.json', name) is not None,
                'unsafe certificate path')
        raw = text.encode()
        record(raw, m['certificates'][name], name)
        outputs['data/' + name] = raw
    # Fail closed on existing damage or extra proof/certificate modules before installation.
    present = {str(p.relative_to(out)) for base, pattern in [('lean', '*.lean'), ('data', '*/*.json')]
               for p in (out / base).glob(pattern)}
    support_proofs = {name for name in m['stored_support'] if name.startswith('lean/') and name.endswith('.lean')}
    require(present <= outputs.keys() | support_proofs, 'unexpected materialized proof or certificate')
    for name in support_proofs:
        path = out / name
        require(not path.is_symlink(), 'linked support proof')
        if path.exists():
            record(path.read_bytes(), m['stored_support'][name], name)
    for name in sorted(outputs):
        path = out / name
        require(not path.is_symlink(), 'linked output')
        if path.exists():
            require(path.is_file() and path.read_bytes() == outputs[name], 'changed output: ' + name)
        elif check:
            raise ValueError('missing output: ' + name)
    if not check:
        for name, raw in sorted(outputs.items()):
            path = out / name
            if path.exists():
                continue
            path.parent.mkdir(parents=True, exist_ok=True)
            # Per-file atomic installation, resumable by rerunning the same command.
            with tempfile.NamedTemporaryFile(dir=path.parent, prefix='.materialize-', delete=False) as f:
                f.write(raw)
                temporary = Path(f.name)
            temporary.replace(path)
    return {'status': 'PASS_MATERIALIZATION_SOURCE_CHECK', 'Lean_compilation': False,
            'modules': len(source), 'certificates': len(cert),
            'source_bytes': sum(len(v.encode()) for v in source.values()),
            'certificate_bytes': sum(len(v.encode()) for v in cert.values())}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--out', type=Path, help='alternate materialized tree, for source controls')
    p.add_argument('--check', action='store_true', help='require existing complete matching outputs')
    a = p.parse_args()
    print(json.dumps(materialize(a.out, a.check), sort_keys=True))


if __name__ == '__main__':
    main()
