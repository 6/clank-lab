#!/usr/bin/env python3
"""Materialize frozen generated Lean bytes, with no Lean/Lake invocation.

Run before computing build/checkpoint source signatures or reading Lake imports.
Existing files are checked, never silently repaired. Delete a damaged generated
file explicitly before retrying. Only public certificates/inputs are consumed.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / 'checks/generated-kernel-sha256.json'
MANIFEST_SHA256 = '005e09c6970964f6fbf0ec9cc5509da1050e23643eec761c61b40ae8ae0dddd5'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require_file(path, record):
    if not path.is_file() or path.is_symlink():
        raise ValueError(f'missing or nonregular file: {path}')
    if path.stat().st_size != record['bytes'] or digest(path) != record['sha256']:
        raise ValueError(f'SHA256/size mismatch: {path}')


def load_manifest():
    if digest(MANIFEST) != MANIFEST_SHA256:
        raise ValueError('generated manifest SHA256 mismatch')
    return json.loads(MANIFEST.read_text(encoding='utf-8'))


def generated_paths(directory):
    return {p.name for pattern in ('SourceKernel*.lean', 'ControlKernel*.lean')
            for p in directory.glob(pattern)}


def bootstrap(scope='all', out=None, check=False):
    if scope not in ('control', 'all'):
        raise ValueError(f'unknown scope: {scope}')
    manifest = load_manifest()
    # Authenticate every input and recipe before generating or accepting outputs.
    for name, record in manifest['inputs'].items():
        require_file(ROOT / name, record)
    for name, record in manifest['recipes'].items():
        require_file(ROOT / name, record)
    out = Path(out) if out is not None else ROOT / 'lean'
    expected = manifest['generated']
    selected = {n: r for n, r in expected.items()
                if scope == 'all' or n.startswith('ControlKernel')}
    present = generated_paths(out)
    extra = present - expected.keys()
    if extra:
        raise ValueError(f'unexpected generated files: {sorted(extra)}')
    # Check even unselected existing modules: quickcheck must not hash stale bytes.
    for name in sorted(present):
        require_file(out / name, expected[name])
    missing = selected.keys() - present
    if check and missing:
        raise ValueError(f'missing generated files: {sorted(missing)}')
    if missing:
        with tempfile.TemporaryDirectory(prefix='adkz-kernel-') as tmp:
            tmp = Path(tmp)
            for kind, prefix, chunk, inp in (
                    ('control', 'ControlKernel', 4, 'lp-control-bounded-rank4-input.json'),
                    ('msw', 'SourceKernel', 64, 'msw-input.json')):
                names = {n for n in selected if n.startswith(prefix)}
                if not names.intersection(missing):
                    continue
                cert = ROOT / 'data/control-certificate.json.gz'
                if kind == 'msw':
                    cert = tmp / 'source-certificate.json.gz'
                    cert.write_bytes(b''.join((ROOT / n).read_bytes() for n in
                        ('data/source-certificate.json.gz.part00',
                         'data/source-certificate.json.gz.part01')))
                ordinary, prepared = tmp / kind, tmp / (kind + '-kernel')
                cmd = [sys.executable, str(ROOT / 'checks/generate_source_kernel.py'),
                       '--certificate', str(cert), '--input', str(ROOT / 'data' / inp),
                       '--kind', kind, '--chunk', str(chunk), '--out', str(ordinary)]
                if kind == 'msw':
                    cmd += ['--chart', str(ROOT / 'data/chart.json')]
                subprocess.run(cmd, check=True, stdout=subprocess.DEVNULL)
                subprocess.run([sys.executable, str(ROOT / 'checks/prepare_kernel.py'),
                    '--generated', str(ordinary), '--out', str(prepared),
                    '--public-export'], check=True)
                if generated_paths(prepared) != names:
                    raise ValueError(f'generator output set mismatch: {kind}')
                # Validate the entire generated scope before installing any of it.
                for name in sorted(names):
                    require_file(prepared / name, selected[name])
            out.mkdir(parents=True, exist_ok=True)
            for name in sorted(missing):
                prepared = tmp / ('control-kernel' if name.startswith('Control')
                                  else 'msw-kernel')
                # Exclusive creation avoids replacing files introduced concurrently.
                with (out / name).open('xb') as target:
                    target.write((prepared / name).read_bytes())
    for name, record in selected.items():
        require_file(out / name, record)
    return {'scope': scope, 'verified_files': len(selected),
            'verified_bytes': sum(r['bytes'] for r in selected.values()),
            'generated_files': len(missing), 'lean_build_run': False}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--scope', choices=('all', 'control'), default='all')
    ap.add_argument('--out', type=Path, help='default: the bundle lean/ directory')
    ap.add_argument('--check', action='store_true', help='verify only; reject missing files')
    args = ap.parse_args()
    try:
        print(json.dumps(bootstrap(args.scope, args.out, args.check), sort_keys=True))
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        print(f'kernel bootstrap failed: {error}', file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
