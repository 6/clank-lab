#!/usr/bin/env python3
"""Check the mathematical source inventory and its checking-guide binding."""
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--guide', type=Path)
    args = ap.parse_args()
    manifest = ROOT / 'checks/proof-sources.json'
    digest = hashlib.sha256(manifest.read_bytes()).hexdigest()
    data = json.loads(manifest.read_text())
    assert data['format'] == 1
    for name, expected in data['sha256'].items():
        relative = Path(name)
        assert not relative.is_absolute() and '..' not in relative.parts
        path = ROOT / relative
        assert path.is_file() and not path.is_symlink(), name
        assert hashlib.sha256(path.read_bytes()).hexdigest() == expected, name
    if args.guide:
        assert ('`' + digest + '`') in args.guide.read_text(), 'checking-guide inventory hash differs'
    print(json.dumps({'accepted': True, 'files': len(data['sha256']),
                      'manifest_sha256': digest,
                      'generated_lean': 'Pinned separately by the included generated-kernel-sha256.json; materialize with bootstrap_kernel.py'}))

if __name__ == '__main__':
    main()
