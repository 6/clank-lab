"""Check package inventory; authenticate only scientific inputs and checkers."""
import hashlib
import json
from pathlib import Path, PurePosixPath


def check(root):
    names = (root / 'checks/PUBLIC.txt').read_text().splitlines()
    if names != sorted(set(names)):
        raise ValueError('PUBLIC.txt must be sorted and contain no duplicates')
    for name in names:
        p = PurePosixPath(name)
        if not name or p.is_absolute() or '..' in p.parts or str(p) != name:
            raise ValueError('unsafe public path')
        path = root / name
        if path.is_symlink() or not path.is_file() or path.stat().st_size > 5_000_000:
            raise ValueError('missing, linked or oversized public file: ' + name)
    expected = {}
    for line in (root / 'data/PUBLIC.sha256').read_text().splitlines():
        digest, name = line.split('  ', 1)
        if name in expected:
            raise ValueError('duplicate digest')
        expected[name] = digest
    scope = json.loads((root / 'data/acceptance-inputs.json').read_text())
    if set(scope) != {'certificates', 'authoritative_inputs', 'checkers'}:
        raise ValueError('invalid scientific pin categories')
    pinned = [name for category in scope.values() for name in category]
    if len(set(pinned)) != len(pinned) or not set(pinned) <= set(names):
        raise ValueError('duplicate or unlisted scientific pin')
    if any(Path(name).suffix in {'.md', '.tex', '.pdf', '.rst'} for name in pinned):
        raise ValueError('prose cannot be an acceptance pin')
    if set(expected) != set(pinned):
        raise ValueError('digest inventory differs from scientific scope')
    for name, digest in expected.items():
        if hashlib.sha256((root / name).read_bytes()).hexdigest() != digest:
            raise ValueError('public file hash mismatch: ' + name)
    print(f'PASS public inventory ({len(names)} files), scientific pins ({len(pinned)} files)')


if __name__ == '__main__':
    check(Path(__file__).resolve().parent.parent)
