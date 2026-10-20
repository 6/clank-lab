"""Audit a regenerated P6/P10/P16 Omega and reject a real-input two-root corruption.

Usage: python audit_omega.py INPUT_DIRECTORY --pmax 16 --out receipt.json
The generator inputs must match the current reproducible raw input hashes. Raw
generator outputs remain outside Git; this writes only a small receipt.
"""
import argparse
import collections
import copy
from decimal import Decimal
import hashlib
import json
from pathlib import Path
import sys
import tempfile

TARGET = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(TARGET / 'enum'))
from export_omega import project_intervals
from caseb_coinc import omega


def sha(blob):
    return hashlib.sha256(blob).hexdigest()


def audit(directory, p):
    names = [f'{stem}_p{p}.json' for stem in
             ('cert_facets4', 'cert_stage1_5d', 'exact_flat', 'exact_boundary')]
    pin_file = TARGET / 'verification-caseb-b2/runtime-inputs.json'
    pins = json.loads(pin_file.read_text())['raw_certificates']
    hashes = {}
    for name in names:
        hashes[name] = sha((directory / name).read_bytes())
        if hashes[name] != pins[f'p{p}/{name}']['sha256']:
            raise ValueError(f'current input mismatch: {name}')
    cycles, flat, boundary = [json.loads((directory / name).read_text())
                              for name in names[1:]]
    projected = project_intervals(cycles, flat, boundary, p)
    # The historical projection is rebuilt separately: it deleted whole
    # listed cycles and kept every other finite ROOT interval, preserving
    # endpoint text, duplicate multiplicities and stable Decimal sorting.
    excluded = set(flat['flat']) | set(boundary['degenerate'])
    historical = [(lo, hi, i) for i, r in enumerate(cycles)
                  if r['status'] == 'ROOT' and i not in excluded
                  for lo, hi in r['R'] if hi != 'inf']
    historical.sort(key=lambda row: Decimal(row[0]))
    frozen_bytes = json.dumps(dict(intervals=historical), indent=0).encode()
    current_bytes = json.dumps(dict(intervals=projected), indent=0).encode()
    if current_bytes != frozen_bytes:
        raise ValueError('Omega bytes changed from historical projection')
    name = f'u5_omega_p{p}.json'
    if (directory / name).read_bytes() != current_bytes:
        raise ValueError('exported file differs from audited projection')
    hashes[name] = sha(current_bytes)
    if p == 16 and hashes[name] != 'c7773fab6fff9110ea94b8c79debf887b3667396503e317ecd8cc54a3c89bc33':
        raise ValueError('P16 Omega differs from frozen B2 pin')
    if len(omega(directory, p)) != len(projected):
        raise ValueError('diagnostic loader differs in interval count')

    bad = copy.deepcopy(cycles)
    index = boundary['degenerate'][0]
    bad[index]['R'].append(list(projected[0][:2]))
    rejected = {}
    with tempfile.TemporaryDirectory() as tmp:
        corrupt_dir = Path(tmp)
        for n, data in zip(names[1:], (bad, flat, boundary)):
            (corrupt_dir / n).write_text(json.dumps(data))
        for label, call in [('exporter', lambda: project_intervals(bad, flat, boundary, p)),
                            ('diagnostic_loader', lambda: omega(corrupt_dir, p))]:
            try:
                call()
            except ValueError as exc:
                if 'exactly one certified root' not in str(exc):
                    raise
                rejected[label] = str(exc)
            else:
                raise ValueError(f'{label} silently removed a two-root cycle')
    return dict(pmax=p, cycles=len(cycles),
                statuses=dict(collections.Counter(r['status'] for r in cycles)),
                flat=len(flat['flat']), degenerate=len(boundary['degenerate']),
                degenerate_root_multiplicities=dict(collections.Counter(
                    len(cycles[i]['R']) for i in boundary['degenerate'])),
                omega_intervals=len(projected),
                historical_bytes_equal=True, diagnostic_loader_count_equal=True,
                two_root_corruption=dict(index=index, rejections=rejected),
                pin_manifest_sha256=sha(pin_file.read_bytes()), sha256=hashes)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path)
    parser.add_argument('--pmax', type=int, choices=(6, 10, 16), required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    result = audit(args.directory, args.pmax)
    args.out.write_text(json.dumps(result, indent=2) + '\n')
    print(f'PASS P{args.pmax}: {result["omega_intervals"]} unchanged intervals; both two-root corruptions rejected')
