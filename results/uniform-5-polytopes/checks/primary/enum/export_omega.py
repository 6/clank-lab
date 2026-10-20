"""Export authenticated, unfiltered stage-1 roots for B2.

Run after cert_stage1_5d.py 16 and exact_angles.py 16. Decimal endpoint
strings and original cycle indices are preserved. The stable byte layout uses Decimal lower-endpoint sorting,
json indent=0, and no trailing newline. No closure-filter input is used.
"""
import argparse
from decimal import Decimal, InvalidOperation
import hashlib
import json
from pathlib import Path


def project_intervals(cycles, flat, boundary, pmax=16):
    """Keep every ROOT interval except the two exact exclusion lists.

    An undecided cycle or surviving infinite interval is an error, never an
    interval silently omitted from the completeness input to B2.
    """
    if flat['pmax'] != pmax or boundary['pmax'] != pmax:
        raise ValueError(f'expected P{pmax} exclusions')
    if flat['failed'] or boundary['unhandled']:
        raise ValueError('incomplete exact exclusions')
    flat_ids = set(flat['flat'])
    degenerate_ids = set(boundary['degenerate'])
    excluded = flat_ids | degenerate_ids
    if any(type(i) is not int or not 0 <= i < len(cycles) for i in excluded):
        raise ValueError('exclusion index out of range')
    if flat_ids & degenerate_ids:
        raise ValueError('flat and degenerate exclusions overlap')
    # The boundary certificate identifies a root, not an entire cycle.
    # Whole-cycle deletion is justified only by one certified ROOT interval.
    # Check before skipping exclusions, including malformed/empty records.
    for i in degenerate_ids:
        record = cycles[i]
        if record['status'] != 'ROOT' or len(record['R']) != 1:
            raise ValueError(f'cycle {i}: degenerate exclusion requires exactly one certified root interval')
        _validated_interval(*record['R'][0], i)
    intervals = []
    for i, record in enumerate(cycles):
        status = record['status']
        if status not in ('ROOT', 'NOROOT'):
            raise ValueError(f'cycle {i}: unresolved status {status}')
        if status != 'ROOT' or i in excluded:
            continue
        if not record['R']:
            raise ValueError(f'cycle {i}: ROOT without intervals')
        for lo, hi in record['R']:
            _validated_interval(lo, hi, i)
            intervals.append((lo, hi, i))
    if not intervals:
        raise ValueError('empty Omega')
    intervals.sort(key=lambda row: Decimal(row[0]))
    return intervals


def _validated_interval(lo, hi, i):
    if not isinstance(lo, str) or not isinstance(hi, str):
        raise ValueError(f'cycle {i}: endpoints must be decimal strings')
    try:
        lower, upper = Decimal(lo), Decimal(hi)
    except InvalidOperation as exc:
        raise ValueError(f'cycle {i}: invalid endpoint') from exc
    if not lower.is_finite() or not upper.is_finite():
        raise ValueError(f'cycle {i}: surviving non-finite interval')
    if lower <= 0 or lower > upper:
        raise ValueError(f'cycle {i}: invalid interval order or radius')


def authenticated_intervals(cycles, flat, boundary, facets, pmax=16):
    """Proof entrypoint: live table, complete cycles, and exact deletions.

    project_intervals alone is only a structural projection; its caller may
    not promote arbitrary exclusion indices into a mathematical certificate.
    """
    from class_filter import validate_inputs, validate_inventory
    from exact_inputs import authenticate_exclusions
    validate_inputs(cycles, flat, boundary, pmax)
    validate_inventory(cycles, facets)
    authenticated = authenticate_exclusions(cycles, flat, boundary, pmax, facets=facets)
    expected = (set(flat['flat']), set(boundary['degenerate']))
    if (type(authenticated) is not tuple or len(authenticated) != 2 or
            any(type(ids) is not set for ids in authenticated) or authenticated != expected):
        raise ValueError('incomplete exact exclusion authentication for Omega')
    return project_intervals(cycles, flat, boundary, pmax)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input-dir', type=Path, default=Path('.'))
    parser.add_argument('--pmax', type=int, default=16)
    parser.add_argument('--output', type=Path, default=Path('u5_omega_p16.json'))
    args = parser.parse_args()
    def load(name):
        return json.loads((args.input_dir / name).read_text(encoding='utf-8'))
    cycles = load(f'cert_stage1_5d_p{args.pmax}.json')
    flat = load(f'exact_flat_p{args.pmax}.json')
    boundary = load(f'exact_boundary_p{args.pmax}.json')
    facets = load(f'cert_facets4_p{args.pmax}.json')
    intervals = authenticated_intervals(cycles, flat, boundary, facets, args.pmax)
    data = json.dumps(dict(intervals=intervals), indent=0).encode('utf-8')
    args.output.write_bytes(data)
    print(f'{len(intervals)} intervals; sha256 {hashlib.sha256(data).hexdigest()}')


if __name__ == '__main__':
    main()
