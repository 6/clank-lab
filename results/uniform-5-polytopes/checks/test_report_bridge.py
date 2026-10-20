#!/usr/bin/env python3
"""Corrupt each new data bridge; full replay supplies its fresh S3 output."""
import argparse
import copy
import json
from pathlib import Path
import report_bridge as bridge


def rejected(call, label):
    try:
        call()
    except (ValueError, KeyError):
        return
    raise AssertionError('accepted corruption: ' + label)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--independent', type=Path)
    parser.add_argument('--primary-report', type=Path)
    parser.add_argument('--signatures', type=Path)
    args = parser.parse_args()
    report = bridge.read_json(bridge.SOURCE)
    signatures = bridge.read_json(bridge.SIGNATURES)
    original = bridge.LEAN.read_text()
    if bridge.generate(report, signatures) != original:
        raise AssertionError('uncorrupted Lean regeneration failed')
    corrupt = copy.deepcopy(report)
    corrupt['classes'][0]['vfs'][0]['realisations'][0]['local_uniqueness']['valid_g'] += 1
    if bridge.generate(corrupt, signatures) == original:
        raise AssertionError('Lean diagnostic corruption escaped exact regeneration')
    swapped = copy.deepcopy(signatures)
    row = next(c for c in swapped if c['index'] == 18)
    row['vfs'][0], row['vfs'][2] = row['vfs'][2], row['vfs'][0]
    rejected(lambda: bridge.generate(report, swapped), 'primary figure order')
    tested = 2
    if bool(args.primary_report) != bool(args.signatures):
        raise ValueError('fresh primary controls require both --primary-report and --signatures')
    primary = bridge.read_json(args.primary_report) if args.primary_report else report
    actual = (bridge.read_json(args.signatures) if args.signatures else
              [dict(row, R=next(c['R'] for c in report['classes'] if c['index'] == row['index']))
               for row in signatures])
    bridge.compare_primary(report, signatures, primary, actual)
    def corrupt_primary(change, label):
        damaged, damaged_input = copy.deepcopy(primary), copy.deepcopy(actual)
        change(damaged, damaged_input)
        rejected(lambda: bridge.compare_primary(report, signatures, damaged, damaged_input), label)
    def change_diagnostic(data, inputs):
        data['classes'][0]['vfs'][0]['realisations'][0]['local_uniqueness']['tested_g'] += 1
    corrupt_primary(change_diagnostic, 'fresh primary diagnostic')
    def change_interval(data, inputs):
        data['classes'][0]['R'][0] = '0'
    corrupt_primary(change_interval, 'fresh primary/input interval link')
    def swap_input(data, inputs):
        row = next(c for c in inputs if c['index'] == 18)
        row['vfs'][0], row['vfs'][1] = row['vfs'][1], row['vfs'][0]
    corrupt_primary(swap_input, 'same-coarse-metadata actual input order')
    def swap_both(data, inputs):
        swap_input(data, inputs)
        row = next(c for c in data['classes'] if c['index'] == 18)
        row['vfs'][0], row['vfs'][1] = row['vfs'][1], row['vfs'][0]
    corrupt_primary(swap_both, 'coordinated primary report/input order swap')
    def omit_pair(data, inputs):
        del data['classes'][0]['vfs'][0]['realisations'][0]['embedding']['A510000']
    corrupt_primary(omit_pair, 'missing candidate pair')
    def change_inventory(data, inputs):
        data['known']['A500001']['classes'] = [1]
    corrupt_primary(change_inventory, 'known radius-class inventory')
    def duplicate_name(data, inputs):
        data['classes'][0]['vfs'][0]['realisations'][0]['known_names'].append('A500001')
    corrupt_primary(duplicate_name, 'known name duplicated')
    def change_extra_no(data, inputs):
        row = next(c for c in data['classes'] if c['index'] == 18)
        row['vfs'][0]['realisations'][0]['embedding']['A510001'][0] = 'NO-COUNT'
    corrupt_primary(change_extra_no, 'extra candidate A510001 must be NO')
    tested += 8
    if args.independent:
        independent = [json.loads(line) for line in bridge.read_bytes(args.independent).splitlines() if line.strip()]
        bridge.compare_independent(report, signatures, independent)
        def mutate(mapping, key, value, label):
            previous = mapping[key]
            mapping[key] = value
            try:
                rejected(lambda: bridge.compare_independent(report, signatures, independent), label)
            finally:
                mapping[key] = previous
        first = independent[0]
        real = first['realisations'][0]
        mutate(first, 'index', 99999, 'class index')
        mutate(real['signature'], 'cycles', real['signature']['cycles'][:-1], 'full cyclic signature')
        mutate(real, 'status', 'REFUTED', 'verdict')
        mutate(real, 'names', [], 'known name')
        mutate(real['radius'], 'status', 'OPEN', 'ROOT flag')
        mutate(real['local_uniqueness'], 'status', 'OPEN', 'FORCED flag')
        extra_class = next(c for c in independent if c['index'] == 18)
        extra = next(r for r in extra_class['realisations'] if r['status'] == 'REFUTED')
        mutate(extra['development'], 'status', 'OPEN', 'row 12 development')
        comparison = next(q for q in extra_class['identification']['known'] if q['name'] == 'A510001')
        mutate(comparison['checks'][0], 'reason', 'exact neighbour count', 'NO vs NO-COUNT')
        # Same coarse facet/cycle counts: the pinned ordered full-word binding
        # distinguishes the extra candidate from the genuine A510001 star.
        swapped = copy.deepcopy(signatures)
        row = next(c for c in swapped if c['index'] == 18)
        row['vfs'][0], row['vfs'][1] = row['vfs'][1], row['vfs'][0]
        rejected(lambda: bridge.compare_independent(report, swapped, independent), 'extra/known signature swap')
        tested += 9
    print(f'PASS report bridge corruption controls: {tested} rejected')


if __name__ == '__main__':
    main()
