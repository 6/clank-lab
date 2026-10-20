"""Replay FILTER and its certificate checkers without private provenance records.

PUBLIC.sha256 authenticates the inputs. The mathematical implementations are
unchanged: this driver connects their public functions to the supplied data.
"""
import json
from pathlib import Path
import sys

BASE = Path(__file__).resolve().parent
sys.path.insert(0, str(BASE / 'independent-merge-filter'))
import filter as f
import certificate_check as c


def strict_disjoint_intervals(records, field, label):
    """Closed class hulls are strictly disjoint, in exact rational arithmetic."""
    intervals = sorted(f.interval(row[field]) for row in records)
    for previous, current in zip(intervals, intervals[1:]):
        if previous[1] >= current[0]:
            raise ValueError(label + ': overlapping or touching class hulls')
    return len(intervals)


def consumer_intervals(actual, expected, library, *, check_disjoint=True):
    """Every fresh S1 root in a surviving class is covered by the S2 input."""
    def key(row):
        return next(iter(f.class_sets([row], library)))
    consumers = {key(row): row for row in expected}
    if len(consumers) != len(expected):
        raise ValueError('duplicate S2 consumer class')
    if set(consumers) != {key(row) for row in actual}:
        raise ValueError('S1/S2 complete class sets differ')
    if check_disjoint:
        strict_disjoint_intervals(actual, 'R_alive', 'regenerated S1')
        strict_disjoint_intervals(expected, 'R', 'S2 consumer')
    for row in actual:
        low, high = f.interval(row['R_alive'])
        outer_low, outer_high = f.interval(consumers[key(row)]['R'])
        if not outer_low <= low <= high <= outer_high:
            raise ValueError('S2 class interval does not cover regenerated S1 roots')
    return len(actual)


def main():
    # Rebind only the provenance container, using the already authenticated
    # public byte identities; no expected scientific result is learned here.
    pins = {name.removeprefix("checks/"): digest for digest, name in
            (line.split('  ', 1) for line in (BASE.parent / 'data/PUBLIC.sha256').read_text().splitlines())
            if name.startswith('checks/')}
    (BASE / 'independent-merge-filter/sources.json').write_text(json.dumps({'sources': pins}))
    library = f.read_library(f.load_json(BASE / 'independent-s1-b2/library.json')['records'])
    f.check_library_data(library, f.load_json(BASE / 'input_link/evidence/s1_facets_p16.json'),
                         f.load_json(BASE / 'check_u1/inputs/u1_facets_p16.json'))
    cycles = f.independent_cycles(f.load_json(BASE / 'independent-s1-b2/evidence/cycles.json.gz'), library)
    output = BASE / 'independent-merge-filter/results'
    reports = c.check_all(BASE, output)
    requirements, aliases, complete = c.inputs(BASE)
    interval_counts = {}
    disjoint_counts = {}
    for p, convention, name in [(6, 'parameter', 'classes_p6.json.gz'),
                                (10, 'parameter', 'classes_p10.json.gz'),
                                (16, 'parameter', 'classes_p16.json.gz'),
                                (6, 'strict', 'strict_p6.json.gz')]:
        selected = f.select_cycles(cycles, library.selected(p, convention))
        actual = f.calculate(selected, library)
        frozen = f.load_json(output / name)
        for key in ('counts', 'classes', 'deletion_certificates'):
            f.require(json.loads(json.dumps(actual[key])) == frozen[key], 'FILTER replay differs: ' + name + '/' + key)
        disjoint_counts[f'independent-{convention}-p{p}'] = strict_disjoint_intervals(
            actual['classes'], 'R_alive', name)
        if convention == 'parameter':
            consumer = f.load_json(BASE / f'independent-s23/inputs/u2_classes_p{p}.json.gz')
            interval_counts[str(p)] = consumer_intervals(actual['classes'], consumer, library)
            disjoint_counts[f'consumer-p{p}'] = strict_disjoint_intervals(
                consumer, 'R', f'S2 P{p}')
            # P6's primary producer classes are the authenticated S2 input.
            # Separate public primary S1 files exist for P10 and P16.
            if p in (10, 16):
                primary = f.load_json(BASE / f'check_u1/classes_p{p}.json')
                if f.class_sets(primary, library) != f.class_sets(actual['classes'], library):
                    raise ValueError('primary/independent surviving class sets differ')
                disjoint_counts[f'primary-p{p}'] = strict_disjoint_intervals(
                    primary, 'R_alive', f'primary P{p}')
                disjoint_counts[f'primary-original-p{p}'] = strict_disjoint_intervals(
                    primary, 'R', f'primary original P{p}')
            # A singleton at a consumer endpoint cannot cover a nonzero root box.
            damaged = json.loads(json.dumps(consumer))
            damaged[0]['R'][1] = damaged[0]['R'][0]
            try:
                consumer_intervals(actual['classes'], damaged, library)
            except ValueError:
                pass
            else:
                raise ValueError('accepted narrowed S2 class interval')
        # Reuse the same semantic corruptions against BOTH mathematical checks.
        if p == 16:
            keys = sorted(selected)
            groups = f.components([(*root, key) for key, row in selected.items()
                                   if row.status == 'ROOT' for root in row.roots])
            rejected = []
            for label, bad in c.mutations(frozen, complete):
                try:
                    c.check_records(bad, complete, requirements, aliases, 'parameter')
                except c.Invalid:
                    pass
                else:
                    raise ValueError('certificate checker accepted ' + label)
                classes = {r['class_index']: r for r in bad['classes']}
                certs = {r['class_index']: r for r in bad['deletion_certificates']}
                try:
                    for i, (_, _, initial) in enumerate(groups):
                        alive = set(next(iter(f.class_sets([classes[i]], library)))) if i in classes else set()
                        rounds = [{(w['facet'], tuple(w['missing'])): [keys[j] for j in w['cycle_ids']]
                                   for w in row} for row in certs.get(i, {}).get('rounds', [])]
                        f.audit_deletions(initial, alive, rounds, library.requirements)
                except f.Invalid:
                    rejected.append(label)
                else:
                    raise ValueError('deletion auditor accepted ' + label)
            if len(rejected) != 3:
                raise ValueError('incomplete corruption suite')
    print(json.dumps({'status': 'PASS', 'checks': reports,
                      'consumer_intervals_cover_s1_roots': interval_counts,
                      'strictly_disjoint_class_hulls': disjoint_counts,
                      'same_corruptions_rejected_by_both': rejected}, sort_keys=True))


if __name__ == '__main__':
    main()
