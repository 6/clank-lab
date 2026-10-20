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
    for p, convention, name in [(6, 'parameter', 'classes_p6.json.gz'),
                                (10, 'parameter', 'classes_p10.json.gz'),
                                (16, 'parameter', 'classes_p16.json.gz'),
                                (6, 'strict', 'strict_p6.json.gz')]:
        selected = f.select_cycles(cycles, library.selected(p, convention))
        actual = f.calculate(selected, library)
        frozen = f.load_json(output / name)
        for key in ('counts', 'classes', 'deletion_certificates'):
            f.require(json.loads(json.dumps(actual[key])) == frozen[key], 'FILTER replay differs: ' + name + '/' + key)
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
                      'same_corruptions_rejected_by_both': rejected}, sort_keys=True))


if __name__ == '__main__':
    main()
