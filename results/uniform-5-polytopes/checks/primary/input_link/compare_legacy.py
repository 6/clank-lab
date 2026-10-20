"""Certify the actual legacy S1 input by both incidence/metric link checks.

Usage: compare_legacy.py cert_facets4_pP.json P [--selftest]
The full-table hash in the receipt binds this check to the replay's input.
The canonical name/alias projection is pinned by current-inputs.sha256.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path

from check import check_record, require

HERE = Path(__file__).resolve().parent


def digest(data):
    return hashlib.sha256(data).hexdigest()


def certify(facets, p):
    cert = json.loads((HERE / 'evidence/certificate.json').read_text())
    source = {r['name']: r for r in cert['records']}
    names = [f['name'] for f in facets]
    require(len(set(names)) == len(names), 'duplicate legacy facet')
    require(set(names) <= source.keys(), 'unknown legacy facet')
    if p == 16:
        require(set(names) == source.keys(), 'incomplete P16 library')
    # This is exactly regenerate_inputs.py's pinned name/alias projection.
    projection = json.dumps([dict(name=f['name'], aliases=f['aliases']) for f in facets], indent=0).encode()
    pins = dict((line.split()[1], line.split()[0]) for line in
                (HERE.parent / 'check_u1/current-inputs.sha256').read_text().splitlines())
    require(digest(projection) == pins['producer-p%d/u1_facets_p%d.json' % (p, p)],
            'legacy name/alias identity')
    totals = []
    for mode in ('A', 'B'):
        polygons = words = 0
        for f in facets:
            record = copy.deepcopy(source[f['name']])
            # The frozen certified occurrence list is unchanged. Every legacy
            # word must occur exactly once and enclose every corresponding
            # exact angle, using S1's actual serialized-ball parser.
            record['input'] = f
            n, w = check_record(record, mode)
            polygons += n
            words += w
        totals.append(dict(mode=mode, facets=len(facets), polygons=polygons, words=words))
    require(totals[0]['polygons'] == totals[1]['polygons'] and
            totals[0]['words'] == totals[1]['words'], 'link checker disagreement')
    return dict(status='PASS', pmax=p, checks=totals,
                claim='legacy S1 input containment conditional on R2',
                names_sha256=digest(projection),
                incidence_certificate_sha256=digest((HERE / 'evidence/certificate.json').read_bytes()))


def corruptions():
    cert = json.loads((HERE / 'evidence/certificate.json').read_text())
    original = next(r for r in cert['records'] if r['name'] == 'A40001')
    rejected = {}
    for mode in ('A', 'B'):
        count = 0
        for corruption in ('radius', 'angle', 'missing-word', 'duplicate-word', 'label', 'polygon'):
            r = copy.deepcopy(original)
            t = r['input']
            if corruption == 'radius':
                t['R'] = ['100', '0']
            elif corruption == 'angle':
                t['orbits'][0][-2:] = ['0', '0']
            elif corruption == 'missing-word':
                t['orbits'].pop()
            elif corruption == 'duplicate-word':
                t['orbits'].append(copy.deepcopy(t['orbits'][0]))
            elif corruption == 'label':
                t['orbits'][0][1] = 'wrong-label'
            else:
                t['orbits'][0][0] += 1
            try:
                check_record(r, mode)
            except ArithmeticError:
                count += 1
            else:
                raise AssertionError(('corrupted legacy table accepted', mode, corruption))
        rejected[mode] = count
    return rejected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('table', type=Path)
    parser.add_argument('pmax', type=int, choices=(6, 10, 16))
    parser.add_argument('--selftest', action='store_true')
    args = parser.parse_args()
    data = args.table.read_bytes()
    out = certify(json.loads(data), args.pmax)
    out['legacy_input_sha256'] = digest(data)
    out['checker_sha256'] = digest(Path(__file__).read_bytes())
    if args.selftest:
        out['corruptions_rejected'] = corruptions()
    print(json.dumps(out, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
