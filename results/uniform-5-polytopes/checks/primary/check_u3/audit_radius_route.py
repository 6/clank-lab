"""Audit the whole-class route after an independent U3 replay.

python audit_radius_route.py PRODUCER_DIR RESULT.json PMAX
python audit_radius_route.py --selftest

Checks producer/export/result interval containment using exact decimals,
complete class/signature coverage, and explicit OPEN/undecided counts.
This is a coverage/accounting test, not a replacement for replaying closure.
"""
import copy
from decimal import Decimal
import hashlib
import json
from pathlib import Path
import sys

def bounds(pair):
    if not len(pair) == 2:
        raise AssertionError()
    a, b = map(Decimal, pair)
    if not (a.is_finite() and b.is_finite() and (0 < a < b)):
        raise AssertionError()
    return (a, b)

def contains(outer, inner):
    a, b = bounds(outer)
    c, d = bounds(inner)
    return a <= c <= d <= b

def indexed(rows):
    out = {c['index']: c for c in rows}
    if not len(out) == len(rows):
        raise AssertionError('duplicate class index')
    return out

def audit(producer, inputs, result):
    alive = {i: c for i, c in enumerate(producer) if c['alive']}
    src, got = (indexed(inputs), indexed(result['classes']))
    if not alive.keys() == src.keys() == got.keys():
        raise AssertionError('missing/extra class')
    counts = dict(classes=len(alive), producer_classes_covered=0, vertex_figures=0, realisations=0, unique_root=0, radius_OPEN=0, verdict_KNOWN=0, verdict_REFUTED=0, verdict_OPEN=0, undecided_vertex_figures=0, signatures_without_realisation=0, development_errors=0, search_undecided=0, development_undecided=0, classes_OPEN=0)
    for ci, c in src.items():
        if not contains(c['R'], alive[ci]['R']):
            raise AssertionError(('input misses producer class', ci))
        if not contains(got[ci]['R'], c['R']):
            raise AssertionError(('result misses input class', ci))
        if not bounds(got[ci]['R']) == bounds(c['R']):
            raise AssertionError(('result changed class', ci))
        counts['producer_classes_covered'] += 1
        counts['classes_OPEN'] += got[ci].get('status') == 'OPEN'
        if not len(c['vfs']) == len(got[ci]['vfs']):
            raise AssertionError(('missing signature', ci))
        for vi, (vf, rec) in enumerate(zip(c['vfs'], got[ci]['vfs'])):
            counts['vertex_figures'] += 1
            if not sorted(vf['facets']) == sorted(rec['facets']):
                raise AssertionError(('facets', ci, vi))
            counts['search_undecided'] += rec['search']['undecided']
            if 'error' in rec:
                counts['undecided_vertex_figures'] += 1
                continue
            if not len(vf['cycles']) == rec['n_cycles']:
                raise AssertionError(('cycles', ci, vi))
            reals = rec['realisations']
            if not reals:
                counts['signatures_without_realisation'] += 1
            for r in reals:
                counts['realisations'] += 1
                if not isinstance(r['unique_root'], bool):
                    raise AssertionError()
                counts['unique_root'] += r['unique_root']
                counts['radius_OPEN'] += not r['unique_root']
                if not r['verdict'] in ('KNOWN', 'REFUTED', 'OPEN'):
                    raise AssertionError()
                counts['verdict_' + r['verdict']] += 1
                counts['development_errors'] += 'error' in r.get('development', {})
                counts['development_undecided'] += r.get('development', {}).get('undecided', 0)
    for key in ('search_undecided', 'development_undecided'):
        if not key in result['summary']:
            raise AssertionError(('mandatory counter missing', key))
        if not counts[key] == result['summary'][key]:
            raise AssertionError(('summary mismatch', key))
    for name, key in (('classes', 'classes'), ('vertex_figures', 'vertex_figures'), ('realisations', 'realisations'), ('unique_root', 'unique_root'), ('verdict_KNOWN', 'verdict_KNOWN'), ('verdict_REFUTED', 'verdict_REFUTED'), ('verdict_OPEN', 'verdict_OPEN'), ('undecided_vertex_figures', 'vf_errors'), ('signatures_without_realisation', 'vf_without_realisation')):
        if not counts[name] == result['summary'].get(key, 0):
            raise AssertionError(('summary mismatch', name))
    counts['status'] = 'PASS' if not any((counts[k] for k in ('radius_OPEN', 'verdict_OPEN', 'undecided_vertex_figures', 'signatures_without_realisation', 'development_errors', 'search_undecided', 'development_undecided', 'classes_OPEN'))) else 'PARTIAL'
    return counts

def selftest():
    producer = [dict(R=['1', '2'], alive=[0])]
    inputs = [dict(index=0, R=['1', '2'], vfs=[dict(facets=['fixture'], cycles=[[]])])]
    result = dict(classes=[dict(index=0, R=['1', '2'], vfs=[dict(facets=['fixture'], n_cycles=1, search=dict(undecided=0), realisations=[dict(unique_root=True, verdict='KNOWN')])])], summary=dict(classes=1, vertex_figures=1, realisations=1, unique_root=1, verdict_KNOWN=1, search_undecided=0, development_undecided=0))
    if not audit(producer, inputs, result)['status'] == 'PASS':
        raise AssertionError()
    rejected = 0
    for pair in (['0.9', '1.5'], ['1.5', '2.1'], ['0.9', '2.1']):
        bad = copy.deepcopy(producer)
        bad[0]['R'] = pair
        try:
            audit(bad, inputs, result)
        except AssertionError:
            rejected += 1
        else:
            raise AssertionError('uncovered producer class accepted')
    bad = copy.deepcopy(result)
    bad['classes'] = []
    try:
        audit(producer, inputs, bad)
    except AssertionError:
        rejected += 1
    else:
        raise AssertionError('missing class accepted')
    bad = copy.deepcopy(result)
    bad['classes'][0]['vfs'][0]['realisations'][0]['unique_root'] = False
    bad['summary']['unique_root'] = 0
    if not audit(producer, inputs, bad)['status'] == 'PARTIAL':
        raise AssertionError()
    if not audit(producer, inputs, bad)['radius_OPEN'] == 1:
        raise AssertionError()
    bad = copy.deepcopy(result)
    bad['classes'][0]['vfs'][0]['realisations'][0]['verdict'] = 'OPEN'
    bad['summary']['verdict_KNOWN'] = 0
    bad['summary']['verdict_OPEN'] = 1
    if not audit(producer, inputs, bad)['status'] == 'PARTIAL':
        raise AssertionError()
    if not audit(producer, inputs, bad)['verdict_OPEN'] == 1:
        raise AssertionError()
    bad = copy.deepcopy(result)
    bad['classes'][0]['vfs'][0] = dict(facets=['fixture'], error='undecided: fixture', search=dict(undecided=1))
    bad['summary'].update(realisations=0, unique_root=0, verdict_KNOWN=0, vf_errors=1, search_undecided=1)
    if not audit(producer, inputs, bad)['status'] == 'PARTIAL':
        raise AssertionError()
    if not audit(producer, inputs, bad)['undecided_vertex_figures'] == 1:
        raise AssertionError()
    for key in ('search_undecided', 'development_undecided'):
        bad = copy.deepcopy(result)
        del bad['summary'][key]
        try:
            audit(producer, inputs, bad)
        except AssertionError:
            rejected += 1
        else:
            raise AssertionError('missing mandatory counter accepted')
    bad = copy.deepcopy(result)
    bad['classes'][0]['vfs'][0]['realisations'][0]['development'] = dict(undecided=1)
    bad['summary']['development_undecided'] = 1
    if not audit(producer, inputs, bad)['status'] == 'PARTIAL':
        raise AssertionError()
    print(json.dumps(dict(status='PASS', false_coverage_controls_rejected=rejected, unresolved_controls_reported_PARTIAL=4), sort_keys=True))

def main():
    if sys.argv[1:] == ['--selftest']:
        selftest()
        return
    if len(sys.argv) != 4:
        raise SystemExit(__doc__)
    directory, result_file, p = (Path(sys.argv[1]), Path(sys.argv[2]), int(sys.argv[3]))
    target = Path(__file__).resolve().parent.parent
    expected = {line.split()[1]: line.split()[0] for line in (target / 'check_u1/current-inputs.sha256').read_text().splitlines()}
    data, identities = ([], {})
    for prefix in ('classes', 'u3_vfs'):
        name = '%s_p%d.json' % (prefix, p)
        path = directory / name
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        if not digest == expected['producer-p%d/%s' % (p, name)]:
            raise AssertionError(('input pin', name))
        identities[name] = digest
        data.append(json.loads(path.read_text()))
    result = json.loads(result_file.read_text())
    report = audit(*data, result)
    if not report['classes'] == {6: 136, 10: 278, 16: 563}[p]:
        raise AssertionError()
    if not report['vertex_figures'] == {6: 168, 10: 332, 16: 629}[p]:
        raise AssertionError()
    report.update(pmax=p, inputs_sha256=identities, result_sha256=hashlib.sha256(result_file.read_bytes()).hexdigest(), radius_route='independent closure on producer class interval')
    print(json.dumps(report, indent=2, sort_keys=True))
    if report['status'] != 'PASS':
        raise SystemExit(1)
if __name__ == '__main__':
    main()
