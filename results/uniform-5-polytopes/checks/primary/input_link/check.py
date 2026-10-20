"""Check the frozen LIB/S1 link without importing its exporter.

Two link implementations: A enumerates sides of certified cyclic cells and
uses the radius formula; B intersects certified faces and evaluates the
geometric dihedral directly. Both replay the existing ridge certificate.
They do not independently prove R2 or the ridge-checking implementation.
"""
import argparse
from collections import Counter
import hashlib
import itertools
import json
from pathlib import Path
from types import SimpleNamespace
from sources import local, cr, cf, angle, read_ball, arb


def require(test, why):
    if not test:
        raise ArithmeticError(why)


def check_record(record, mode):
    name = record['name']
    S, src = local(name)
    ridges = [(lab, tuple(c)) for lab, c in record['ridges']]
    model = SimpleNamespace(name=name, X=src.X, ridges=ridges)
    cert, _ = cr.certify(model, S=S)
    require(cert == ridges, 'cell labels')
    actual = {}
    if mode == 'A':
        for ci, (_, cyc) in enumerate(cert):
            for a, b in zip(cyc, cyc[1:] + cyc[:1]):
                actual.setdefault(tuple(sorted((a, b))), []).append(ci)
    else:
        # Distinct faces of a convex 3-polytope share an edge iff their
        # vertex intersection has two elements. Their supporting/cyclic
        # and closure facts were checked above, not inferred from floats.
        for i, j in itertools.combinations(range(len(cert)), 2):
            common = set(cert[i][1]) & set(cert[j][1])
            require(len(common) <= 2, 'two faces share more than an edge')
            if len(common) == 2:
                e = tuple(sorted(common))
                require(e not in actual, 'three cells at one polygon')
                actual[e] = [i, j]
    listed = {}
    for o in record['occurrences']:
        e = tuple(o['edge'])
        require(e == tuple(sorted(e)) and len(e) == 2 and e not in listed, 'repeated/invalid polygon')
        require(e in actual and sorted(o['cells']) == sorted(actual[e]), 'polygon-cell correspondence')
        pair = actual[e]
        require(len(pair) == 2, 'polygon cell count')
        p = cr.chord_q(cr.model_d2(model.X[e[0]], model.X[e[1]]))
        a, b = sorted(cert[i][0] for i in pair)
        require(o['word'] == [p, a, b], 'polygon word')
        listed[e] = (p, a, b)
    require(set(listed) == set(actual), 'missing polygon occurrence')
    table = record['input']
    require(table['name'] == name, 'table name')
    radius = read_ball(table['R'])
    require(radius.is_finite() and radius > 0 and radius.contains(S['R']), 'radius enclosure')
    words = [(p, a, b) for p, a, b, _, _ in table['orbits']]
    require(Counter(words) == Counter(set(listed.values())), 'incomplete/duplicate orbit table')
    lookup = {(p, a, b): read_ball((mid, rad)) for p, a, b, mid, rad in table['orbits']}
    # The existing S1 consumer stops at depth eight. This proves the
    # cutoff conservatively, including the serialized-ball widening.
    require(all(al.is_finite() and al > 0 and al < arb.pi() and 9 * al > 2 * arb.pi()
                for al in lookup.values()), 'S1 depth bound')
    for edge, word in listed.items():
        p, a, b = word
        if mode == 'A':
            value = angle(S['R'], p, a, b)
        else:
            ca, cb = actual[edge]
            value = cf.dihedral(S['v0'], [S['nbrs'][i] for i in edge],
                                [S['nbrs'][i] for i in cert[ca][1]],
                                [S['nbrs'][i] for i in cert[cb][1]])
        require(value.is_finite() and lookup[word].contains(value), 'angle enclosure')
    return len(actual), len(words)


def check(certificate, spec, mode='A', only=None):
    require(certificate['schema'] == 1, 'schema')
    require(certificate['claim'] == 'LIB/S1 input link conditional on R2', 'claim scope')
    records = certificate['records']
    names = [r['name'] for r in records]
    require(len(names) == len(set(names)), 'duplicate facet')
    require(set(names) == {f['name'] for f in spec}, 'incomplete library')
    aliases = {f['name']: f['aliases'] for f in spec}
    n, polygons, words = 0, 0, 0
    for r in records:
        require(r['input']['aliases'] == aliases[r['name']], 'alias projection')
        if only is None or r['name'] in only:
            p, w = check_record(r, mode)
            n, polygons, words = n + 1, polygons + p, words + w
    return dict(mode=mode, facets=n, polygons=polygons, words=words)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('certificate', type=Path)
    p.add_argument('--names', type=Path, required=True)
    p.add_argument('--table', type=Path, required=True)
    p.add_argument('--mode', choices=('A', 'B'), default='A')
    p.add_argument('--only', nargs='+')
    a = p.parse_args()
    cert = json.loads(a.certificate.read_text())
    require(hashlib.sha256(a.names.read_bytes()).hexdigest() == cert['names_sha256'], 'names identity')
    spec = json.loads(a.names.read_text())
    require(json.loads(a.table.read_text()) == [r['input'] for r in cert['records']], 'export projection')
    if a.only:
        require(set(a.only) <= {f['name'] for f in spec}, 'unknown selected facet')
    print(json.dumps(check(cert, spec, a.mode, a.only), sort_keys=True))


if __name__ == '__main__':
    main()
