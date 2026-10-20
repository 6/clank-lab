"""Check complete uniform snub factors and their check_u3 index identities.

The proposal generator is not imported. Equalities use a finite exact
quadratic-field group and polynomial identities. Intervals prove strict
inequalities and root existence/uniqueness, never equality from overlap.
"""
import argparse
import hashlib
import json
import time
from collections import Counter
from pathlib import Path
from snub_exact import ExactGroup
from snub_interval import construction, support
import tcert

HERE = Path(__file__).resolve().parent


def check(cert, corruption=''):
    if not (cert['schema'] == 1):
        raise AssertionError()
    for name in ('geom.py', 'ivla.py', 'tcert.py'):
        actual = hashlib.sha256((HERE.parent/'check_u3'/name).read_bytes()).hexdigest()
        if not (cert['sources'][name] == actual):
            raise AssertionError(('source identity', name))
    results = {}
    for diag in ('B3', 'H3'):
        start = time.monotonic()
        g = ExactGroup(diag)
        data = cert['models'][diag]
        if not (data['permutations'] == g.perms):
            raise AssertionError('certified exact permutations')
        if not (data['parents'] == [list(p) if p is not None else None for p in g.parent]):
            raise AssertionError('exact group words')
        if not (data['seeds'] == g.seeds):
            raise AssertionError('exact unit-edge seeds')
        points, _, _ = construction(g, corruption, data['root_box'])
        model = tcert.SnubModel(diag)
        if not (model.n == g.n and model.dim == 3 and model.stab_gens == []):
            raise AssertionError()
        if not ([p.tolist() for p in model.gens] == g.perms and model.seeds == g.seeds):
            raise AssertionError()
        if not (model.planar == {frozenset(g.cyclic_orbit(k)) for k in range(2)}):
            raise AssertionError()
        actions = [list(range(g.n))]
        for parent in g.parent[1:]:
            i, k = parent
            actions.append([g.perms[k][t] for t in actions[i]])
        inverse_actions = [[p.index(i) for i in range(g.n)] for p in actions]
        regular = set()
        for k in range(2):
            O = g.cyclic_orbit(k)
            for p in actions:
                cycle = tuple(p[i] for i in O)
                for oriented in (cycle, cycle[::-1]):
                    regular.update(oriented[j:]+oriented[:j] for j in range(len(cycle)))
        seen, edges = set(), Counter()
        for face in data['faces']:
            if not (len(face) >= 3 and len(set(face)) == len(face)):
                raise AssertionError()
            if not (all(type(i) is int and 0 <= i < g.n for i in face)):
                raise AssertionError()
            s = frozenset(face)
            if not (s not in seen):
                raise AssertionError('duplicate facet')
            seen.add(s)
            if len(face) > 3:
                if not (tuple(face) in regular):
                    raise AssertionError('exact planar regular rotation orbit')
            for i, j in zip(face, face[1:]+face[:1]):
                relative = inverse_actions[i][j]
                if not (relative in g.identities):
                    raise AssertionError('exact facet edge equation')
                edges[tuple(sorted((i, j)))] += 1
            support(points, face)
        if not (set().union(*seen) == set(range(g.n))):
            raise AssertionError('vertex coverage')
        if not (set(edges.values()) == {2}):
            raise AssertionError('closed complete hull boundary')
        fvector = (g.n, len(edges), len(seen))
        if not (fvector == ((24, 60, 38) if diag == 'B3' else (60, 150, 92))):
            raise AssertionError('snub f-vector')
        if not (g.n-len(edges)+len(seen) == 2):
            raise AssertionError()
        counts = dict(sorted(Counter(map(len, data['faces'])).items()))
        if not (counts == ({3: 32, 4: 6} if diag == 'B3' else {3: 80, 5: 12})):
            raise AssertionError()
        results[diag] = {'f_vector': fvector, 'regular_facets': counts,
                         'exact_unit_neighbors': g.seeds,
                         'seconds': round(time.monotonic()-start, 6)}
    return results


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('certificate', nargs='?', type=Path, default=HERE/'snub_certificate.json')
    args = parser.parse_args()
    print(json.dumps({'outcome': 'CERTIFIED', 'models': check(json.loads(args.certificate.read_text()))}, sort_keys=True))
