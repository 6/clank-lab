"""Small independent checker of the exact correspondence certificates.

Does not import the search or the certificate producer. The authoritative
model generators and cell certification are the existing read-only U3
library. Group permutations are exact by construction, never inferred from
nearby alternative placements. All certificate fields are checked.
"""
import argparse
import copy
import json
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'check_u3'))
import templates
import tcert
from model_runtime import ensure_guard

class ModelCells(templates.Template):

    def _dihedral(self, *args):
        return None

    def _syms(self):
        pass
_CACHE = {}

def authoritative(name):
    ensure_guard()
    if name not in _CACHE:
        model = tcert.model4(name)
        V = [[tcert.qiv(c) for c in v] for v in model.E] if hasattr(model, 'E') else None
        _CACHE[name] = ModelCells(name, V=V)
    return _CACHE[name]

def check(doc):
    if not set(doc) == {'schema', 'name', 'neighbours', 'faces', 'symmetries', 'reductions'}:
        raise AssertionError()
    if not doc['schema'] == 'stage2-exact-equivalence-v1':
        raise AssertionError()
    T = authoritative(doc['name'])
    nb = T.nb
    if not doc['neighbours'] == nb:
        raise AssertionError()
    loc = {v: i for i, v in enumerate(nb)}
    faces = doc['faces']
    if not len(faces) == len(T.cells):
        raise AssertionError()
    edges = {frozenset((loc[v] for v in k)): q['p'] for k, q in T.polys.items()}
    expect = {}
    for fi, cell in enumerate(T.cells):
        f = faces[fi]
        if not set(f) == {'verts', 'label', 'ps'}:
            raise AssertionError()
        true_order = [loc[v] for v in cell['poly']]
        if not any((f['verts'] == (true_order[s:] + true_order[:s])[::d] for s in range(len(true_order)) for d in (1, -1))):
            raise AssertionError()
        if not f['label'] == cell['label']:
            raise AssertionError()
        vs = f['verts']
        m = len(vs)
        if not f['ps'] == [edges[frozenset((vs[i], vs[(i + 1) % m]))] for i in range(m)]:
            raise AssertionError()
        for s in range(m):
            for d in (1, -1):
                ci = 2 * s + (d == -1)
                expect[fi, ci] = [vs[(s + d * i) % m] for i in range(m)]
    group = {tuple((loc[int(g[v])] for v in nb)) for g in T.model.stab()}
    perms = [tuple(p) for p in doc['symmetries']]
    if not (len(set(perms)) == len(perms) and perms):
        raise AssertionError()
    if not all((p in group for p in perms)):
        raise AssertionError()
    for p in perms:
        if not sorted(p) == list(range(len(nb))):
            raise AssertionError()
        for e, size in edges.items():
            if not edges[frozenset((p[v] for v in e))] == size:
                raise AssertionError()
        lookup = {frozenset(f['verts']): f for f in faces}
        for f in faces:
            target = lookup[frozenset((p[v] for v in f['verts']))]
            if not f['label'] == target['label']:
                raise AssertionError()
            a = [p[v] for v in f['verts']]
            b = target['verts']
            if not any((a == (b[s:] + b[:s])[::d] for s in range(len(b)) for d in (1, -1))):
                raise AssertionError()
    reductions = doc['reductions']
    if not len(reductions) == len(expect):
        raise AssertionError()
    seen = set()
    reps = {}
    for r in reductions:
        if not set(r) == {'source', 'representative', 'symmetry', 'hinge'}:
            raise AssertionError()
        src = tuple(r['source'])
        dst = tuple(r['representative'])
        if not (src in expect and src not in seen and (dst in expect)):
            raise AssertionError()
        seen.add(src)
        reps[src] = dst
        if not r['hinge'] == 'opposite':
            raise AssertionError()
        si = r['symmetry']
        if not (type(si) is int and 0 <= si < len(perms)):
            raise AssertionError()
        p = perms[si]
        if not [p[v] for v in expect[src]] == expect[dst]:
            raise AssertionError()
        if not faces[src[0]]['label'] == faces[dst[0]]['label']:
            raise AssertionError()
    if not seen == set(expect):
        raise AssertionError()
    if not all((reps[dst] == dst for dst in reps.values())):
        raise AssertionError()
    return dict(type=doc['name'], correspondences=len(expect), retained=sum((src == dst for src, dst in reps.items())), discarded=sum((src != dst for src, dst in reps.items())))

def mutations(doc):
    """Five different mathematical corruption classes, all must fail."""
    a = copy.deepcopy(doc)
    a['reductions'].pop()
    yield ('missing-correspondence', a)
    a = copy.deepcopy(doc)
    a['reductions'][0]['hinge'] = 'same'
    yield ('hinge', a)
    a = copy.deepcopy(doc)
    a['faces'][0]['label'] = 'wrong'
    yield ('label', a)
    a = copy.deepcopy(doc)
    a['symmetries'][0][0] = a['symmetries'][0][1]
    yield ('non-permutation', a)
    a = copy.deepcopy(doc)
    r = a['reductions'][0]
    dst = r['representative']
    dst[1] = (dst[1] + 1) % (2 * len(a['faces'][dst[0]]['verts']))
    yield ('ridge-order', a)

def documents(paths):
    for path in paths:
        data = json.load(open(path))
        yield from (data if isinstance(data, list) else [data])

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('certificates', nargs='+')
    ap.add_argument('--corruptions', action='store_true')
    a = ap.parse_args()
    counts = dict(types=0, correspondences=0, retained=0, discarded=0, corruptions_rejected=0)
    for doc in documents(a.certificates):
        r = check(doc)
        for k in ('correspondences', 'retained', 'discarded'):
            counts[k] += r[k]
        counts['types'] += 1
        if a.corruptions:
            for name, bad in mutations(doc):
                try:
                    check(bad)
                except (AssertionError, KeyError, IndexError):
                    counts['corruptions_rejected'] += 1
                else:
                    raise AssertionError('accepted corruption ' + name)
    print(json.dumps(counts, sort_keys=True))
if __name__ == '__main__':
    main()
