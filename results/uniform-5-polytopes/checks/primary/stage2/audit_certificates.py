"""Primary replay: rebuild exact equivalences in checked cyclic indexing.

Cyclic starts and directions are presentation choices. Validate them against
the constructed cells, then compare every certificate field exactly.

Run the independent checker in a separate process as well.  This script's
corruptions check both acceptance predicates against the same five edits.
"""
import argparse
import json
from mpmath import iv
from exact_types import ExactTypeData
from check_equivalences import check, mutations, documents

def presented_certificate(T, faces):
    """Reindex exact correspondences; never change cells or symmetry orbits."""
    expected = T.certificate()
    if len(faces) != len(expected['faces']):
        raise ValueError('certificate face coverage differs from construction')
    orders = {}
    for fi, (face, true) in enumerate(zip(faces, expected['faces'], strict=True)):
        vs = face['verts']
        original = true['verts']
        if not any((vs == (original[s:] + original[:s])[::direction] for s in range(len(original)) for direction in (1, -1))):
            raise ValueError('certificate face is not a constructed cyclic order')
        expected['faces'][fi] = dict(verts=list(vs), label=true['label'], ps=[T.edge_p[frozenset((vs[i], vs[(i + 1) % len(vs)]))] for i in range(len(vs))])
        for start in range(len(vs)):
            for direction in (1, -1):
                ci = 2 * start + (direction == -1)
                orders[fi, ci] = tuple((vs[(start + direction * i) % len(vs)] for i in range(len(vs))))
    index = {(fi, order): (fi, ci) for (fi, ci), order in orders.items()}
    reductions = []
    for source, order in orders.items():
        images = []
        for si, permutation in enumerate(T.syms):
            image = tuple((permutation[v] for v in order))
            fi = T.face_of_vset[frozenset(image)]
            images.append((index[fi, image], si))
        representative, symmetry = min(images)
        reductions.append(dict(source=list(source), representative=list(representative), symmetry=symmetry, hinge='opposite'))

    def inventory(rows):
        return (len(rows), sum((r['source'] == r['representative'] for r in rows)))
    if inventory(reductions) != inventory(expected['reductions']):
        raise ValueError('cyclic reindexing changed correspondence counts')
    expected['reductions'] = reductions
    return expected

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('certificates', nargs='+')
    ap.add_argument('--corruptions', action='store_true')
    a = ap.parse_args()
    iv.prec = 200
    totals = dict(types=0, correspondences=0, retained=0, discarded=0, primary_corruptions_rejected=0, independent_corruptions_rejected=0)
    for doc in documents(a.certificates):
        T = ExactTypeData(doc['name'])
        expected = presented_certificate(T, doc['faces'])
        if not doc == expected:
            raise AssertionError('certificate differs from exact construction')
        r = check(doc)
        totals['types'] += 1
        for k in ['correspondences', 'retained', 'discarded']:
            totals[k] += r[k]
        if a.corruptions:
            for name, bad in mutations(doc):
                if not bad != expected:
                    raise AssertionError('primary accepted ' + name)
                totals['primary_corruptions_rejected'] += 1
                try:
                    check(bad)
                except (AssertionError, KeyError, IndexError):
                    totals['independent_corruptions_rejected'] += 1
                else:
                    raise AssertionError('independent accepted ' + name)
    print(json.dumps(totals, sort_keys=True))
if __name__ == '__main__':
    main()
