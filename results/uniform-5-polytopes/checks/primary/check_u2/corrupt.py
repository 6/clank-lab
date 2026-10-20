"""The two deliberate corruptions of the spec.

(a) delete one allowed cycle from a class that has a vertex figure using it:
    every vertex figure using that cycle must disappear;
(b) edit one cycle's facet name to a type not in the class: every user of
    the original cycle must disappear, with no new vertex figures.

usage: python3 corrupt.py CLASSES_JSON FACETS_JSON REF_SIGS_JSON
The targets are chosen deterministically from the uncorrupted result (see
choose()).
"""
import argparse, copy, json, os, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import search


def sigs(cls):
    found, stats, cpu = search.run_class(cls)
    return [json.loads(s) for s in sorted(found)], stats


def canon(cy):
    return search.canon_word(list(zip(cy['facets'], cy['cells'])))


def show(vf):
    return '%d facets %s' % (len(vf['facets']), ' '.join(
        '%s x%d' % (k, vf['facets'].count(k)) for k in sorted(set(vf['facets']))))


def corruption_a(cls, j):
    before, _ = sigs(cls)
    cw = canon(cls['cycles'][j])
    users = [vf for vf in before if cw in vf['cycles']]
    bad = copy.deepcopy(cls)
    del bad['cycles'][j]
    after, _ = sigs(bad)
    gone = [vf for vf in before if vf not in after]
    ok = (bool(users) and all(vf not in after for vf in users)
          and after == [vf for vf in before if vf not in users])
    lines = ['(a) class %d: deleted allowed cycle %d %s (p=%d)' % (
        cls['index'], j, json.dumps(cw), cls['cycles'][j]['p']),
        '    vertex figures before: %d, using the cycle: %d, after: %d' % (
            len(before), len(users), len(after))]
    for vf in users:
        lines.append('    using it: %s -> %s' % (show(vf), 'GONE' if vf not in after else 'STILL THERE'))
    for vf in after:
        if vf not in before:
            lines.append('    NEW after deletion: %s' % show(vf))
    lines.append('    verdict: %s' % ('PASS (every vertex figure using the cycle disappeared)'
                                     if ok else 'FAIL'))
    return ok, lines


def corruption_b(cls, j, k, new):
    before, _ = sigs(cls)
    cw = canon(cls['cycles'][j])
    users = [vf for vf in before if cw in vf['cycles']]
    bad = copy.deepcopy(cls)
    old = bad['cycles'][j]['facets'][k]
    bad['cycles'][j]['facets'][k] = new
    after, st = sigs(bad)
    lines = ['(b) class %d: cycle %d position %d facet %s -> %s (now %s)' % (
        cls['index'], j, k, old, new, json.dumps(canon(bad['cycles'][j]))),
        '    vertex figures before: %d, after: %d (search nodes %d, placements %d, '
        'interval prunes %d, combinatorial prunes %d)' % (
            len(before), len(after), st['nodes'], st['placements'], st['geo_prunes'],
            st['comb_prunes'])]
    for vf in before:
        if vf not in after:
            lines.append('    disappeared: %s' % show(vf))
    for vf in after:
        if vf not in before:
            lines.append('    appeared: %s' % show(vf))
    if before == after:
        lines.append('    no change')
    ok = (bool(users) and all(vf not in after for vf in users)
          and after == [vf for vf in before if vf not in users])
    lines.append('    verdict: %s' % (
        'PASS (exactly the original cycle users disappeared)' if ok else 'FAIL'))
    return ok, lines


def choose(classes, ref, names):
    """(a): the class with most vertex figures (ties: lowest index), its
    first cycle used by some but not all of them.  (b): the same class; the
    first (cycle, position, type) such that the new type is not in the
    class, has faces with both neighbouring cell labels meeting at an edge
    of the cycle's p (so it is not dropped by label/edge-type filters
    alone), in name order."""
    best = max(classes, key=lambda c: (len(ref[c['index']]), -c['index']))
    vfs = ref[best['index']]
    ja = None
    for j, cy in enumerate(best['cycles']):
        n = sum(1 for vf in vfs if canon(cy) in vf['cycles'])
        if 0 < n < len(vfs):
            ja = j
            break
    if ja is None:
        ja = next(j for j, cy in enumerate(best['cycles'])
                  if any(canon(cy) in vf['cycles'] for vf in vfs))
    present = set(K for cy in best['cycles'] for K in cy['facets'])
    names = sorted(names)
    for j, cy in enumerate(best['cycles']):
        if not any(canon(cy) in vf['cycles'] for vf in vfs):
            continue
        n = len(cy['facets'])
        for k in range(n):
            a, b = cy['cells'][k - 1], cy['cells'][k]
            for nm in names:
                if nm in present:
                    continue
                T = search.get_type(nm)
                for e, (fa, fb) in T.edge_faces.items():
                    if T.edge_p[e] == cy['p'] and \
                            {T.faces[fa]['label'], T.faces[fb]['label']} == {a, b}:
                        return best, ja, (j, k, nm)
    raise RuntimeError('no candidate for (b)')


def choose_b2(classes, ref, names):
    """(b2): a spurious type that survives every filter, so the gluing
    search has to try it: the first (class, cycle, position, type) in index
    and name order with the cycle used by a vertex figure, the new type not
    in the class, R_K < R certified, and the type kept by the edge-word
    type filter for some start."""
    for cls in classes:
        vfs = ref[cls['index']]
        if not vfs:
            continue
        present = set(K for cy in cls['cycles'] for K in cy['facets'])
        for j, cy in enumerate(cls['cycles']):
            if not any(canon(cy) in vf['cycles'] for vf in vfs):
                continue
            for k in range(len(cy['facets'])):
                for nm in sorted(names):
                    if nm in present:
                        continue
                    bad = copy.deepcopy(cls)
                    bad['cycles'][j]['facets'][k] = nm
                    types = {n: search.get_type(n)
                             for n in set(K for y in bad['cycles'] for K in y['facets'])}
                    S = search.ClassSearch(bad, types)
                    if nm not in S.types or not (S.geo[nm][0] ** 2).a > 0:
                        continue
                    if nm in S.usable_types(set(S.types), bad['cycles']):
                        return cls, j, k, nm
    raise RuntimeError('no candidate for (b2)')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('classes')
    ap.add_argument('facets', help='u2_facets_p10.json (facet type names)')
    ap.add_argument('ref', help='sigs json of the uncorrupted run')
    a = ap.parse_args()
    with open(a.classes) as stream:
        classes = json.load(stream)
    with open(a.ref) as stream:
        ref = {r['index']: r['vfs'] for r in json.load(stream)}
    with open(a.facets) as stream:
        names = [f['name'] for f in json.load(stream)]
    cls, ja, (jb, kb, nb) = choose(classes, ref, names)
    ok, la = corruption_a(cls, ja)
    ok_b, lb = corruption_b(cls, jb, kb, nb)
    c2, j2, k2, n2 = choose_b2(classes, ref, names)
    ok_b2, lb2 = corruption_b(c2, j2, k2, n2)
    lb2[0] = lb2[0].replace('(b)', '(b2)', 1)
    print('\n'.join(la + lb + lb2))
    return 0 if ok and ok_b and ok_b2 else 1


if __name__ == '__main__':
    sys.exit(main())
