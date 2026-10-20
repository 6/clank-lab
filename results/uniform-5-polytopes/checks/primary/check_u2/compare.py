"""Compare this checker's sigs_p10.json with the producer's file.

usage: python3 compare.py MINE.json PRODUCER.json
Compares per class the sets of signatures (facets multiset as sorted list,
cycles as sorted list of canonical words), independent of key order and
list order of vertex figures.
"""
import json, sys


def norm(vf):
    return json.dumps({'facets': sorted(vf['facets']),
                       'cycles': sorted(vf['cycles'])}, sort_keys=True)


def main(a, b):
    A = {r['index']: r['vfs'] for r in json.load(open(a))}
    B = {r['index']: r['vfs'] for r in json.load(open(b))}
    diffs = []
    for i in sorted(set(A) | set(B)):
        if i not in A or i not in B:
            diffs.append('class %d only in %s' % (i, 'mine' if i in A else 'producer'))
            continue
        sa = [norm(v) for v in A[i]]
        sb = [norm(v) for v in B[i]]
        if len(set(sa)) != len(sa) or len(set(sb)) != len(sb):
            diffs.append('class %d: duplicate signatures (mine %d/%d, producer %d/%d)' % (
                i, len(set(sa)), len(sa), len(set(sb)), len(sb)))
        for s in sorted(set(sa) - set(sb)):
            diffs.append('class %d: only mine: %s' % (i, s))
        for s in sorted(set(sb) - set(sa)):
            diffs.append('class %d: only producer: %s' % (i, s))
    print('classes: mine %d, producer %d; vertex figures: mine %d, producer %d' % (
        len(A), len(B), sum(map(len, A.values())), sum(map(len, B.values()))))
    print('differences: %d' % len(diffs))
    for d in diffs:
        print(d)
    return 1 if diffs else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1], sys.argv[2]))
