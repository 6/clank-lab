"""Compare completed independent output with the legacy JSON export only.

This file reads JSON, never legacy source or implementation modules.
The legacy [mid,rad] representation is interpreted with Arb(mid,rad),
preserving all rounding uncertainty in BOTH printed components.
"""
import argparse
import copy
import json
from flint import arb,fmpq,ctx


def contains_bracket(legacy,bracket):
    lo,hi = (fmpq(x) for x in bracket)
    ball = arb(*legacy)
    return ball.contains(arb(lo)) and ball.contains(arb(hi))


def compare(independent,legacy):
    ctx.prec = 320
    records = independent['records']
    ours = {r['name']:r for r in records}
    theirs = {r['name']:r for r in legacy}
    if not (len(ours) == len(records)):
        raise AssertionError('duplicate independent name')
    if not (len(theirs) == len(legacy)):
        raise AssertionError('duplicate reference name')
    if not (set(ours) == set(theirs)):
        raise AssertionError(('name set',set(ours)^set(theirs)))
    word_count = 0
    for name,r in ours.items():
        t = theirs[name]
        if not (set(r['aliases']) == set(t['aliases'])):
            raise AssertionError(('aliases',name))
        if not (len(t['aliases']) == len(set(t['aliases']))):
            raise AssertionError(('duplicate alias',name))
        if not (contains_bracket(t['R'],r['radius_bracket'])):
            raise AssertionError(('radius',name))
        words = {(w['p'],*sorted((w['A'],w['B']))):w for w in r['words']}
        old = {(w[0],*sorted(w[1:3])):w[3:5] for w in t['orbits']}
        if not (len(old) == len(t['orbits'])):
            raise AssertionError(('duplicate reference word',name))
        if not (len(words) == len(r['words'])):
            raise AssertionError(('duplicate independent word',name))
        if not (set(words) == set(old)):
            raise AssertionError(('word set',name,set(words)^set(old)))
        for key,w in words.items():
            if not (contains_bracket(old[key],w['alpha_bracket'])):
                raise AssertionError(('angle',name,key))
        word_count += len(words)
    if not (word_count == independent['counts']['words']):
        raise AssertionError()
    return {'status':'CERTIFIED','types':len(records),'words':word_count,
            'radius_and_angle_relation':'independent rational brackets contained in decoded reference balls',
            'multiplicities':'independently reconstructed; not present in reference JSON'}


def corruptions(independent,legacy):
    mutations = []
    def add(label,fn):
        data = copy.deepcopy(legacy)
        fn(data)
        mutations.append((label,data))
    add('missing type',lambda d:d.pop())
    add('duplicate type',lambda d:d.append(copy.deepcopy(d[0])))
    add('wrong canonical name',lambda d:d[0].__setitem__('name','wrong-name'))
    add('missing alias',lambda d:d[0]['aliases'].pop())
    add('wrong radius',lambda d:d[0].__setitem__('R',['1','0']))
    add('missing word',lambda d:d[0]['orbits'].pop())
    add('duplicate word',lambda d:d[0]['orbits'].append(copy.deepcopy(d[0]['orbits'][0])))
    add('wrong polygon',lambda d:d[0]['orbits'][0].__setitem__(0,4))
    add('wrong cell',lambda d:d[0]['orbits'][0].__setitem__(1,'cube'))
    add('wrong angle',lambda d:d[0]['orbits'][0].__setitem__(slice(3,5),['1','0']))
    rejected = []
    for label,data in mutations:
        try:
            compare(independent,data)
        except (AssertionError,ValueError,KeyError):
            rejected.append(label)
        else:
            raise AssertionError(('accepted corruption',label))
    return {'status':'CERTIFIED','corruptions_rejected':len(rejected),'labels':rejected}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('independent')
    parser.add_argument('reference')
    parser.add_argument('--corruptions',action='store_true')
    args = parser.parse_args()
    ours = json.load(open(args.independent))
    theirs = json.load(open(args.reference))
    print(json.dumps(compare(ours,theirs),sort_keys=True))
    if args.corruptions:
        print(json.dumps(corruptions(ours,theirs),sort_keys=True))
