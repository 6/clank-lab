"""Small controls of the mathematical decisions, including hostile inputs."""
from copy import deepcopy
from flint import arb
from geometry import identity, Undecided, Impossible, positive_sqrt
from control import SimplexFacet, simplex_class
from stage2 import search_class, equivalences
from check_equivalence import check
from combinatorics import word_key, word_variants


def raises(kind,fn):
    try: fn()
    except kind: return
    raise AssertionError(f'{kind.__name__} not raised')


def main():
    m=SimplexFacet();models={m.name:m};c=simplex_class()
    good=search_class(c,models)
    if not (not good.open_reasons and len(good.states)==1):
        raise AssertionError()
    if not (len(good.states[0]['points'])==len(good.states[0]['facets'])==5):
        raise AssertionError()
    if not (len(good.states[0]['signature']['cycles'])==10):
        raise AssertionError()
    # A proper exact subgroup must retain exactly the same signatures.
    m0=SimplexFacet();m0.stabilizers=[p for p in m0.stabilizers if p[0]==0]
    unreduced=search_class(c,{m0.name:m0})
    if not (not unreduced.open_reasons):
        raise AssertionError()
    if not (unreduced.record()['vfs']==good.record()['vfs']):
        raise AssertionError()
    if not (identity((arb(0),),(arb(0,'1e-50'),))):
        raise AssertionError()
    if not (not identity((arb(0),),(arb(2),))):
        raise AssertionError()
    raises(Impossible,lambda:identity((arb(0),),(arb('0.5'),)))
    raises(Undecided,lambda:identity((arb(0),),(arb(0,2),)))
    raises(Undecided,lambda:positive_sqrt(arb(0,1)))
    raises(Impossible,lambda:positive_sqrt(arb(-1)))
    _,cert=equivalences(m)
    if not (check(m,cert)==24 and len(cert['retained'])==1):
        raise AssertionError()
    bad=[]
    b=deepcopy(cert);b['records'].pop();bad.append(b)
    b=deepcopy(cert);b['options'].pop();bad.append(b)
    b=deepcopy(cert);b['records'][1]['permutation']=[0]*4;bad.append(b)
    b=deepcopy(cert);b['records'][1]['representative']=500;bad.append(b)
    b=deepcopy(cert);b['records'][1]['permutation']=list(range(4));bad.append(b)
    for b in bad: raises(ValueError,lambda:check(m,b))
    c0=deepcopy(c);c0['cycles']=[]
    result=search_class(c0,models)
    if not (not result.open_reasons and not result.states):
        raise AssertionError()
    c0=deepcopy(c);c0['cycles'][0]['p']=4
    result=search_class(c0,models)
    if not (not result.open_reasons and not result.states):
        raise AssertionError()
    c0=deepcopy(c);c0['R']=['0.60','0.80']
    if not (search_class(c0,models).open_reasons):
        raise AssertionError()
    if not (search_class(c,models,node_limit=1).open_reasons):
        raise AssertionError()
    # Reversal shifts the cell labels: c_i always stays between K_i,K_i+1.
    w=(('A','x'),('B','y'),('C','z'),('D','t'))
    if not (word_key(w)==word_key((('A','t'),('D','z'),('C','y'),('B','x')))):
        raise AssertionError()
    if not (all(word_key(v)==word_key(w) for v in word_variants(w))):
        raise AssertionError()
    print('PASS simplex gluing, 5 equivalence corruptions, 2 cycle corruptions, uncertainty, node-limit and cyclic-word controls')


if __name__=='__main__': main()
