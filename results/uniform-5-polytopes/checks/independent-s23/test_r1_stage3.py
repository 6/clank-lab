"""R1 end-to-end control + uncertainty corruptions; requires new models.py."""
import json
from unittest.mock import patch
from flint import arb,ctx
from geometry import Undecided,ball_interval
from r1_probe import make_class
import r1_provider
from stage2 import search_class
from stage3 import check_class,decode_state,group_states
from s3_stars import reconstruct_star
from s3_develop import develop
import s3_develop


def main():
    ctx.prec=320
    c,models=make_class(r1_provider)
    s2=search_class(c,models)
    if not (not s2.open_reasons):
        raise AssertionError()
    result=check_class(s2.record(include_states=True),r1_provider,['A510001'],development_depth=6,node_limit=1000)
    if not (result['status']=='COMPLETE'):
        raise AssertionError(result)
    if not (sorted(r['status'] for r in result['realisations'])==['KNOWN','REFUTED']):
        raise AssertionError()
    if not (all(r['radius']['status']=='UNIQUE' and r['local_uniqueness']['status']=='FORCED' for r in result['realisations'])):
        raise AssertionError()
    extra=next(r for r in result['realisations'] if r['status']=='REFUTED')
    if not (extra['development']['statistics']['open']==0):
        raise AssertionError()
    # Reconstruct EXACT same representative used by the trusted checker.
    state=s2.states[extra['s2_states'][0]]
    star=reconstruct_star(state,ball_interval(*c['R']),models)
    original=s3_develop.merge_candidate
    calls=0
    def corrupted_merge(*args):
        nonlocal calls
        calls+=1
        if calls==2:raise Undecided('injected recursive point identity uncertainty')
        return original(*args)
    with patch('s3_develop.merge_candidate',corrupted_merge):
        bad=develop(star,models,max_depth=6,node_limit=1000,root_forced=True)
    if not (bad['status']=='OPEN' and any('injected' in r for r in bad['reasons'])):
        raise AssertionError(bad)
    with patch('s3_develop.conditional_same',side_effect=Undecided('injected initial identity uncertainty')):
        bad=develop(star,models,max_depth=6,node_limit=1000,root_forced=True)
    if not (bad['status']=='OPEN'):
        raise AssertionError(bad)
    if not (develop(star,models,max_depth=6,node_limit=0,root_forced=True)['status']=='OPEN'):
        raise AssertionError()
    # Complete coverage cannot be inferred from signatures only.
    record=s2.record(include_states=True);record['status']='OPEN'
    if not (check_class(record,r1_provider,['A510001'])['status']=='OPEN'):
        raise AssertionError()
    checks=result['identification']['known'][0]['checks']
    if not (any(q['status']=='NO' and q['frames']==48 for q in checks)):
        raise AssertionError()
    print('PASS R1 restricted-type realisations: unique radius, exact elimination, local uniqueness, finite extra refutation; initial+recursive identity/node-limit corruptions OPEN')

if __name__=='__main__':main()
