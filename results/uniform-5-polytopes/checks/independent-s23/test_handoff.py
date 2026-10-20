"""Corruptions of the independent audit's mathematical input premises."""
from copy import deepcopy
import json
from pathlib import Path
from unittest.mock import patch
from stage2 import search_class
from stage3 import check_class
from audit_stage3 import audit
from s3_controls import Provider,FullSimplexFacet,simplex_class
import models


def rejected(call):
    try:call()
    except ValueError:return
    raise AssertionError('corruption accepted')


def main():
    c=simplex_class();provider=Provider();names=['A500001']
    s=search_class(c,{'A40001':FullSimplexFacet()}).record(True)
    r=check_class(s,provider,names)
    if not (audit([c],[s],[r],provider,names)['status']=='PASS'):
        raise AssertionError()
    bad=deepcopy(c);bad['cycles']=[]
    # This really IS complete for the wrong input. Its output must never
    # certify coverage of the original pinned simplex class.
    empty=search_class(bad,{}).record(True)
    result=check_class(empty,provider,names)
    if not (empty['status']=='COMPLETE' and result['status']=='COMPLETE'):
        raise AssertionError()
    rejected(lambda:audit([c],[empty],[result],provider,names))
    rejected(lambda:audit([c],[s],[r],provider,[]))
    missing=deepcopy(s);del missing['input_class_sha256']
    if not (check_class(missing,provider,names)['status']=='OPEN'):
        raise AssertionError()
    changed=deepcopy(r);changed['input_class_sha256']='0'*64
    rejected(lambda:audit([c],[s],[changed],provider,names))
    # Damage an exceptional cell label before preflight. It must trigger
    # validation failure/OPEN, never an OUTSIDE-LIBRARY decision.
    source=models.MODEL_DATA/'q5_certificate.json'
    certificate=json.loads(source.read_text())
    next(m for m in certificate['models'] if m['name']=='sadi')['cells'][0]['label']='cube'
    text=json.dumps(certificate);original=Path.read_text
    def read(path,*args,**kwargs):
        return text if path==source else original(path,*args,**kwargs)
    def clear():
        models.exceptional.cache_clear();models.facet_cell_types.cache_clear()
        models.facet_polygon_sizes.cache_clear();models.known_facet_types.cache_clear()
    clear()
    try:
        with patch.object(Path,'read_text',read):
            outcome=check_class(s,models,['prism-sadi'])
        if not (outcome['status']=='OPEN'):
            raise AssertionError(outcome)
        if not (outcome.get('unbuilt_known_models',[{}])[0].get('name')=='prism-sadi'):
            raise AssertionError(outcome)
        if not (not any(r.get('status')=='OUTSIDE-LIBRARY' for r in outcome.get('identification',{}).get('known',[]))):
            raise AssertionError(outcome)
    finally:clear()
    print('PASS input-cycle, missing/changed class binding, known-list, and preflight exceptional-label corruptions')


if __name__=='__main__':main()
