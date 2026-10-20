#!/usr/bin/env python3
"""Independent exact-decimal coverage audit of FROZEN own S3 outputs.

This does not re-prove Arb witnesses. Re-run stage3.py for geometric proof.
It detects omitted/duplicated classes, narrowed class intervals, missing
states/orientations/signatures, OPEN verdicts, and receipt hash mismatch.
No comparison with any historical stage2/3 result is performed.
"""
import argparse,hashlib,importlib,json,sys
from fractions import Fraction
from pathlib import Path
from stage3 import decode_state
from s3_orient import expand_orientations
from provenance import parsed_json, json_digest,file_digest,authenticate,model_data_hashes,check_frozen_science,source_document


def read(path):
    s=Path(path).read_text().strip()
    x=parsed_json(s) if s.startswith('[') else [parsed_json(t) for t in s.splitlines() if t.strip()]
    return x if isinstance(x,list) else [x]


def equal_interval(a,b):
    return len(a)==len(b)==2 and all(Fraction(x)==Fraction(y) for x,y in zip(a,b,strict=True))


def indexed(records,label):
    result={}
    for c in records:
        if c['index'] in result:raise ValueError(f'duplicate {label} class {c["index"]}')
        result[c['index']]=c
    return result


def audit(classes,states,results,provider,known_names,require_complete=True):
    pins=indexed(classes,'pinned');ss=indexed(states,'S2');rr=indexed(results,'S3')
    if set(pins)!=set(ss) or set(pins)!=set(rr): raise ValueError('class coverage mismatch')
    nreal=0;nsig=0
    for i,pin in pins.items():
        s=ss[i];r=rr[i]
        class_pin=json_digest(pin)
        if s.get('input_class_sha256')!=class_pin or r.get('input_class_sha256')!=class_pin:
            raise ValueError(f'class {i}: original cycle input binding mismatch')
        if r.get('known_names_sha256')!=json_digest(known_names):
            raise ValueError(f'class {i}: intended known-name list binding mismatch')
        if not equal_interval(pin['R'],s['R']) or not equal_interval(pin['R'],r['R']):
            raise ValueError(f'class {i}: whole pinned interval changed')
        if require_complete and (s['status']!='COMPLETE' or s.get('open_reasons')):
            raise ValueError(f'class {i}: S2 OPEN')
        if require_complete and r['status']!='COMPLETE': raise ValueError(f'class {i}: S3 OPEN')
        original=[decode_state(t) for t in s['states']]
        if s.get('statistics',{}).get('complete_states',len(original))!=len(original):
            raise ValueError('S2 state count mismatch')
        sigkey=lambda x:json.dumps(x,sort_keys=True,separators=(',',':'))
        sigs={sigkey(t['signature']) for t in original}
        if 'vfs' in s and sigs!={sigkey(t) for t in s['vfs']}:raise ValueError('S2 signature coverage mismatch')
        names={f['name'] for t in original for f in t['facets']}
        models={name:provider.facet(name) for name in names}
        expanded=[]
        for si,t in enumerate(original):
            for full in expand_orientations(t,models):expanded.append((si,full['orientation']))
        seen=set();seen_sigs=set()
        for real in r['realisations']:
            nreal+=1;seen_sigs.add(sigkey(real['signature']))
            ids=real['states'];sources=real['s2_states'];orientations=real['orientations']
            if len(ids)!=len(sources) or len(ids)!=len(orientations):raise ValueError('orientation witness length mismatch')
            for j,si,orientation in zip(ids,sources,orientations,strict=True):
                if j in seen or not 0<=j<len(expanded):raise ValueError('duplicate/missing expanded-state index')
                seen.add(j)
                if expanded[j]!=(si,orientation):raise ValueError('expanded orientation coverage mismatch')
            if require_complete:
                if real['status']=='KNOWN':
                    if real.get('radius',{}).get('status')!='UNIQUE' or not equal_interval(real['radius']['R'],pin['R']):
                        raise ValueError('KNOWN radius not unique on whole pinned class')
                    if real.get('local_uniqueness',{}).get('status')!='FORCED' or not real.get('names'):
                        raise ValueError('KNOWN without forcing/name')
                elif real['status']=='REFUTED':
                    if 'development' in real:
                        if real['development']['status']!='REFUTED' or real['development']['statistics']['open']:
                            raise ValueError('development uncertainty in refutation')
                    elif not real.get('reason'): raise ValueError('refutation lacks contradiction reason')
                else:raise ValueError('OPEN realisation')
        if seen!=set(range(len(expanded))) or seen_sigs!=sigs:raise ValueError('full realisation/signature coverage mismatch')
        nsig+=len(sigs)
    return {'status':'PASS','classes':len(pins),'signatures':nsig,'realisations':nreal,'historical_comparison':False}


def authenticate_sources(provenance,receipt,provider_name):
    """Match both complete source inventories to local executable bytes.

    Receipt links alone authenticate only the supplied documents. Rebinding
    those links must not allow fabricated source maps to stand for this code.
    Names are derived here, never interpreted as paths supplied by a receipt.
    """
    here=Path(__file__).resolve().parent
    local={path.name:file_digest(path) for path in here.glob('*.py')}
    prose_free=lambda mapping: {k:v for k,v in mapping.items() if Path(k).suffix.lower() not in {'.md','.tex','.pdf','.rst'}} if isinstance(mapping,dict) else mapping
    if prose_free(provenance.get('sources'))!=local:
        raise ValueError('S2 source inventory or digest mismatch')
    expected=dict(local)
    expected.update({path.stem:file_digest(path) for path in here.glob('s3_*.py')})
    for name in ('geometry',provider_name,'models','exact'):
        module=sys.modules.get(name)
        if module is not None and getattr(module,'__file__',None):
            expected['module:'+name]=file_digest(module.__file__)
    if prose_free(receipt.get('source_sha256'))!=expected:
        raise ValueError('S3 source inventory or digest mismatch')


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--classes',required=True);p.add_argument('--states',required=True)
    p.add_argument('--results',required=True);p.add_argument('--models',required=True)
    p.add_argument('--known',required=True);p.add_argument('--pmax',type=int,choices=(6,10,16),required=True)
    p.add_argument('--receipt',required=True);p.add_argument('--allow-open',action='store_true')
    a=p.parse_args();receipt=parsed_json(Path(a.receipt).read_text())
    class_hash=authenticate(a.classes,f'producer-p{a.pmax}/u2_classes_p{a.pmax}.json')
    known_hash=authenticate(a.known,f'producer-p{a.pmax}/u3_known_p{a.pmax}.json')
    s2_provenance=Path(a.states+'.provenance.json')
    provenance=parsed_json(s2_provenance.read_text())
    if provenance['input_sha256']!=class_hash:raise ValueError('S2 searched a different original input')
    # The provenance document is parsed below; its old byte hash is historical.
    # Complete actual checker/input inventories are still authenticated.
    if receipt.get('known_names_sha256')!=known_hash:raise ValueError('S3 known-name input mismatch')
    provider=importlib.import_module(a.models)
    authenticate_sources(provenance,receipt,a.models)
    if receipt.get('s2_provenance') is not None and source_document(receipt['s2_provenance']) != source_document(provenance):
        raise ValueError('S2 parsed provenance scientific fields differ')
    if provenance.get('model_data_sha256')!=model_data_hashes() or receipt.get('model_data_sha256')!=model_data_hashes():
        raise ValueError('mathematical model input data mismatch')
    check_frozen_science(receipt,a.results)
    check_frozen_science(receipt,a.states,'scientific_states')
    print(json.dumps(audit(read(a.classes),read(a.states),read(a.results),provider,parsed_json(Path(a.known).read_text()),not a.allow_open)))

if __name__=='__main__':main()
