#!/usr/bin/env python3
"""Independent rigorous S3, derived from paper/main.tex mathematical statements.

Usage: python stage3.py --states s2-complete.jsonl --models models --known
       ../check_u3/inputs/u3_known_p6.json --output own-s3.jsonl

Only complete states from the independently implemented S2 and exact model
construction code are executable inputs. Missing facts/resource limits or
undecided arithmetic produce OPEN. Output is frozen before any comparison.
"""
import argparse
import hashlib
import importlib
import json
import sys
import time
from concurrent.futures import ProcessPoolExecutor
import multiprocessing
from pathlib import Path
from flint import arb,ctx
from geometry import Undecided,Impossible,ball_interval
from s3_radius import unique_radius
from s3_cycles import closure_cycles
from s3_stars import reconstruct_star,correspondence_isomorphisms,local_uniqueness,separation_obstruction
from s3_identify import identify_by_elimination
from s3_develop import develop
from s3_orient import expand_orientations,orientation_options
from provenance import json_digest,file_digest,model_data_hashes,scientific_records
from runtime_versions import require_versions


def decode_state(s):
    return dict(s,points=[tuple(arb(x) for x in p) for p in s['points']])


def group_states(states,models,node_limit=None):
    """Keep proof witnesses; equal signatures alone NEVER merge states."""
    groups=[]
    for si,s in enumerate(states):
        joined=False
        for g in groups:
            t=g['state']
            if s['signature']!=t['signature']: continue
            maps=correspondence_isomorphisms(s,t,models,node_limit,first_only=True)
            if maps:
                g['states'].append(si);g['maps'].append(list(maps[0]));joined=True;break
        if not joined: groups.append({'state':s,'states':[si],'maps':[]})
    return groups


def check_class(record,provider,known_names,*,node_limit=None,frame_limit=None,development_depth=6,
                development_node_limit=None,coset_reduction=True,support_pruning=True):
    output={'index':record['index'],'R':record['R'],'status':'OPEN','realisations':[]}
    pin=record.get('input_class_sha256')
    if not isinstance(pin,str) or len(pin)!=64 or any(c not in '0123456789abcdef' for c in pin):
        output['reason']='missing S2 input class binding';return output
    output['input_class_sha256']=pin
    output['known_names_sha256']=json_digest(known_names)
    if record.get('status')!='COMPLETE' or record.get('open_reasons'):
        output['reason']='S2 class coverage incomplete';return output
    if 'states' not in record:
        output['reason']='full S2 states required, signatures alone insufficient';return output
    try:
        states=[decode_state(s) for s in record['states']]
        declared=getattr(provider,'dimension',None)
        if declared is not None and (not isinstance(declared,int) or declared<3):
            raise ValueError('invalid provider dimension')
        for state in states:
            points=state['points']
            dimension=len(points[0])+1 if points else 0
            if (dimension<3 or any(len(p)!=dimension-1 for p in points) or
                    (declared is not None and dimension!=declared)):
                raise ValueError('provider/S2 dimension mismatch')
        expected_count=record.get('statistics',{}).get('complete_states')
        if expected_count is not None and expected_count!=len(states):
            raise Undecided('S2 complete-state count disagrees with supplied states')
        if 'vfs' in record:
            key=lambda sig:json.dumps(sig,sort_keys=True,separators=(',',':'))
            if {key(s['signature']) for s in states}!={key(v) for v in record['vfs']}:
                raise Undecided('S2 signature coverage disagrees with supplied states')
        names=sorted({f['name'] for s in states for f in s['facets']})
        models={name:provider.facet(name) for name in names}
        # Full-star orientation defects are restored before grouping.
        # A rejection-only separation scan removes impossible orientations
        # before identification, preserving sole-candidate lazy elimination.
        defect_types={n for n,m in models.items() if len(orientation_options(m))>1}
        expanded=[]
        for si,s in enumerate(states):
            for full in expand_orientations(s,models,node_limit):
                full['s2_state_index']=si;expanded.append(full)
        states=expanded
        groups=group_states(states,models,node_limit)
        stars=[];active=[]
        R=ball_interval(*record['R'])
        for gi,g in enumerate(groups):
            r={'states':g['states'],'congruence_maps':g['maps'],
               'signature':g['state']['signature'],'status':'OPEN',
               's2_states':[states[k]['s2_state_index'] for k in g['states']],
               'orientations':[states[k]['orientation'] for k in g['states']]}
            output['realisations'].append(r)
            try:
                cycles=closure_cycles(g['state'],models)
                r['radius']=unique_radius(record['R'],cycles)
                star=reconstruct_star(g['state'],R,models)
                if defect_types:
                    witness=separation_obstruction(star,defect_types)
                    if witness is not None:
                        r['status']='REFUTED';r['reason']=witness['reason']
                        r['separation_witness']=witness
                        continue
                stars.append(star);active.append(gi)
            except Impossible as e:
                r['status']='REFUTED';r['reason']=str(e)
            except Undecided as e:
                r['reason']=str(e)
                # An unresolved state MUST remain in elimination coverage.
                output['reason']='unresolved full-star reconstruction';return output
        known=[];model_opens=[];preflight_reports=[]
        for name in known_names:
            try:
                if hasattr(provider,'known_facet_types'):
                    # This provider API derives the COMPLETE type set exactly
                    # from parabolic/product construction rules. Library
                    # membership is an independent necessary entry condition;
                    # it needs no number field or full5D orbit construction.
                    types=tuple(provider.known_facet_types(name))
                    if not types:raise Undecided('empty construction facet-type proof')
                    if not set(types).issubset(set(names)):
                        preflight_reports.append({'name':name,'status':'OUTSIDE-LIBRARY',
                            'facet_types':list(types),
                            'reason':'exact construction facet-type precondition fails'})
                        continue
                known.append(provider.known(name))
            except (Undecided,NotImplementedError,KeyError) as e:
                model_opens.append({'name':name,'reason':str(e)})
        ident=identify_by_elimination(stars,known,record['R'],names,True,frame_limit)
        if preflight_reports:
            ident['known'].extend(preflight_reports)
            order={name:i for i,name in enumerate(known_names)}
            ident['known'].sort(key=lambda q:order[q['name']])
        output['identification']=ident
        if model_opens: output['unbuilt_known_models']=model_opens
        for i,star in enumerate(stars):
            r=output['realisations'][active[i]]
            try:
                r['local_uniqueness']=local_uniqueness(star,models,node_limit=node_limit)
            except Undecided as e:
                r['local_uniqueness']={'status':'OPEN','reason':str(e)}
            except Impossible as e:
                r['status']='REFUTED';r['reason']=str(e);continue
            matches=ident['identified'][i]
            if matches and r['radius']['status']=='UNIQUE' and r['local_uniqueness']['status']=='FORCED':
                r['status']='KNOWN';r['names']=matches
            elif not matches:
                r['development']=develop(star,models,max_depth=development_depth,
                                         node_limit=(node_limit if development_node_limit is None
                                                     else development_node_limit),
                                         coset_reduction=coset_reduction,
                                         support_pruning=support_pruning,
                                         # The development shortcut may choose the first root-compatible
                                         # map only when ALL such maps passed the one-step coset test.
                                         # Collar forcing has additionally excluded some of those maps.
                                         root_forced=(r['local_uniqueness']['status']=='FORCED'
                                                      and r['local_uniqueness'].get('method') is None))
                if r['development']['status']=='REFUTED': r['status']='REFUTED'
        if all(r['status'] in ('KNOWN','REFUTED') for r in output['realisations']):
            # Missing Q models do not invalidate independent positive proofs,
            # but a complete names audit remains OPEN until all are built.
            output['status']='COMPLETE' if not model_opens and ident['status']=='COMPLETE' else 'OPEN'
        return output
    except Exception as e:
        # Provider exact.Undecided may be a different exception class. Any
        # uncaught construction/arithmetic/programming failure is OPEN.
        output['reason']=f'{type(e).__name__}: {e}';return output


def _init_worker(module,names,bits,options):
    # Arb precision and model caches belong to this process. No arithmetic
    # objects or mutable model state are shared between concurrent workers.
    global _worker_provider,_worker_names,_worker_options
    ctx.prec=bits
    _worker_provider=importlib.import_module(module)
    _worker_names=names;_worker_options=options


def _check_record(record):
    return check_class(record,_worker_provider,_worker_names,**_worker_options)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--states',required=True);p.add_argument('--models',required=True)
    p.add_argument('--known',required=True);p.add_argument('--output',required=True)
    p.add_argument('--index',type=int);p.add_argument('--bits',type=int,default=320)
    p.add_argument('--node-limit',type=int);p.add_argument('--frame-limit',type=int)
    p.add_argument('--development-depth',type=int,default=6)
    p.add_argument('--development-node-limit',type=int)
    p.add_argument('--no-development-support-pruning',action='store_true',
                   help='retain historical development without convex-support cuts')
    p.add_argument('--no-development-coset-reduction',action='store_true',
                   help='retain exhaustive historical development for diagnostics')
    p.add_argument('--jobs',type=int,default=1,help='independent worker processes; default one')
    a=p.parse_args()
    require_versions()
    if a.bits<256: p.error('rigorous S3 requires at least 256 bits')
    if a.jobs<1:p.error('--jobs must be positive')
    if a.development_node_limit is not None and a.development_node_limit<1:
        p.error('--development-node-limit must be positive')
    ctx.prec=a.bits
    provider=importlib.import_module(a.models)
    # Pin source bytes BEFORE work, so later edits cannot change the receipt
    # of code already loaded by a running worker.
    source_hashes={}
    source_paths={f.name:f for f in Path(__file__).parent.glob('*.py')}
    source_paths.update({f.stem:f for f in Path(__file__).parent.glob('s3_*.py')})
    for name in ('geometry',a.models,'models','exact'):
        module=sys.modules.get(name)
        if module is not None and getattr(module,'__file__',None):
            source_paths['module:'+name]=Path(module.__file__)
    for name,path in source_paths.items():
        if path.is_file():source_hashes[name]=hashlib.sha256(path.read_bytes()).hexdigest()
    started=time.monotonic()
    s2_provenance=Path(a.states+'.provenance.json')
    provenance_record=json.loads(s2_provenance.read_text()) if s2_provenance.exists() else None
    data_hashes=(provider.model_data_hashes() if hasattr(provider,'model_data_hashes')
                 else model_data_hashes())
    names=json.loads(Path(a.known).read_text())
    data=Path(a.states).read_text().strip()
    records=json.loads(data) if data.startswith('[') else [json.loads(s) for s in data.splitlines() if s.strip()]
    if isinstance(records,dict): records=[records]
    records=[c for c in records if a.index is None or c['index']==a.index]
    options={'node_limit':a.node_limit,'frame_limit':a.frame_limit,'development_depth':a.development_depth,
             'development_node_limit':a.development_node_limit,
             'coset_reduction':not a.no_development_coset_reduction,
             'support_pruning':not a.no_development_support_pruning}
    pool=None
    if a.jobs==1:
        results=(check_class(c,provider,names,**options) for c in records)
    else:
        pool=ProcessPoolExecutor(max_workers=a.jobs,mp_context=multiprocessing.get_context('spawn'),
                                 initializer=_init_worker,initargs=(a.models,names,a.bits,options))
        results=pool.map(_check_record,records,chunksize=1)
    outputs=[]
    try:
        with open(a.output,'w') as out:
            for c,result in zip(records,results,strict=True):
                if result['index']!=c['index']:raise ValueError('worker class order mismatch')
                out.write(json.dumps(result,sort_keys=True)+'\n');out.flush();outputs.append(result)
                print(json.dumps({'index':c['index'],'status':result['status'],
                                  'realisations':len(result['realisations'])}),flush=True)
    finally:
        if pool is not None:pool.shutdown(wait=True,cancel_futures=True)
    receipt={'scientific_results':scientific_records(a.output),'bits':ctx.prec,
             'scientific_states':scientific_records(a.states),
             'classes':len(outputs),'open':sum(c['status']=='OPEN' for c in outputs),
             'comparison_performed':False,'source':'paper/main.tex mathematics only',
             'source_sha256':source_hashes,'elapsed_seconds':time.monotonic()-started,
             's2_provenance':provenance_record,
             'model_data_sha256':data_hashes,
             'jobs':a.jobs,
             'development_options':{'depth':a.development_depth,
                                    'node_limit':a.development_node_limit,
                                    'coset_reduction':not a.no_development_coset_reduction,
                                    'support_pruning':not a.no_development_support_pruning},
             'known_names_sha256':hashlib.sha256(Path(a.known).read_bytes()).hexdigest()}
    Path(a.output+'.frozen.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt),flush=True)
    return int(not outputs or any(c['status']!='COMPLETE' for c in outputs))

if __name__=='__main__': sys.exit(main())
