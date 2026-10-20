"""Checkpointed independent stage-2 replay. Outputs and large state in scratch."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import sys
import time
from flint import ctx
from geometry import Undecided
from exact import Undecided as ModelUndecided
from stage2 import search_class, equivalences
from check_equivalence import check
from provenance import model_data_hashes
from runtime_versions import require_versions


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('input',type=Path)
    ap.add_argument('output',type=Path)
    ap.add_argument('--ids',help='comma-separated original class indices')
    ap.add_argument('--bits',type=int,default=320)
    ap.add_argument('--node-limit',type=int)
    ap.add_argument('--states',action='store_true')
    ap.add_argument('--resume',action='store_true')
    args=ap.parse_args()
    require_versions()
    if args.bits<320: ap.error('at least 320 bits required')
    ctx.prec=args.bits
    from models import facet
    classes=json.loads(args.input.read_text())
    if args.ids is not None:
        ids={int(s) for s in args.ids.split(',')}
        classes=[c for c in classes if c['index'] in ids]
        if {c['index'] for c in classes}!=ids: ap.error('requested index absent')
    args.output.parent.mkdir(parents=True,exist_ok=True)
    provenance={'input_sha256':digest(args.input),'bits':args.bits,
                'model_data_sha256':model_data_hashes(),
                'sources':{p.name:digest(p) for p in sorted(Path(__file__).parent.glob('*.py'))}}
    pin=args.output.with_suffix(args.output.suffix+'.provenance.json')
    completed={}
    if args.resume and args.output.exists():
        if json.loads(pin.read_text())!=provenance:
            raise ValueError('source or input changed; use new output')
        for line in args.output.read_text().splitlines():
            row=json.loads(line)
            if row['status']=='COMPLETE': completed[row['index']]=row
    elif args.output.exists():
        raise ValueError('output exists; use --resume or a new path')
    else:
        pin.write_text(json.dumps(provenance,indent=2)+'\n')
    models={};model_errors={};stats=[]
    with args.output.open('a') as out:
        for c in classes:
            if c['index'] in completed: continue
            start=time.process_time()
            try:
                names=sorted({n for cyc in c['cycles'] for n in cyc['facets']})
                for name in names:
                    if name in model_errors: raise Undecided(model_errors[name])
                    if name not in models:
                        try:
                            m=facet(name)
                            cert=equivalences(m)[1]; check(m,cert)
                            models[name]=m
                        except (Undecided,ModelUndecided) as e:
                            model_errors[name]=str(e);raise
                model_seconds=time.process_time()-start
                result=search_class(c,models,args.node_limit)
                row=result.record(args.states)
                row['statistics']['model_cpu_seconds']=model_seconds
            except (Undecided,ModelUndecided,NotImplementedError) as e:
                row={'index':c['index'],'R':c['R'],'status':'OPEN','vfs':[],
                     'open_reasons':[str(e)],'statistics':{'cpu_seconds':time.process_time()-start}}
            out.write(json.dumps(row,sort_keys=True)+'\n');out.flush();os.fsync(out.fileno())
            stats.append(row['status'])
            print(json.dumps({'index':row['index'],'status':row['status'],'vfs':len(row['vfs']),'statistics':row['statistics']}),flush=True)
    return int('OPEN' in stats)


if __name__=='__main__': sys.exit(main())
