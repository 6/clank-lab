#!/usr/bin/env python3
"""Plant semantic corruptions, refreshing hashes so hashes cannot reject them.

No solver/search imports. Both exact checkers must first pass the original.
The optional positive-control mode rehearses this protocol without claiming
the requested zero bound.
"""
import argparse,concurrent.futures,hashlib,json,os,shutil,subprocess,sys,tempfile,time
from pathlib import Path

def main():
    p=argparse.ArgumentParser();p.add_argument('certificate',type=Path);p.add_argument('--checker',type=Path,required=True)
    p.add_argument('--positive-control',action='store_true');p.add_argument('--output',type=Path,required=True)
    p.add_argument('--tasks', help='selected case:checker pairs separated by commas; default runs the full protocol')
    a=p.parse_args();here=Path(__file__).resolve().parent;start=time.monotonic()
    extra=['--allow-control-bound'] if a.positive_control else []
    commands={'A':[sys.executable,str(here/'check_exact.py'),'CERT','--checker',str(a.checker.resolve())]+extra,
              'B':[sys.executable,str(here/'check_grouped.py'),'CERT']+extra}
    cases=['original','wrong-class-coefficient','non-PSD-block','negative-multiplier','CL-predicate','cover-gap']
    tasks=[(c,k) for c in cases for k in commands]
    if a.tasks:
        tasks=[tuple(item.split(':')) for item in a.tasks.split(',')]
        if not tasks or len(tasks)!=len(set(tasks)) or any(c not in cases or k not in commands for c,k in tasks):
            p.error('invalid or repeated selected case:checker pair')
    with tempfile.TemporaryDirectory() as tmp:
        roots={}
        for case in cases:
            dst=Path(tmp)/case;shutil.copytree(a.certificate,dst);roots[case]=dst
            c=json.loads((dst/'certificate.json').read_text());changed=None
            if case=='wrong-class-coefficient':
                changed='classes-00.json';rows=json.loads((dst/changed).read_text());rows[0][2]+=1
                (dst/changed).write_text(json.dumps(rows,separators=(',',':'))+'\n')
            elif case=='non-PSD-block':
                changed='block-00.json';b=json.loads((dst/changed).read_text());
                if c['schema']=='p33-b1-sos-v1':b['terms']=[{'weight':-1,'vector':[1]+[0]*(len(b['flags'])-1)}]
                else:b['matrix'][0][0]=-1
                (dst/changed).write_text(json.dumps(b,separators=(',',':'))+'\n')
            elif case=='negative-multiplier':c['inequality_multipliers'][0]=-1
            elif case=='CL-predicate':c['cl_predicates'][0][4]=2
            if changed:
                raw=(dst/changed).read_bytes();f=next(f for f in c['files'] if f['file']==changed)
                f.update(sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw))
            (dst/'certificate.json').write_text(json.dumps(c,separators=(',',':'))+'\n')
        def run(task):
            case,checker=task;cmd=[str(roots[case]) if x=='CERT' else x for x in commands[checker]]
            if case=='cover-gap':cmd+=['--plant-cover-gap']
            t=time.monotonic();r=subprocess.run(cmd,capture_output=True,text=True)
            ok=(r.returncode==0)==(case=='original')
            return {'case':case,'checker':checker,'pass':ok,'returncode':r.returncode,
                    'output':r.stdout.strip()[-1800:],'error':r.stderr.strip()[-400:],
                    'wall_seconds':time.monotonic()-t}
        # Two independently implemented checkers, each original and each corruption.
        with concurrent.futures.ThreadPoolExecutor(max_workers=min(4,int(os.environ.get('C5_CHECK_CPUS','1')))) as pool:
            records=list(pool.map(run,tasks))
    result={'status':'PASS_POSITIVE_CONTROL_CORRUPTIONS' if a.positive_control else 'PASS_EXACT_CERTIFICATE_CORRUPTIONS',
            'records':records,'wall_seconds':time.monotonic()-start}
    if a.tasks and not a.positive_control:result['status']='PASS_SELECTED_CERTIFICATE_CORRUPTIONS'
    if not all(r['pass'] for r in records):result['status']='FAIL_CORRUPTION_PROTOCOL'
    a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
    if result['status']=='FAIL_CORRUPTION_PROTOCOL':raise SystemExit(1)

if __name__=='__main__':main()
