#!/usr/bin/env python3
"""Six independent fresh enumerations, semantic audits and two chain checks."""
import argparse,concurrent.futures,gzip,json,os,resource,shutil,subprocess,sys,tempfile,time
from pathlib import Path
ROOT=Path(__file__).resolve().parent
DATA=ROOT.parent/"data"
GROUPS=['H4','G33','G34','E6','E7','E8']

def gap(script,out,tag):
    program=out/(tag+'.g');program.write_text(script)
    with (out/(tag+'.log')).open('w') as log:
        r=subprocess.run(['gap','-q','-b','-T',str(program)],stdout=log,stderr=subprocess.STDOUT)
    if r.returncode:raise RuntimeError(tag+' failed; see '+str(out/(tag+'.log')))

def unit(kind,out):
    start=time.monotonic();directory=out/kind;directory.mkdir()
    graph=directory/'interval.json';receipt=directory/'semantic.json'
    common=f'Read({json.dumps(str(ROOT/"models.g"))});;\nSCD_TYPE:={json.dumps(kind)};;\n'
    gap(common+f'SCD_OUT:={json.dumps(str(graph))};;\nRead({json.dumps(str(ROOT/"generate.g"))});;\n',directory,'generate')
    data=json.loads(graph.read_text())
    frozen=json.loads(gzip.decompress((DATA/(kind+'.interval.json.gz')).read_bytes()))
    payload={k:data[k] for k in ('group','rank','labels','ranks','edges')}
    if payload!=frozen:raise ValueError('regenerated interval differs from frozen payload: '+kind)
    # The second checker receives literal data only, never the generator.
    inputfile=directory/'data.g'
    inputfile.write_text('CERT_HEIGHT:='+str(data['rank'])+';;\nCERT_GROUP:='+json.dumps(data['group'])+';;\nCERT_LABELS:='+json.dumps(data['labels'])+';;\nCERT_RANKS:='+json.dumps(data['ranks'])+';;\nCERT_EDGES:='+json.dumps(data['edges'])+';;\n')
    gap(common+f'Read({json.dumps(str(inputfile))});;\nSCD_OUT:={json.dumps(str(receipt))};;\nRead({json.dumps(str(ROOT/"check_semantic.g"))});;\n',directory,'semantic')
    semantic=json.loads(receipt.read_text())
    if semantic.get('accepted') is not True:raise ValueError('semantic refusal')
    semantic_corruptions=[]
    if kind=='H4':
        # Actual edited inputs are fed through the full semantic checker.
        for corruption in ['missing_vertex','missing_edge']:
            bad=json.loads(json.dumps(data))
            if corruption=='missing_vertex':
                removed=next(i+1 for i,r in enumerate(bad['ranks']) if 0<r<bad['rank'])
                bad['labels'].pop(removed-1);bad['ranks'].pop(removed-1)
                bad['edges']=[[a-(a>removed),b-(b>removed)] for a,b in bad['edges'] if a!=removed and b!=removed]
                expected='descending closure gap'
            else:
                bad['edges'].pop();expected='exact complete cover graph'
            badinput=directory/(corruption+'.g')
            badinput.write_text('CERT_HEIGHT:='+str(bad['rank'])+';;\nCERT_GROUP:='+json.dumps(bad['group'])+';;\nCERT_LABELS:='+json.dumps(bad['labels'])+';;\nCERT_RANKS:='+json.dumps(bad['ranks'])+';;\nCERT_EDGES:='+json.dumps(bad['edges'])+';;\n')
            driver=directory/(corruption+'-driver.g')
            driver.write_text(common+f'Read({json.dumps(str(badinput))});;\nSCD_OUT:={json.dumps(str(directory/(corruption+".receipt.json")))};;\nRead({json.dumps(str(ROOT/"check_semantic.g"))});;\n')
            proc=subprocess.run(['gap','-q','-b','-T',str(driver)],capture_output=True,text=True)
            (directory/(corruption+'.log')).write_text(proc.stdout+proc.stderr)
            if proc.returncode!=1 or 'REJECT '+expected not in proc.stdout:raise ValueError('semantic corruption failed: '+corruption)
            semantic_corruptions.append(corruption)
    cert=DATA/(kind+'.chains.json.gz');original=json.loads(gzip.decompress(cert.read_bytes()))
    commands=[[sys.executable,str(ROOT/'check_chains.py')],['node',str(ROOT/'check_chains.js')]]
    checks=[]
    for command in commands:
        p=subprocess.run(command+[str(graph),str(cert)],capture_output=True,text=True)
        if p.returncode:raise ValueError(p.stdout+p.stderr)
        checks.append(json.loads(p.stdout))
    variants={}
    missing=json.loads(json.dumps(original));missing['chains'].pop();variants['missing_chain']=missing
    duplicate=json.loads(json.dumps(original));duplicate['chains'].append(duplicate['chains'][0]);variants['duplicate_chain']=duplicate
    wrong=json.loads(json.dumps(original));long=next(c for c in wrong['chains'] if len(c)>2);long[0],long[1]=long[1],long[0];variants['noncover_order']=wrong
    asym=json.loads(json.dumps(original));long=next(c for c in asym['chains'] if len(c)>2);long.pop();variants['asymmetric_end']=asym
    rejected=[]
    for name,bad in variants.items():
        path=directory/(name+'.json');path.write_text(json.dumps(bad))
        for command in commands:
            p=subprocess.run(command+[str(graph),str(path)],capture_output=True,text=True)
            if p.returncode!=1 or not p.stdout.startswith('REJECT'):raise ValueError('corruption was not rejected: '+name)
        rejected.append(name)
    return {'group':kind,'accepted':True,'regenerated_matches_frozen':True,'semantic':semantic,'semantic_corruptions_rejected':semantic_corruptions,'chain_checks':checks,'both_rejected':rejected,'generation_cpu_ms':data['generation_cpu_ms'],'wall_seconds':round(time.monotonic()-start,3)}


def audit_receipt(groups):
    """Check the complete parsed acceptance record, including all controls."""
    required = set(GROUPS)
    if len(groups) != 6 or {g.get('group') for g in groups} != required:
        raise RuntimeError('missing or repeated exceptional group receipt')
    for group in groups:
        semantic = group['semantic']
        checks = group['chain_checks']
        if (group.get('accepted') is not True or
                group.get('regenerated_matches_frozen') is not True or
                semantic.get('accepted') is not True or
                semantic.get('group') != group['group']):
            raise RuntimeError('incomplete group regeneration or semantic check')
        if len(checks) != 2 or {c.get('checker') for c in checks} != {'python', 'javascript'}:
            raise RuntimeError('missing independent chain checker')
        if any(c.get('accepted') is not True or c['vertices'] != semantic['vertices']
               for c in checks):
            raise RuntimeError('inconsistent or rejected chain checker receipt')
        if (checks[0]['rank_sizes'] != checks[1]['rank_sizes'] or
                checks[0]['chains'] != checks[1]['chains']):
            raise RuntimeError('independent chain checker results disagree')
        if set(group['both_rejected']) != {'missing_chain', 'duplicate_chain',
                                           'noncover_order', 'asymmetric_end'}:
            raise RuntimeError('missing chain corruption control')
        if group['group'] == 'H4' and set(group['semantic_corruptions_rejected']) != {
                'missing_vertex', 'missing_edge'}:
            raise RuntimeError('missing semantic planted-gap controls')


def verify(out, workers):
    start=time.monotonic();before=resource.getrusage(resource.RUSAGE_CHILDREN)
    result={'accepted':False,'groups':[]}
    try:
        with concurrent.futures.ThreadPoolExecutor(max_workers=min(6,workers)) as pool:
            futures={pool.submit(unit,g,out):g for g in GROUPS}
            for f in concurrent.futures.as_completed(futures):
                result['groups'].append(f.result());print('PASS '+futures[f],flush=True)
        result['groups'].sort(key=lambda x:GROUPS.index(x['group']))
        audit_receipt(result['groups'])
        result['accepted']=True
    finally:
        after=resource.getrusage(resource.RUSAGE_CHILDREN)
        result['wall_seconds']=round(time.monotonic()-start,3)
        result['cpu_seconds']=round(after.ru_utime+after.ru_stime-before.ru_utime-before.ru_stime,3)
        (out/'report.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'accepted':result['accepted'],'wall_seconds':result['wall_seconds']}))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--workers',type=int,default=2,
                        help='concurrent group checks (default: 2, maximum: 6)')
    parser.add_argument('--work',type=Path,help='retain logs in this new directory')
    args=parser.parse_args()
    if args.workers<1:
        parser.error('--workers must be positive')
    for tool in ('gap','node'):
        if shutil.which(tool) is None:
            raise SystemExit('Missing '+tool+'; see checks/README.md.')
    # SmallGrp is a GAP package dependency, including for core conjugacy calls.
    probe=subprocess.run(['gap','-q','-b','-T','-c',
        'if LoadPackage("smallgrp") = fail then QUIT_GAP(1); fi; '
        'if IdGroup(Group((1,2),(1,2,3))) <> [6,1] then QUIT_GAP(1); fi; '
        'QUIT_GAP(0);'],capture_output=True,text=True)
    if probe.returncode:
        raise SystemExit('GAP SmallGrp identification is required; install gap-smallgrp. See checks/README.md.')
    if args.work is None:
        with tempfile.TemporaryDirectory(prefix='noncrossing-chains-') as work:
            verify(Path(work),args.workers)
    else:
        out=args.work.resolve();out.mkdir(parents=True,exist_ok=False)
        verify(out,args.workers)


if __name__=='__main__':main()
