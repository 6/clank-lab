#!/usr/bin/env python3
"""Check one generated finite certificate, with explicit durable receipts.

This is a proof phase, never a full endpoint verification. Builds stay outside keep;
generated inputs/logs are packed at completion, including on a check failure.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
import hashlib
import json
import os
from pathlib import Path
import resource
import re
import subprocess
import tarfile
import time
import psutil


def save(p,x):
    q=p.with_suffix(p.suffix+'.tmp');q.write_text(json.dumps(x,indent=2)+'\n');q.replace(p)


def cpu():
    return sum(resource.getrusage(k).ru_utime+resource.getrusage(k).ru_stime
               for k in [resource.RUSAGE_SELF,resource.RUSAGE_CHILDREN])


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--generated',required=True)
    ap.add_argument('--mathlib',required=True)
    ap.add_argument('--build',required=True)
    ap.add_argument('--keep',required=True)
    ap.add_argument('--resume',action='store_true')
    ap.add_argument('--prior-receipt')
    ap.add_argument('--representative-only',action='store_true')
    ap.add_argument('--split-representative',action='store_true')
    ap.add_argument('--kernel-reduction',action='store_true')
    ap.add_argument('--async-kernel',action='store_true')
    ap.add_argument('--proof-parallel',type=int)
    ap.add_argument('--module-wall-seconds',type=int,default=600)
    ap.add_argument('--module-rss-gib',type=float,default=8)
    ap.add_argument('--assembly-rss-gib',type=float)
    a=ap.parse_args()
    assert 0<a.module_wall_seconds<=600 and a.module_rss_gib>0
    assert not a.split_representative or a.representative_only
    assert not a.async_kernel or a.kernel_reduction
    root,build,keep,mathlib=map(lambda x:Path(x).resolve(),[a.generated,a.build,a.keep,a.mathlib])
    assert 'keep' not in build.parts and 'keep' not in root.parts
    build.mkdir(parents=True,exist_ok=True);keep.mkdir(parents=True,exist_ok=True)
    workers=int(os.environ['PROOF_CPUS']);assert workers>0
    m=json.loads((root/'manifest.json').read_text())
    for name,h in m['files'].items():assert hashlib.sha256((root/name).read_bytes()).hexdigest()==h
    env=dict(os.environ)
    env['LEAN_PATH']=str(build)+':'+env.get('ADKZ_PROOF_BUILD',str(Path(env['PROOF_SCRATCH'])/'proof-build'))+':'+subprocess.check_output(
        ['lake','env','printenv','LEAN_PATH'],cwd=mathlib,text=True).strip()
    prior={}
    prior_path=Path(a.prior_receipt) if a.prior_receipt else keep/'kernel-receipt.json'
    if a.resume and prior_path.exists():
        prior={c['module']:c for c in json.loads(prior_path.read_text())['checks']}
    parallel=a.proof_parallel or workers
    assert 1<=parallel<=workers and workers%parallel==0
    representative_modules=[]
    if a.split_representative:
        # Preserve each original theorem verbatim; only module boundaries change.
        original=(root/'SourceKernelChunk9.lean').read_text()
        header,body=original.split('theorem source_vertex_576',1)
        body='theorem source_vertex_576'+body
        vertices,aggregation=body.split('theorem source_chunk_9',1)
        parts=re.split(r'(?=theorem source_vertex_\d+ : )',vertices)
        parts=[part for part in parts if part]
        assert len(parts)==64
        for v,part in zip(range(576,640),parts):
            assert part.startswith(f'theorem source_vertex_{v} : ')
            name=f'SourceKernelRepresentativeVertex{v}'
            raw=header+part+'end ADKZPricing.Generated\n'
            (root/(name+'.lean')).write_text(raw)
            m['files'][name+'.lean']=hashlib.sha256(raw.encode()).hexdigest()
            representative_modules.append(name)
        raw=''.join(f'import {name}\n' for name in representative_modules)+header
        raw+='theorem source_chunk_9'+aggregation
        (root/'SourceKernelRepresentativeAggregate.lean').write_text(raw)
        m['files']['SourceKernelRepresentativeAggregate.lean']=hashlib.sha256(raw.encode()).hexdigest()
    if a.representative_only:
        assert m['kind']=='msw' and m['vertices']==36425
        # A plumbing test with an explicit remaining-premise: NOT the endpoint proof.
        smoke="""import SourceKernelChunk9
namespace ADKZPricing.Generated
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem source_imported_gap : (21 : ℤ) ≤ sourceTree.potential mswPlusLabels -
    sourceTree.potential mswMinusLabels := by decide
theorem source_imported_endpoint_test
    (remaining : ∀ i : Fin 36425, ¬ (576 ≤ i.val ∧ i.val < 640) →
      integerSourceVertexCheck sourceA sourceData i ∧
      sourcePotentialVertexCheck sourceData sourceTree sourceLevels i) : ProposedEndpoint := by
  have checks (i : Fin 36425) : integerSourceVertexCheck sourceA sourceData i ∧
      sourcePotentialVertexCheck sourceData sourceTree sourceLevels i := by
    by_cases h : 576 ≤ i.val ∧ i.val < 640
    · exact source_chunk_9 i h.1 h.2
    · exact remaining i h
  let valid := integerSourceValid_of_checks sourceA sourceData (fun i => (checks i).1)
  exact msw_endpoint_of_source_certificate valid.toCertificate sourceTree.potential
    (sourcePotential_local sourceA sourceData valid sourceTree sourceLevels (fun i => (checks i).2))
    source_imported_gap
#print axioms source_imported_endpoint_test
end ADKZPricing.Generated
"""
        if a.split_representative:
            smoke=smoke.replace('import SourceKernelChunk9','import SourceKernelRepresentativeAggregate')
        (root/'SourceKernelImportedTest.lean').write_text(smoke)
        m['files']['SourceKernelImportedTest.lean']=hashlib.sha256(smoke.encode()).hexdigest()
    module_map={}
    if a.kernel_reduction:
        assert not a.split_representative
        names=(['SourceKernelChunk9','SourceKernelImportedTest'] if a.representative_only else
               [f'SourceKernelChunk{i}' for i in range(m['chunks'])]+['SourceKernelComplete'])
        module_map={name:name+('KernelAsync' if a.async_kernel else 'Kernel') for name in names}
        for name in names:
            raw=(root/(name+'.lean')).read_text()
            decision='decide +kernel'
            if a.async_kernel:
                decision=('run_tac Lean.Elab.Tactic.liftMetaTactic fun g => g.withContext do\n'
                          '    let pf ← Lean.Meta.mkDecideProof (← g.getType)\n'
                          '    g.assign pf\n    pure []')
                raw=raw.replace('by decide','by\n  '+decision).replace('\n  decide\n','\n  '+decision+'\n')
            else:raw=raw.replace('by decide','by decide +kernel').replace('\n  decide\n','\n  decide +kernel\n')
            for before,after in module_map.items():raw=raw.replace('import '+before+'\n','import '+after+'\n')
            new=module_map[name]+'.lean'
            (root/new).write_text(raw)
            m['files'][new]=hashlib.sha256(raw.encode()).hexdigest()
    if a.async_kernel and m['kind']=='control':
        bad=('import '+module_map['SourceKernelComplete']+'\n'
             'theorem deliberatelyFalse : (1 : Nat) = 2 := by\n  '+decision+'\n')
        (root/'SourceKernelDispatchCorruption.lean').write_text(bad)
        m['files']['SourceKernelDispatchCorruption.lean']=hashlib.sha256(bad.encode()).hexdigest()
    inputs=keep/'generated-inputs.tar.gz'
    temporary=inputs.with_suffix('.tmp')
    with tarfile.open(temporary,'w:gz') as archive:
        for name in [*m['files'],'manifest.json']:archive.add(root/name,arcname=name)
    with tarfile.open(temporary,'r:gz') as archive:
        for name,h in m['files'].items():
            assert hashlib.sha256(archive.extractfile(name).read()).hexdigest()==h
    temporary.replace(inputs)
    start,c0=time.monotonic(),cpu()
    report={'kind':m['kind'],'vertices':m['vertices'],'chunks':m['chunks'],
            'files':m['files'],'checks':[],'kernel_checked':False,'full_target_unit_complete':False,
            'representative_only':a.representative_only,'split_representative':a.split_representative,
            'allocated_cpus':workers,'kernel_reduction':a.kernel_reduction,'async_kernel':a.async_kernel,
            'proof_parallel':parallel,'module_wall_guard_seconds':a.module_wall_seconds,
            'module_rss_guard_gib':a.module_rss_gib,
            'prior_receipt_sha256':hashlib.sha256(prior_path.read_bytes()).hexdigest() if prior else None}
    def check(module,threads):
        module=module_map.get(module,module)
        t=time.monotonic()
        rss_limit=(a.assembly_rss_gib if a.assembly_rss_gib and
                   ('ImportedTest' in module or 'Complete' in module) else a.module_rss_gib)
        obj=build/(module+'.olean')
        old=prior.get(module,{})
        if (old.get('exit')==0 and old.get('source_sha256')==m['files'][module+'.lean']
                and obj.exists() and old.get('olean_sha256')==hashlib.sha256(obj.read_bytes()).hexdigest()):
            return {**old,'wall_seconds':0,'reused_verified_receipt':True}
        with (root/(module+'.log')).open('w') as log:
            proc=subprocess.Popen(['lean','--root='+str(root),'-j',str(threads),'-DwarningAsError=true',
                              '-o',str(build/(module+'.olean')),str(root/(module+'.lean'))],
                             cwd=mathlib,env=env,stdout=log,stderr=subprocess.STDOUT)
            peak=0;guard=None
            while True:
                try:code=proc.wait(timeout=5);break
                except subprocess.TimeoutExpired:
                    try:peak=max(peak,psutil.Process(proc.pid).memory_info().rss)
                    except psutil.NoSuchProcess:pass
                    if peak>rss_limit*1024**3:guard='per-module RSS guard'
                    if time.monotonic()-t>a.module_wall_seconds:guard='per-module wall guard'
                    if guard:
                        proc.terminate()
                        try:code=proc.wait(timeout=10)
                        except subprocess.TimeoutExpired:proc.kill();code=proc.wait()
                        break
        return {'module':module,'exit':code,'wall_seconds':time.monotonic()-t,
                'peak_sampled_rss_bytes':peak,'guard':guard,'lean_threads':threads,'rss_guard_gib':rss_limit,
                'source_sha256':m['files'][module+'.lean'],
                'olean_sha256':hashlib.sha256(obj.read_bytes()).hexdigest() if code==0 else None}
    def record(result):
        report['checks'].append(result)
        report['wall_seconds']=time.monotonic()-start
        report['cpu_seconds_parent_and_children']=cpu()-c0
        save(keep/'kernel-receipt.json',report)
        return result['exit']==0
    def group(modules,concurrency):
        # Submit only a bounded window; the first failure stops new work.
        pending={};remaining=iter(modules);ok=True
        with ThreadPoolExecutor(max_workers=concurrency) as pool:
            for _ in range(concurrency):
                name=next(remaining,None)
                if name is not None:pending[pool.submit(check,name,workers//concurrency)]=name
            while pending:
                done,_=wait(pending,return_when=FIRST_COMPLETED)
                for f in done:
                    pending.pop(f)
                    ok=record(f.result()) and ok
                if ok:
                    for _ in done:
                        name=next(remaining,None)
                        if name is not None:pending[pool.submit(check,name,workers//concurrency)]=name
        return ok
    success=group([f'SourceKernelDataBlock{i}' for i in range(m.get('data_blocks',0))],workers)
    if success:success=record(check('SourceKernelData',workers))
    # The first exact production chunk calibrates memory before concurrency.
    # This is a chunk of the same finite certificate, not another target unit.
    if success and a.split_representative:
        success=group(representative_modules,workers)
        if success:success=record(check('SourceKernelRepresentativeAggregate',workers))
    elif success:
        success=record(check('SourceKernelChunk9' if a.representative_only else 'SourceKernelChunk0',workers))
    if success and a.representative_only:
        success=record(check('SourceKernelImportedTest',workers))
    elif success:
        success=group([f'SourceKernelChunk{i}' for i in range(1,m['chunks'])],parallel)
        if success:success=record(check('SourceKernelComplete',workers))
    if success:
        final_module='SourceKernelImportedTest' if a.representative_only else 'SourceKernelComplete'
        log=(root/(module_map.get(final_module,final_module)+'.log')).read_text()
        assert 'sorryAx' not in log and 'Lean.ofReduceBool' not in log and 'native_decide' not in log
        axiom_lists=re.findall(r'depends on axioms: \[(.*?)\]',log,re.S)
        assert axiom_lists,'missing trusted-axiom report'
        reported={name.strip() for names in axiom_lists for name in names.split(',') if name.strip()}
        assert reported<={'propext','Classical.choice','Quot.sound'},reported
        report['checked_axioms']=sorted(reported)
        if m['kind']=='msw' and not a.representative_only:
            assert 'source_frozen_endpoint' in log
            report['unconditional_source_endpoint_checked']=True
    if success and a.async_kernel and m['kind']=='control':
        bad=check('SourceKernelDispatchCorruption',workers)
        bad['expected_exit']=1;record(bad)
        log=(root/'SourceKernelDispatchCorruption.log').read_text()
        success=bad['exit']==1 and 'kernel' in log.lower()
        report['false_proposition_rejected_by_kernel']=success
    report['kernel_checked']=success and not a.representative_only
    report['representative_and_import_test_passed']=success if a.representative_only else None
    report['wall_seconds']=time.monotonic()-start;report['cpu_seconds_parent_and_children']=cpu()-c0
    save(keep/'kernel-receipt.json',report)
    archive=keep/'generated-inputs-and-logs.tar.gz'
    temporary=archive.with_suffix('.tmp')
    with tarfile.open(temporary,'w:gz') as t:
        for p in sorted(root.iterdir()):
            if p.suffix in ['.lean','.log','.json']:t.add(p,arcname=p.name)
    with tarfile.open(temporary,'r:gz') as t:
        names=t.getnames()
        for name,h in m['files'].items():assert hashlib.sha256(t.extractfile(name).read()).hexdigest()==h
    temporary.replace(archive)
    save(keep/'kernel-archive.json',{'sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),
                                  'bytes':archive.stat().st_size,'entries':len(names)})
    print(json.dumps({k:v for k,v in report.items() if k not in ['files','checks']}))
    raise SystemExit(0 if success else 1)


if __name__=='__main__':main()
