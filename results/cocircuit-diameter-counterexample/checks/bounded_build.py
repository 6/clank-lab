#!/usr/bin/env python3
"""Run a normal Lake build with bounded resources and atomic progress checkpoints."""
import argparse, hashlib, json, math, os
from pathlib import Path
import signal, subprocess, time
import psutil
PROJECT=Path(__file__).resolve().parents[1]/'lean'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,x):
    q=p.with_suffix('.tmp')
    with q.open('w') as f:
        json.dump(x,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
    q.replace(p)
    fd=os.open(p.parent,os.O_RDONLY | os.O_DIRECTORY)
    try:os.fsync(fd)
    finally:os.close(fd)
def cpu():
    # The allocation's monotonic counter includes live AND reaped descendants.
    # Other work in the same cgroup is charged conservatively to this allowance.
    return int(dict(line.split() for line in
        Path('/sys/fs/cgroup/cpu.stat').read_text().splitlines())['usage_usec'])/1e6
def cpu_scope():
    st=Path('/sys/fs/cgroup').stat()
    return [st.st_dev,st.st_ino,Path('/proc/sys/kernel/random/boot_id').read_text().strip()]
def cpu_accounting(old):
    scope=cpu_scope(); now=cpu()
    if old:
        account=old.get('cpu_accounting',{})
        assert account.get('backend')=='cgroup-v2', 'legacy CPU checkpoint requires independently verified accounting'
        assert account['scope']==scope, 'CPU cgroup changed; independently verify prior consumption before resuming'
        assert account['origin_seconds']<=now, 'CPU counter regressed'
        return account
    return {'backend':'cgroup-v2','scope':scope,'origin_seconds':now}
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--cpus',type=int,required=True)
    ap.add_argument('--workers',type=int,required=True)
    ap.add_argument('--cpu-hours',type=float,required=True)
    ap.add_argument('--work',type=Path,required=True)
    ap.add_argument('--checkpoint',type=Path,required=True)
    ap.add_argument('--checkpoint-seconds',type=float,default=600)
    ap.add_argument('--resume',action='store_true')
    ap.add_argument('--target',default='Proof')
    a=ap.parse_args()
    assert 1<=a.workers<=a.cpus<=len(os.sched_getaffinity(0)) and a.cpus%a.workers==0
    assert 0<a.checkpoint_seconds<=600 and math.isfinite(a.cpu_hours) and a.cpu_hours>0
    assert a.cpus//a.workers==2, 'Lake configuration uses two Lean threads per process'
    limit=Path('/sys/fs/cgroup/memory.max')
    memory=min(psutil.virtual_memory().total,int(limit.read_text()) if limit.exists() and limit.read_text().strip()!='max' else psutil.virtual_memory().total)
    if a.target=='Proof':assert a.cpus>=12 and memory>=(a.workers*12+16)*1024**3
    work=a.work.resolve(); cp=a.checkpoint.resolve()
    assert PROJECT.parent not in work.parents and PROJECT.parent not in cp.parents
    work.mkdir(parents=True,exist_ok=True);cp.parent.mkdir(parents=True,exist_ok=True)
    # Authenticate/materialize before source signatures, resume checks and Lake imports.
    from bootstrap_kernel import bootstrap
    bootstrap(scope='all')
    sources={p.name:sha(p) for p in PROJECT.iterdir() if p.suffix=='.lean' or p.name in ['lean-toolchain','lake-manifest.json']}
    old=json.loads(cp.read_text()) if a.resume and cp.exists() else {}
    assert old.get('sources',sources)==sources, 'resume requires the same source bytes'
    account=cpu_accounting(old)
    state={'sources':sources,'complete':False,'command':['lake','build',a.target],
           'prior_checkpoint_sha256':sha(cp) if old else None,'lost_or_modified_prior_objects':[],
           'cpu_accounting':account,'cpu_limit_seconds':a.cpu_hours*3600}
    objects=PROJECT/'.lake/build/lib/lean'
    for n,h in old.get('completed_modules',{}).items():
        if not (objects/n).exists() or sha(objects/n)!=h:state['lost_or_modified_prior_objects'].append(n)
    # Lake rechecks dependencies, and rebuilds absent/changed products. No checkpoint is a proof input.
    env=dict(os.environ,LEAN_NUM_THREADS=str(a.workers))
    log=work/'lake-build.log';t=time.monotonic();c0=cpu();peak=old.get('peak_sampled_process_tree_rss_bytes',0);last=t
    # Preserve the original counter on resume, including work since the last
    # checkpoint and downtime. Reserve polling and five-second shutdown CPU.
    reserve=6*max(a.cpus,len(os.sched_getaffinity(0)))+1
    state['cpu_shutdown_reserve_seconds']=reserve
    def spent():return cpu()-account['origin_seconds']
    def checkpoint():
        current=cpu()
        state.update(wall_seconds=time.monotonic()-t,cpu_seconds=current-c0,
                     cumulative_cpu_seconds=current-account['origin_seconds'],peak_sampled_process_tree_rss_bytes=peak,
                     completed_modules={p.name:sha(p) for p in objects.glob('*.olean')},
                     build_log_sha256=sha(log))
        save(cp,state)
        # Only logs/checkpoints enter the durable directory; no compiler products.
        temp=cp.parent/'lake-build.log.tmp';temp.write_bytes(log.read_bytes());temp.replace(cp.parent/'lake-build.log')
    with log.open('w') as f:
        checkpoint()  # Seal the CPU origin before any build work can start.
        if spent()>=a.cpu_hours*3600-reserve:
            state['error']='explicit cumulative CPU allowance exhausted before launch'
            checkpoint()
            raise RuntimeError(state['error'])
        proc=subprocess.Popen(state['command'],cwd=PROJECT,env=env,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
        try:
            while proc.poll() is None:
                try:tree=[psutil.Process(proc.pid)]+psutil.Process(proc.pid).children(recursive=True)
                except psutil.NoSuchProcess:tree=[]
                rss=0;leans=[]
                for p in tree:
                    try:
                        rss+=p.memory_info().rss
                        if p.name()=='lean':leans.append(p)
                    except psutil.NoSuchProcess:pass
                peak=max(peak,rss)
                if len(leans)>a.workers:raise RuntimeError('Lake concurrency exceeds worker limit')
                for p in leans:
                    try:
                        if time.time()-p.create_time()>590:raise RuntimeError('Lean module reached ten-minute restart limit; subdivision required')
                        assembly=any('Proof.lean' in x or 'Complete' in x for x in p.cmdline())
                        if p.memory_info().rss>(20 if assembly else 12)*1024**3:raise RuntimeError('Lean module memory guard')
                    except psutil.NoSuchProcess:pass
                if spent()>=a.cpu_hours*3600-reserve:raise RuntimeError('explicit cumulative CPU allowance exhausted')
                if rss>memory-4*1024**3:raise RuntimeError('aggregate memory guard')
                if time.monotonic()-last>=a.checkpoint_seconds:checkpoint();last=time.monotonic()
                time.sleep(.25)
            state['exit']=proc.returncode
            assert proc.returncode==0,'Lake build failed; inspect retained log'
            state['complete']=True
        except BaseException as e:
            state['error']=str(e)
            try:os.killpg(proc.pid,signal.SIGTERM)
            except ProcessLookupError:pass
            try:proc.wait(timeout=5)
            except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGKILL);proc.wait()
            raise
        finally:checkpoint()
    print(json.dumps({k:v for k,v in state.items() if k not in ['sources','completed_modules']}))
if __name__=='__main__':main()
