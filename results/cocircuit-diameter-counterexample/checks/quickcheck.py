#!/usr/bin/env python3
"""Exact geometry and bounded Lean control. No source-size Lean build."""
import argparse, gzip, hashlib, importlib, json, os
from pathlib import Path
import resource, signal, subprocess, sys, time
import psutil
ROOT = Path(__file__).resolve().parents[1]
CHECKS = ROOT / 'checks'
# Isolated Python omits the script directory. Trust this bundle's sibling
# modules explicitly, without importing from the working directory or PYTHONPATH.
sys.path.insert(0, str(CHECKS))
from corruptions import KINDS, mutate
from bootstrap_kernel import bootstrap

def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def save(p, x):
    q = p.with_suffix('.tmp')
    with q.open('w') as f:
        json.dump(x, f, indent=2); f.write('\n'); f.flush(); os.fsync(f.fileno())
    q.replace(p)
    fd=os.open(p.parent,os.O_RDONLY | os.O_DIRECTORY)
    try:os.fsync(fd)
    finally:os.close(fd)
def cpu():
    return sum(resource.getrusage(k).ru_utime + resource.getrusage(k).ru_stime
               for k in [resource.RUSAGE_SELF, resource.RUSAGE_CHILDREN])
def reject(checker, cert, inp, workers):
    # Import failure is outside the semantic exception handler.
    mod = importlib.import_module(checker)
    c = json.loads(Path(cert).read_text())
    try: mod.verify(c, inp, int(workers))
    except (AssertionError, ValueError, IndexError) as error:
        print(json.dumps({'rejected': True, 'exception': type(error).__name__})); return
    raise RuntimeError('semantic corruption accepted')
def process_tree_usage(pid):
    processes = [psutil.Process(pid)]
    try:
        processes += processes[0].children(recursive=True)
    except psutil.NoSuchProcess:
        pass
    rss = used = 0
    for proc in processes:
        try:
            rss += proc.memory_info().rss
            ct = proc.cpu_times()
            # Reaped descendants disappear from children(); their CPU remains
            # in the live parent's waited-child counters until that parent exits.
            used += ct.user + ct.system + ct.children_user + ct.children_system
        except psutil.NoSuchProcess:
            pass
    return rss, used

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--cpus', type=int, required=True)
    ap.add_argument('--work', type=Path, required=True)
    ap.add_argument('--checkpoint', type=Path, required=True)
    ap.add_argument('--cpu-hours', type=float, default=1)
    ap.add_argument('--checkpoint-seconds', type=float, default=600)
    ap.add_argument('--geometry-only', action='store_true')
    ap.add_argument('--resume', action='store_true')
    a = ap.parse_args()
    assert 1 <= a.cpus <= len(os.sched_getaffinity(0))
    assert 0 < a.cpu_hours <= 1 and 0 < a.checkpoint_seconds <= 600
    work=a.work.resolve(); checkpoint=a.checkpoint.resolve()
    assert ROOT not in work.parents and ROOT not in checkpoint.parents
    work.mkdir(parents=True,exist_ok=True);checkpoint.parent.mkdir(parents=True,exist_ok=True)
    state=json.loads(checkpoint.read_text()) if a.resume and checkpoint.exists() else {'steps':{},'complete':False}
    # Materialize/verify before hashing: first run and resume see the same files.
    bootstrap(scope='control')
    inputs = sorted(CHECKS.glob('*.py')) + [CHECKS/'generated-kernel-sha256.json', CHECKS/'proof-sources.json', CHECKS/'README.md', ROOT/'paper/paper.tex'] + sorted((ROOT/'data').iterdir()) + sorted((ROOT/'lean').glob('*.lean')) + [ROOT/'lean/lean-toolchain', ROOT/'lean/lake-manifest.json']
    signature=hashlib.sha256(b''.join(str(p.relative_to(ROOT)).encode()+b'\0'+p.read_bytes() for p in inputs)).hexdigest()
    assert state.get('checking_sources_sha256',signature)==signature
    state['checking_sources_sha256']=signature
    state['complete']=False
    env=dict(os.environ, PROOF_CPUS=str(a.cpus), LEAN_NUM_THREADS=str(a.cpus), PYTHONDONTWRITEBYTECODE='1')
    start=time.monotonic(); c0=cpu(); peak=0; last=start
    def checkpoint_now():
        state.update(elapsed_wall_seconds=time.monotonic()-start, inclusive_cpu_seconds=cpu()-c0,
                     peak_sampled_process_tree_rss_bytes=peak)
        # Lake's incremental products remain in its build directory, never in checkpoints.
        state['completed_lean_modules']={p.name:sha(p) for p in (ROOT/'lean/.lake/build/lib/lean').glob('*.olean')}
        save(checkpoint,state)
    def run(name, cmd, cwd=ROOT, expected=0):
        nonlocal peak,last
        log=work/(name+'.log')
        old=state['steps'].get(name)
        if a.resume and old and old['exit']==expected and log.exists() and old['log_sha256']==sha(log):
            # Lake itself must validate incremental dependencies on every resume.
            if name!='lean-control': return log
        t=time.monotonic(); c=cpu()
        with log.open('w') as f:
            p=subprocess.Popen(list(map(str,cmd)),cwd=cwd,env=env,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
            try:
                while p.poll() is None:
                    rss, live = process_tree_usage(p.pid)
                    peak=max(peak,rss)
                    if cpu()-c0+live>=a.cpu_hours*3600: raise RuntimeError('one CPU-hour guard reached')
                    if time.monotonic()-last>=a.checkpoint_seconds:
                        checkpoint_now();last=time.monotonic()
                    time.sleep(.25)
            except BaseException:
                os.killpg(p.pid,signal.SIGTERM)
                try:p.wait(timeout=5)
                except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL);p.wait()
                raise
        result={'exit':p.returncode,'wall_seconds':time.monotonic()-t,'cpu_seconds':cpu()-c,'log_sha256':sha(log)}
        state['steps'][name]=result;checkpoint_now()
        assert p.returncode==expected, f'{name}: exit {p.returncode}; see {log}'
        return log
    try:
        run('proof-sources',[sys.executable,CHECKS/'check_proof_sources.py',
            '--guide',CHECKS/'README.md'])
        run('written-certificate',[sys.executable,CHECKS/'check_written_certificate.py',
            '--data',ROOT/'data','--check-paper',ROOT/'paper/paper.tex',
            '--output',work/'written-certificate.json'])
        for scope in ['control','source']:
            if scope=='source':
                packed=b''.join(p.read_bytes() for p in sorted((ROOT/'data').glob('source-certificate.json.gz.part*')))
                inp=ROOT/'data/msw-input.json'; count,edges,gap=36425,364250,21
            else:
                packed=(ROOT/'data/control-certificate.json.gz').read_bytes()
                inp=ROOT/'data/lp-control-bounded-rank4-input.json'; count,edges,gap=8,12,3
            cert=work/(scope+'.json'); cert.write_bytes(gzip.decompress(packed)); obj=json.loads(cert.read_text())
            for checker in ['check_fraction','check_rational']:
                log=run(scope+'-'+checker,[sys.executable,CHECKS/(checker+'.py'),cert,inp])
                parsed=json.loads(log.read_text())
                assert parsed['accepted_relative_graph'] and (parsed['vertices'],parsed['edges'],parsed['endpoint_distance'])==(count,edges,gap)
                if scope=='control': assert parsed['control_cover_exhaustive']
                for kind in KINDS:
                    bad=work/(scope+'-'+kind+'.json');save(bad,mutate(obj,kind))
                    log=run(scope+'-'+checker+'-'+kind,[sys.executable,__file__,'--reject',checker,bad,inp,a.cpus])
                    assert json.loads(log.read_text())['rejected']
        run('source-transcription',[sys.executable,CHECKS/'bind_source.py','--check'])
        if not a.geometry_only:
            run('lean-control',['lake','build','ControlCheck'],ROOT/'lean')
            run('lean-bridges',['lake','build','BridgeCheck'],ROOT/'lean')
            log=run('false-control',['lake','env','lean',CHECKS/'FalseControl.lean'],ROOT/'lean',expected=1)
            assert 'kernel' in log.read_text().lower(), 'false proposition must fail in kernel reduction'
        state.update(complete=True,source_geometry=True,control_geometry=True,semantic_rejections=28,
                     bounded_lean_control=not a.geometry_only,full_endpoint_rebuilt=False)
    finally:
        checkpoint_now()
        print(json.dumps({k:v for k,v in state.items() if k not in ['steps','completed_lean_modules']}))
if __name__=='__main__':
    if len(sys.argv)>1 and sys.argv[1]=='--reject':reject(*sys.argv[2:])
    else:main()
