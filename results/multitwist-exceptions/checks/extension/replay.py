#!/usr/bin/env python3
"""Check finite extension facts and require parsed mathematical rejections."""
import json
from pathlib import Path
import subprocess
import sys

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent


# Optimization would disable the explicit assertion-based validation below.
if not __debug__:
    raise SystemExit(2)


def run(label, script, args=(), accept=True, status=False):
    p=subprocess.run([sys.executable,'-I',str(script),*map(str,args)],
                     capture_output=True,text=True,timeout=300)
    if status:
        d=json.loads(p.stdout)
        verdict=d.get('status')
        wanted='PASS' if accept else 'REJECT'
    else:
        d=json.loads(p.stdout.strip().splitlines()[-1])
        verdict=d.get('verdict')
        wanted='ACCEPT' if accept else 'REJECT'
    assert p.returncode==(0 if accept else 1) and verdict==wanted, (label,p.returncode,d)
    if 'failure_count' in d:
        assert (d['failure_count']==0)==accept
    if 'failures' in d:
        assert (d['failures']==0)==accept
    print(json.dumps({'test':label,'exit':p.returncode,'verdict':verdict},sort_keys=True))
    return d


def main():
    a=HERE/'check_topology.py'
    b=HERE/'check_topology_independent.py'
    run('topology-grid',a,[HERE/'topology.json'])
    top=run('topology-facial',b,[HERE/'topology.json','--self-test'],status=True)
    assert len([c for c in top['controls'] if c['status']=='REJECT'])==7
    # Compare the regenerated certificate by parsed fields, not JSON formatting.
    import importlib.util
    spec=importlib.util.spec_from_file_location('facial_checker',b)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    result=module.check(json.loads((HERE/'topology.json').read_text()))
    result['input_sha256']=top['input_sha256']
    result['controls']=top['controls']
    normalized=json.loads(json.dumps(result,default=str))
    frozen=json.loads((HERE/'topology-independent-certificate.json').read_text())
    assert normalized==frozen,'facial certificate differs from supplied independent certificate'
    for f in ['puncture.json','crossing.json','face.json']:
        run('topology-grid-'+f,a,[HERE/'corruptions'/f],False)
        run('topology-facial-'+f,b,[HERE/'corruptions'/f],False,status=True)
    fa=HERE/'check_free_group.py'
    dy=HERE/'check_dynnikov.py'
    run('free-group',fa,['--kmax','12'])
    run('dynnikov',dy,['--kmax','8'])
    for f in sorted((ROOT.parent/'data/corrupt').glob('*.json')):
        run('free-group-'+f.stem,fa,['--kmax','2','--curves',f],False)
        run('dynnikov-'+f.stem,dy,['--input',f],False)
    for m in ['order','exponent']:
        run('free-group-'+m,fa,['--kmax','2','--mutation',m],False)
    for f in sorted((HERE/'corruptions/model').glob('*.json')):
        run('dynnikov-'+f.stem,dy,['--input',f],False)
    print('PASS finite extension certificate and exact-model controls')


if __name__=='__main__':
    main()
