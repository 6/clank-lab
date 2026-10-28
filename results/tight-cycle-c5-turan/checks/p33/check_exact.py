#!/usr/bin/env python3
"""Standalone certificate loader, exact PSD/sign checks, and semantic driver.

Only a separate arithmetic checker module is imported. No solver,
generator, search, or recovered multiplication matrix is imported.
"""
import argparse
import hashlib,json,subprocess,tempfile,time
from pathlib import Path
from check_control_psd import psd, integer


def require(test,message):
    if not test:raise ValueError(message)


def main():
    p=argparse.ArgumentParser();p.add_argument('certificate',type=Path);p.add_argument('--checker',type=Path,required=True)
    p.add_argument('--allow-control-bound',action='store_true',help='accept a positive bound only for checker rehearsal')
    p.add_argument('--plant-cover-gap',action='store_true')
    a=p.parse_args();start=time.monotonic();root=a.certificate
    c=json.loads((root/'certificate.json').read_text());require(c['schema'] in ('p33-b1-v1','p33-b1-sos-v1'),'schema');sos=c['schema']=='p33-b1-sos-v1'
    require(c['coefficient'] in ([1,1],[3999,4000]),'coefficient')
    bn,bd=c['bound'];require(type(bn)==int and type(bd)==int and bd>0 and bn>=0,'bound')
    require(c['bound']==[0,1] or a.allow_control_bound,'statement')
    require(c['cut_bound']==[2,5] and c['density_bound']==[464101615,1000000000],'hypotheses')
    require(c['classes']==40547 and c['psd_blocks']==38,'dimensions')
    S,D=c['scale'],c['class_denominator'];require(isinstance(S,int) and S>0 and D==180000000000,'scales')
    payload={}
    for record in c['files']:
        name=record['file'];require('/' not in name and name not in payload,'file name')
        data=(root/name).read_bytes();require(hashlib.sha256(data).hexdigest()==record['sha256'] and len(data)==record['bytes'],'file hash')
        payload[name]=json.loads(data)
    blocks=[payload[f'block-{j:02d}.json'] for j in range(38)];ranks=[];types=set()
    require(720000000000%bd==0,'control bound denominator')
    cn,cd=c['coefficient'];lines=[f'{S} {D} {cn} {cd} 38 40547 {bn} {bd} {int(not sos)}']
    for j,b in enumerate(blocks):
        n,k,typ,flags=[b[key] for key in ['n','k','type','flags']];d=len(flags)
        if sos:
            Q=[[0]*d for _ in range(d)]
            for term in b['terms']:
                w=term['weight'];require(type(w)==int and w>=0,'negative PSD term weight')
                require(set(term) in ({'weight','vector'},{'weight','matrix'}),'PSD term fields')
                if 'vector' in term:
                    v=term['vector'];require(len(v)==d and all(type(x)==int for x in v),'PSD vector')
                    seed=[[x*y for y in v] for x in v]
                else:
                    seed=term['matrix'];require(len(seed)==d and all(len(row)==d for row in seed),'PSD seed shape')
                    require(all(type(x)==int for row in seed for x in row),'PSD seed integers')
                    require(all(seed[i][h]==seed[h][i] for i in range(d) for h in range(i)),'PSD seed symmetry')
                    psd([[integer(x) for x in row] for row in seed])
                for i in range(d):
                    for h in range(d):Q[i][h]+=w*seed[i][h]
            ranks.append(None) # PSD proved by positive SOS terms, without rank claim.
        else:Q=b['matrix']
        require((n,k) in [(4,2),(5,4)] and (k,typ) not in types,'block type');types.add((k,typ))
        if j<3:require((n,k,typ,d)==(4,2,[0,2,3][j],40),'regularity basis')
        require(flags==sorted(set(flags)) and all(isinstance(v,int) for v in flags),'flags')
        require(len(Q)==d and all(len(row)==d for row in Q),'matrix shape')
        require(all(isinstance(v,int) for row in Q for v in row),'matrix integer')
        require(all(Q[i][j]==Q[j][i] for i in range(d) for j in range(i)),'asymmetric matrix')
        if not sos:ranks.append(psd([[integer(v) for v in row] for row in Q]))
        lines.extend([f'{n} {k} {typ} {d}',' '.join(map(str,flags))]);lines.extend(' '.join(map(str,row)) for row in Q)
    for b in c['local_bases']+[c['global_basis']]:
        n,k,typ,flags=[b[key] for key in ['n','k','type','flags']]
        require(flags==sorted(set(flags)) and all(isinstance(v,int) for v in flags),'scalar flags')
        lines.extend([f'{n} {k} {typ} {len(flags)}',' '.join(map(str,flags))])
    require(len(c['local_bases'])==2,'local basis count')
    y,e=c['inequality_multipliers'],c['equality_multipliers']
    require(len(y)==12847 and all(isinstance(v,int) and v>=0 for v in y),'negative inequality multiplier')
    require(len(e)==120 and all(isinstance(v,int) for v in e),'equality multipliers')
    lines.extend([' '.join(map(str,y)),' '.join(map(str,e))])
    require(len(c['cl_predicates'])==12750,'CL predicate count')
    for i,record in enumerate(c['cl_predicates']):
        if i<510:expected=[i,i//255,-1,3,i%255+1]
        else:
            v=i-510;combo=v//255;expected=[i,combo//24,(combo//3)%8,combo%3+1,v%255+1]
        require(record==expected,'CL row does not match its predicate')
    classes=[]
    for j in range(20):classes.extend(payload[f'classes-{j:02d}.json'])
    require(len(classes)==40547,'class count')
    for row in classes:
        require(len(row)==(3 if sos else 4) and all(type(v)==int for v in row),'class record')
        if not sos:require(row[3]>=0,'negative class slack')
        lines.append(' '.join(map(str,row)))
    with tempfile.TemporaryDirectory() as tmp:
        inputfile=Path(tmp)/'certificate.txt';inputfile.write_text('\n'.join(lines)+'\n')
        command=[str(a.checker.resolve()),str(inputfile)]
        if a.plant_cover_gap:command.append('--plant-cover-gap')
        result=subprocess.run(command,capture_output=True,text=True)
        require(result.returncode==0,'semantic checker rejection: '+result.stdout+result.stderr)
        data=json.loads(result.stdout)
    require(data['status']=='EXACT_B1_IDENTITIES_AND_COVER' and data['coefficient']==c['coefficient'],'checker result')
    print(json.dumps({'status':'POSITIVE_BOUND_CONTROL_A' if bn else 'EXACT_B1_CHECKER_A','semantic':data,'psd_ranks':ranks,'wall_seconds':time.monotonic()-start}),flush=True)


if __name__=='__main__':
    try:main()
    except (ValueError,KeyError,TypeError,AssertionError,IndexError) as e:
        print('REJECT:',str(e),flush=True);raise SystemExit(1)
