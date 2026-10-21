#!/usr/bin/env python3
"""Executable mathematical checks. See README.md for scope and requirements."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import copy
import hashlib
import json
import os
from pathlib import Path
import random
import re
import subprocess
import sys
import tempfile

sys.dont_write_bytecode=True
import options
import positive
from rows import bounds, row, rows_summary, range_entry

HERE=Path(__file__).resolve().parent
DATA=HERE.parent/'data'
MODES=('fast','direct','independent')

def need(ok,msg):
    if not ok: raise ValueError(msg)

def pairs(items):
    d={}
    for k,v in items:
        need(k not in d,'duplicate JSON key');d[k]=v
    return d

def load(p):
    return json.loads(Path(p).read_text(),object_pairs_hook=pairs,
                      parse_constant=lambda s:(_ for _ in ()).throw(ValueError(s)))

def write(p,d):
    p=Path(p);t=p.with_suffix(p.suffix+'.tmp')
    t.write_text(json.dumps(d,sort_keys=True)+'\n');t.replace(p)

def call(cmd,**kw):
    return subprocess.run(list(map(str,cmd)),check=True,**kw)

def cores():
    try: return len(os.sched_getaffinity(0))
    except AttributeError: return os.cpu_count() or 1

def certificate():
    c=load(DATA/'ranges.json')
    fixed=dict(group=[3,9,9],parameters=[243,121,60],singleton_mask=24909666,
               depth=12,batch=4096,cases=8,total_ids=8*3**12,range_count=1038,
               id_rule='case*3**depth+big_endian_ternary_prefix',
               row_rule='ASCII decimal id valid nodes solutions; single spaces; LF per row')
    need(set(c)==set(fixed)|{'ranges'},'range certificate fields')
    need(all(c[k]==v for k,v in fixed.items()),'range certificate definition')
    need(len(c['ranges'])==1038,'range count')
    for r,e in enumerate(c['ranges']):
        need(set(e)=={'range','first','stop','valid','nodes','solutions','rows_sha256'},'range fields')
        need(all(type(e[k]) is int and e[k]>=0 for k in e if k!='rows_sha256'),'range integer grammar')
        need((e['range'],e['first'],e['stop'])==(r,*bounds(r)),'range partition')
        need(e['valid']==e['stop']-e['first'] and e['nodes']>0 and e['solutions']==0,'range counters')
        need(type(e['rows_sha256']) is str and re.fullmatch('[0-9a-f]{64}',e['rows_sha256']),'canonical row digest')
    need(sum(e['nodes'] for e in c['ranges'])==108_733_222_341,'node sum')
    # These are names of mathematical row streams, not file-integrity checks.
    digests=re.findall(r'"([0-9a-f]{64})"',(HERE.parent/'lean/DS243/ReceiptData.lean').read_text())
    need(digests==[e['rows_sha256'] for e in c['ranges']],'Lean range labels differ')
    return c

def compile_one(work,mode,test=False):
    work=Path(work);binary=work/(mode+('-control' if test else '')+'.bin')
    src=HERE/('independent_kernel.cpp' if mode=='independent' else 'sample_kernel.cpp' if mode=='sample' else 'campaign.cpp')
    cmd=['g++','-O3','-std=c++20','-fopenmp']
    if mode in ('fast','direct'): cmd+=['-D'+mode.upper()+'_KERNEL']
    if test: cmd+=['-DTEST_ONLY']
    call([*cmd,src,'-o',binary])
    return binary

def compile_all(work,threads,controls=False):
    jobs=[(m,False) for m in MODES]+([('fast',True),('direct',True)] if controls else [])
    with ThreadPoolExecutor(max_workers=threads) as p:
        vals=list(p.map(lambda x:compile_one(work,*x),jobs))
    return {m+('-control' if t else ''):v for (m,t),v in zip(jobs,vals)}

def production(binary,ids,work,threads,config=None):
    tasks,out=Path(work)/'tasks',Path(work)/'rows'
    rows=[f'{i} 0 0 0 0 0 - - 0' for i in ids]
    while True:
        tasks.write_text('\n'.join(rows)+'\n')
        if out.exists():out.unlink()
        cmd=[binary,DATA/'p243.txt',DATA/'cases.txt',12,60,threads,tasks,out]
        if config is not None:cmd+=['--test-config',config]
        call(cmd)
        data=out.read_bytes();need(data.endswith(b'\n'),'worker final LF')
        nxt=data.decode('ascii').splitlines()
        need(len(nxt)==len(ids),'worker missing/extra rows')
        complete=True
        for i,a,b in zip(ids,rows,nxt):
            x,y=row(a,i),row(b,i)
            need(y[0]>=x[0] and y[1]>=x[1] and y[3]>=x[3] and y[4]>=x[4],'worker moved backwards')
            need(not x[0] or x[2]==y[2],'prefix validity changed')
            need(not x[1] or a==b,'completed row changed')
            complete &= bool(y[1])
        rows=nxt
        if complete:return rows
        # Caller-selected work directory is the checkpoint location. No previous
        # run is trusted as fresh execution; every invocation starts from zeros.
        write(Path(work)/'checkpoint.json',{'ids':ids,'rows':rows})
        print('CHECKPOINT completed',sum(row(x,i)[1] for i,x in zip(ids,rows)),'of',len(ids),flush=True)

def tuples(data,ids):
    need(data.endswith(b'\n'),'independent row final LF')
    lines=data.decode('ascii').splitlines();need(len(lines)==len(ids),'independent row count')
    result=[]
    for i,l in zip(ids,lines):
        need(re.fullmatch(r'(0|[1-9][0-9]*) (0|1) (0|[1-9][0-9]*) (0|[1-9][0-9]*)',l),'independent row grammar')
        t=list(map(int,l.split()));need(t[0]==i,'independent ID/coverage')
        need((t[1]==0 and t[2:]==[0,0]) or (t[1]==1 and t[2]>0),'independent counters')
        need(t[3]==0,'solution found; negative claim rejected');result.append(t)
    return result

def actual(mode,binary,first,stop,work,threads):
    ids=list(range(first,stop))
    if mode in ('fast','direct'):
        return range_entry(first//4096,production(binary,ids,work,threads))
    env=dict(os.environ,OMP_NUM_THREADS=str(threads))
    data=call([binary,DATA/'p243.txt',DATA/'cases.txt',0,first,stop],capture_output=True,env=env).stdout
    ts=tuples(data,ids)
    return dict(range=first//4096,first=first,stop=stop,valid=sum(x[1] for x in ts),
                nodes=sum(x[2] for x in ts),solutions=sum(x[3] for x in ts),
                rows_sha256=hashlib.sha256(data).hexdigest())

def match(a,e):
    need(a==e,'fresh replay digest/count mismatch at range '+str(e['range']))

def option_controls(bins,work):
    tabs=[]
    for m in ('fast','direct'):
        path=Path(work)/('choices_'+m.upper()+'.json')
        call([bins[m+'-control'],'--dump-choices',DATA/'p243.txt',DATA/'cases.txt',path])
        tabs.append(options.check(path))
        bad=Path(work)/('bad-'+m+'.json')
        call([bins[m+'-control'],'--dump-choices',DATA/'p243.txt',DATA/'cases.txt',bad,'--drop-option'])
        rejected=False
        try:options.check(bad)
        except ValueError:rejected=True
        need(rejected,'dropped compiled option was accepted')
    need(tabs[0]==tabs[1],'production option dumps disagree')
    print('PASS compiled options: both kernels, all 8 x 24 x 3 ordered options; dropped options rejected',flush=True)

def smoke(bins,work,threads):
    expected=load(DATA/'smoke-rows.json');ids=[r[0] for r in expected]
    for m in ('fast','direct'):
        rows=production(bins[m],ids,work,threads)
        got=[[i,*row(l,i,final=True)[2:]] for i,l in zip(ids,rows)]
        need(got==expected,m+' smoke rows differ')
    for e in expected:
        got=call([bins['independent'],DATA/'p243.txt',DATA/'cases.txt',0,e[0],e[0]+1],capture_output=True,
                 env=dict(os.environ,OMP_NUM_THREADS=str(threads))).stdout
        need(tuples(got,[e[0]])==[e],'independent smoke row differs')
    print('PASS eight fixed depth-12 IDs in all three complete kernels; sample only',flush=True)

def positive_controls(bins,work,threads):
    expected=positive.controls();modes={}
    for m in ('fast','direct'):
        rec={}
        for label,delta in (('bound_M',0),('bound_M_minus_1',-1)):
            config=Path(work)/'control-config'
            config.write_text(''.join(f"{r['maximum']+delta} {r['word']}\n" for r in expected))
            ids=[i for r in expected for i in ([r['prefix_id'],r['wrong_prefix_id']] if delta==0 else [r['prefix_id']])]
            production(bins[m+'-control'],ids,work,threads,config)
            rec[label]=positive.parse_rows(Path(work)/'rows',ids)
        modes[m]=rec
    positive.check_results(expected,modes)
    write(Path(work)/'positive.json',dict(test_only=True,mathematical_difference_set_claim=False,controls=expected,modes=modes))
    print('PASS same-group positive-prefix and M-1 controls in both TEST_ONLY builds; these are not difference sets',flush=True)

def discovery_control(work):
    # This source receives neither a witness nor a precomputed orbit list.
    binary=Path(work)/'discovery.bin'
    call(['g++','-O3','-std=c++20',HERE/'discovery.cpp','-o',binary])
    result=call([binary],capture_output=True,text=True)
    need(result.stderr.strip()=='orbits=24 fixed_DS=88','positive discovery count differs')
    sets=[]
    for line in result.stdout.splitlines():
        words=line.split()
        need(len(words)==40 and all(re.fullmatch(r'0|[1-9][0-9]*',x) for x in words),'discovery witness grammar')
        points=sorted(map(int,words))
        need(len(set(points))==40 and all(0<=x<121 for x in points),'discovery witness cardinality')
        need({3*x%121 for x in points}==set(points),'discovery multiplier invariance')
        counts=[0]*121
        for a in points:
            for b in points:
                if a!=b:counts[(a-b)%121]+=1
        need(counts[0]==0 and counts[1:]==[13]*120,'discovery witness ordered differences')
        sets.append(points)
    need(len(sets)==len({tuple(s) for s in sets})==88,'missing or duplicate discovered sets')
    write(Path(work)/'discovery.json',dict(group=[121],parameters=[121,40,13],multiplier=3,sets=sets))
    print('PASS genuine C121 positive discovery: 88 sets recovered without supplied witnesses; all independently checked',flush=True)

def frontend_check(artifact=DATA/'frontend.json',p243=DATA/'p243.txt',cases=DATA/'cases.txt',capture=False):
    return subprocess.run([sys.executable,str(HERE/'frontend_certificate.py'),str(artifact),str(p243),str(cases)],
                          capture_output=capture,text=True)

def frontend_corruptions(work,threads):
    orig=load(DATA/'frontend.json');jobs=[]
    def add(label,fn):
        c=copy.deepcopy(orig);fn(c);p=Path(work)/(label+'.json');write(p,c);jobs.append((p,DATA/'p243.txt',DATA/'cases.txt'))
    def swap(a,i,j):a[i],a[j]=a[j],a[i]
    add('phi',lambda c:swap(c['maps'][3]['phi'],5,6))
    add('translation',lambda c:c['maps'][0].__setitem__('phi',[(v+1)%243 for v in c['maps'][0]['phi']]))
    add('qperm',lambda c:swap(c['maps'][2]['qperm'],1,2))
    add('duplicate-map',lambda c:c['maps'].__setitem__(1,c['maps'][0]))
    add('duplicate-image',lambda c:c['images'].__setitem__(5,c['images'][4]))
    def change_image(c):
        a=c['images'][7];swap(a,a.index(3,1),a.index(6,1))
    add('image-swap',change_image)
    add('representative',lambda c:c['representatives'].__setitem__(0,c['images'][0] if c['images'][0]!=c['representatives'][0] else c['images'][1]))
    add('cover-map',lambda c:c['image_cover'][10].__setitem__(1,(c['image_cover'][10][1]+1)%27))
    add('singleton-param',lambda c:c['singleton_cover'][100].__setitem__(2,(c['singleton_cover'][100][2]+1)%3))
    add('singleton-mask',lambda c:c['singleton_cover'][50].__setitem__(0,c['singleton_cover'][50][0]^3))
    add('singleton-drop',lambda c:c['singleton_cover'].pop())
    add('mask',lambda c:c.__setitem__('S0',c['S0']+1))
    add('cell-drop',lambda c:c['cell_orbit_lines'].pop('1'))
    add('short-image',lambda c:c['images'].__setitem__(0,c['images'][0][:26]))
    add('group',lambda c:c.__setitem__('group',[3,3,27]))
    add('map-drop',lambda c:c.__setitem__('maps',c['maps'][:-1]))
    rows=[list(map(int,l.split())) for l in (DATA/'cases.txt').read_text().splitlines()]
    for n in range(3):
        bad=copy.deepcopy(rows)
        if n==0:bad[1]=bad[0][:]
        elif n==1:bad[0][2],bad[0][3]=bad[0][3],bad[0][2]
        else:bad[0][0]=9
        path=Path(work)/f'cases-{n}.txt';path.write_text(''.join(' '.join(map(str,r))+'\n' for r in bad))
        jobs.append((DATA/'frontend.json',DATA/'p243.txt',path))
    lines=(DATA/'p243.txt').read_text().splitlines();a,b=lines.index('3 1 4 7'),lines.index('3 28 31 34')
    lines[a],lines[b]='3 4 7 28','3 1 31 34';path=Path(work)/'regrouped.txt';path.write_text('\n'.join(lines)+'\n')
    jobs.append((DATA/'frontend.json',path,DATA/'cases.txt'))
    def rejects(job):
        r=frontend_check(*job,capture=True)
        need(r.returncode!=0 and 'FAIL' in r.stdout,'frontend corruption not explicitly rejected')
    with ThreadPoolExecutor(max_workers=threads) as p:list(p.map(rejects,jobs))
    print('PASS finite artifact and input corruptions, including regrouped multiplier partition',len(jobs),flush=True)

def quick(work,threads):
    certificate();frontend_check().check_returncode()
    bins=compile_all(work,threads,controls=True)
    option_controls(bins,work);smoke(bins,work,threads);positive_controls(bins,work,threads)
    frontend_corruptions(work,threads)
    discovery_control(work)
    print('QUICK CHECK ONLY: finite structure, options and bounded controls passed; no exhaustive lifting replay.',flush=True)
    return bins

def complete_cover(work,threads):
    # Opaque production observations and a separate definition-based checker.
    base=Path(work)/'complete-cover';base.mkdir()
    results=base/'results';results.mkdir()
    call([sys.executable,HERE/'export_coverage.py','--output',base/'observations','--threads',threads])
    binary=base/'coverage-kernel.bin'
    call(['g++','-O3','-std=c++20','-fopenmp',HERE/'coverage_kernel.cpp','-o',binary])
    result=call([binary,'singleton',results/'passing-masks.txt','--threads',threads],capture_output=True,text=True)
    (results/'singleton-result.json').write_text(result.stdout)
    result=call([binary,'prefix',base/'observations',base,8,'--threads',threads],capture_output=True,text=True)
    (results/'prefix-result.txt').write_text(result.stdout)
    env=dict(os.environ,DS243_COVER_WORK=str(base),COVER_THREADS=str(threads))
    call([sys.executable,HERE/'exhaustive_cover.py','baseline','--threads',threads],env=env)
    expected={'gap-prefix':'MISSING PREFIX witness ID=4095',
              'gap-option':'MISSING ACTUAL INVARIANT SUBSET',
              'gap-case':'MISSING IMAGE ORBIT'}
    records=[]
    for mode,reason in expected.items():
        result=subprocess.run([sys.executable,str(HERE/'exhaustive_cover.py'),mode,'--threads',str(threads)],
                              env=env,capture_output=True,text=True)
        need(result.returncode==1 and reason in result.stderr,'semantic cover gap not explicitly rejected')
        records.append(dict(gap=mode,reason=result.stderr.strip(),semantic_gap_caught=True))
        print('PASS semantic cover',mode,result.stderr.strip(),flush=True)
    write(results/'semantic-gaps.json',records)
    print('PASS separate exhaustive cover: all 4,251,528 actual IDs in each production decoder, all options and three semantic gaps; no tail search.',flush=True)

def finite(work,threads,bins=None):
    if bins is None:
        bins={m+'-control':compile_one(work,m,True) for m in ('fast','direct')}
        option_controls(bins,work)
    call([sys.executable,HERE/'frontend.py','all','--threads',threads,'--out',Path(work)/'frontend.json'])
    need(load(Path(work)/'frontend.json')==load(DATA/'frontend.json'),'complete frontend differs by parsed fields')
    # The cover implementation uses independently defined full-group maps,
    # compiled option dumps, and 1000 disguised-leaf normalization round trips.
    call([sys.executable,HERE/'cover.py',1,1000,work])
    call([sys.executable,HERE/'quotient_identity.py'])
    for name in ('singletons','quotient'):
        binary=Path(work)/name
        call(['g++','-O3','-std=c++20',HERE/(name+'.cpp'),'-o',binary])
        output=call([binary],cwd=work,capture_output=True,text=True).stdout
        print(output,end='',flush=True)
        if name=='singletons':
            need('tested13=20058300 layer_ok=5335092 pass=7776' in output and
                 'maps=23328 orbit=7776 stab=3 orbit==pass:1 mask_in_pass:1' in output,
                 'separate complete singleton enumeration differs')
        else:
            need('forms=13 line-count solutions=144 autocorrelation-passing=144' in output,
                 'separate quotient DFS counts differ')
    imgs={tuple(map(int,l.split())) for l in (Path(work)/'qdfs_images.txt').read_text().splitlines()}
    want={tuple(map(int,l.split())) for l in (DATA/'images.txt').read_text().splitlines()}
    need(imgs==want and len(imgs)==144,'separate quotient DFS differs')
    complete_cover(work,threads)
    print('PASS complete independent frontend/cover enumeration and all 38 input mutations; no exhaustive lifting replay.',flush=True)

def replay(work,threads,kernel,first,stop,c=None,bins=None):
    c=c or certificate();need(0<=first<stop<=1038,'range bounds')
    modes=MODES if kernel=='all' else (kernel,)
    bins=bins or {m:compile_one(work,m) for m in modes}
    for m in modes:
        out=Path(work)/m;out.mkdir(exist_ok=True)
        for r in range(first,stop):
            e=c['ranges'][r]
            a=actual(m,bins[m],e['first'],e['stop'],out,threads)
            match(a,e)
            write(out/f'range-{r:04d}.json',a)
            print('REPLAY MATCH',m,r,flush=True)
        if first==0 and stop==1038:
            print('FULL EXHAUSTIVE LIFTING REPLAY MATCH',m,'1038 ranges, 4,251,528 IDs, zero solutions',flush=True)
        else:print('BOUNDED REPLAY ONLY',m,first,stop,flush=True)

def corruptions(work,threads,bins=None):
    c=certificate();bad=copy.deepcopy(c['ranges'][0]);h=bad['rows_sha256'];bad['rows_sha256']=('1' if h[0]=='0' else '0')+h[1:]
    bins=bins or {m:compile_one(work,m) for m in MODES}
    for m in MODES:
        out=Path(work)/('corrupt-'+m);out.mkdir()
        a=actual(m,bins[m],0,4096,out,threads)
        match(a,c['ranges'][0]);rejected=False
        try:match(a,bad)
        except ValueError as e:
            need('fresh replay digest/count mismatch' in str(e),'wrong corruption failure');rejected=True
        need(rejected,'changed range digest was accepted')
        print('PASS changed range-0 digest rejected by fresh',m,'execution',flush=True)
    frontend_corruptions(work,threads)

def sample(work,threads,bins=None):
    # The original fixed selection is retained; this is additional sample evidence.
    ids=set()
    for c in range(8):
        ids.update(range(c*3**12,c*3**12+25));ids.update(range((c+1)*3**12-25,(c+1)*3**12))
    rng=random.Random(20261020)
    while len(ids)<10000:ids.add(rng.randrange(8*3**12))
    ids=sorted(ids);bins=bins or {m:compile_one(work,m) for m in ('fast','direct')}
    independent=compile_one(work,'sample')
    chunks=[ids[i::threads] for i in range(threads)]
    def batch(chunk):
        data=call([independent,DATA/'cases.txt'],input=('\n'.join(map(str,chunk))+'\n').encode(),capture_output=True).stdout
        return tuples(data,chunk)
    with ThreadPoolExecutor(max_workers=threads) as p:parts=list(p.map(batch,chunks))
    rows=sorted(r for part in parts for r in part)
    for m in ('fast','direct'):
        got=production(bins[m],ids,work,threads)
        need([[i,*row(l,i,final=True)[2:]] for i,l in zip(ids,got)]==rows,'fixed sample differs')
    write(Path(work)/'sample-rows.json',rows)
    print('PASS 10,000 fixed sampled IDs; independent scalar-orbit implementation and production pair agree. Sample only.',flush=True)

def summary(paths,kernel):
    c=certificate();modes=MODES if kernel=='all' else (kernel,)
    for m in modes:
        found={}
        for base in paths:
            for path in (Path(base)/m).glob('range-*.json'):
                e=load(path);r=e['range'];need(r not in found,'duplicate range in summary');match(e,c['ranges'][r]);found[r]=e
        need(set(found)==set(range(1038)),'incomplete range cover in summary')
        print('COMPLETE MATCHING RECORDS',m,'1038 ranges; summary reads records and does not execute search.',flush=True)

def main():
    need(sys.flags.optimize==0,'Python assertions must be enabled')
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('command',choices=['quick','frontend','cover','replay','full','corruptions','sample','summary'])
    p.add_argument('--work',type=Path,help='new output directory outside this public subtree')
    p.add_argument('--threads',type=int,default=cores())
    p.add_argument('--kernel',choices=(*MODES,'all'),default='all')
    p.add_argument('--first-range',type=int,default=0);p.add_argument('--stop-range',type=int,default=1038)
    p.add_argument('--pieces',type=Path,nargs='+')
    a=p.parse_args();need(a.threads>0,'positive thread count')
    if a.command=='summary':
        need(a.pieces,'summary needs --pieces');summary(a.pieces,a.kernel);return
    need(a.work is not None,'--work is required')
    work=a.work.resolve();need(not work.is_relative_to(HERE.parent),'work directory must be outside public subtree')
    work.mkdir(parents=True,exist_ok=False)
    if a.command=='quick':quick(work,a.threads)
    elif a.command=='frontend':finite(work,a.threads)
    elif a.command=='cover':complete_cover(work,a.threads)
    elif a.command=='replay':
        frontend_check().check_returncode()
        replay(work,a.threads,a.kernel,a.first_range,a.stop_range)
    elif a.command=='corruptions':
        frontend_check().check_returncode()
        corruptions(work,a.threads)
    elif a.command=='sample':sample(work,a.threads)
    else:
        bins=quick(work,a.threads);finite(work,a.threads,bins)
        sample(work,a.threads,bins);replay(work,a.threads,'all',0,1038,bins=bins)
        corruptions(work,a.threads,bins)
        print('FULL CHECK: complete frontend and exhaustive replay of all three complete kernels passed.',flush=True)

if __name__=='__main__':
    try:main()
    except (ValueError,KeyError,IndexError,TypeError) as e:
        print('FAIL',e,file=sys.stderr);sys.exit(1)
