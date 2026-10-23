#!/usr/bin/env python3
"""Independent manifest, receipt, and exact symmetric-circulant checks."""
import argparse
import bisect
import concurrent.futures
import hashlib
import json
import math
import mmap
import os
from pathlib import Path
import re
import shutil
import struct
import sys
import time

class Invalid(Exception): pass
def require(ok, why):
    if not ok: raise Invalid(why)
def integers(values):
    try:
        require(all(re.fullmatch(r'-?[0-9]+',v) for v in values),'integer syntax')
        return list(map(int,values))
    except (ValueError,OverflowError) as e: raise Invalid('integer syntax') from e
def seconds(v):
    try: t=float(v)
    except ValueError as e: raise Invalid('time syntax') from e
    require(math.isfinite(t) and t>=0,'negative/nonfinite time')
    return t
def read_classes(path):
    out=[]; offset=0; keys=set(); vectors=set()
    allowed={1,-3,5,-7,9,-11,13,-15}
    for line in Path(path).read_text().splitlines():
        f=line.split('\t'); require(len(f)==7,'class field count')
        i,key,r,n,off=integers([f[j] for j in (0,1,2,4,5)])
        x=integers(f[3].split(',')); require(len(x)==7,'compressed vector length')
        require(i==len(out) and off==offset and n>0,'class numbering/count/offset')
        require(r in allowed and x[0] in (-3,1,5) and all(v in (-5,-3,-1,1,3,5) for v in x[1:]),'compressed vector values')
        require(x[0]+2*sum(x[1:])==r,'compressed rowsum')
        require(key not in keys and tuple(x) not in vectors,'duplicate class')
        require(re.fullmatch('[0-9a-f]{64}',f[6]) is not None,'class hash syntax')
        out.append(dict(id=i,key=key,r=r,x=x,n=n,off=off,sha=f[6]));offset+=n;keys.add(key);vectors.add(tuple(x))
    require(len(out)==15251 and offset==396050997,'class totals')
    return out
def read_units(path,classes):
    units=[]; seen=set()
    for line in Path(path).read_text().splitlines():
        f=integers(line.split('\t'));require(len(f)==6,'unit field count')
        i,*q,orbit=f;require(i==len(units),'unit id sequence')
        require(all(0<=c<len(classes) for c in q),'unit class range')
        require(tuple(q) not in seen,'duplicate unit tuple');seen.add(tuple(q))
        require(orbit in (1,2,3,6),'unit orbit size');units.append((tuple(q),orbit))
    return units
def check_cover(units_path,classes,minima_path):
    units=read_units(units_path,classes)
    minima={tuple(v[:4]):v[4] for line in Path(minima_path).read_text().splitlines() if (v:=integers(line.split('\t')))}
    require(len(minima)==70699,'independent minima count')
    require(dict(units)==minima and len(units)==len(minima),'units differ from independently enumerated orbit minima')
    return f'units={len(units)}'
def check_rows(path,classes):
    expected=sum(c['n'] for c in classes)*4
    require(Path(path).stat().st_size==expected,f'rows byte length: expected {expected}, got {Path(path).stat().st_size}')
    with open(path,'rb') as f, mmap.mmap(f.fileno(),0,access=mmap.ACCESS_READ) as mm:
        def one(c):
            view=memoryview(mm)[4*c['off']:4*(c['off']+c['n'])]
            digest=hashlib.sha256(view).hexdigest();view.release()
            return digest==c['sha']
        with concurrent.futures.ThreadPoolExecutor(max_workers=os.cpu_count()) as pool:
            require(all(pool.map(one,classes)),'rows class SHA-256 mismatch')
    return f'rows={expected//4} classes={len(classes)}'
def read_counts(path,classes):
    counts=[]
    for line in Path(path).read_text().splitlines():
        f=line.split('\t');require(len(f)==4,'counts syntax');i,n,k=integers(f[:3])
        require(i==len(counts) and i<len(classes),'counts sequence');c=classes[i]
        require(n==c['n'] and 0<=k<=n and f[3]==c['sha'],'regenerated class counts/hash')
        counts.append((n,k))
    require(len(counts)==len(classes),'counts class total');return counts
def mask_image(mask,u):
    return sum(((mask>>(min(i*u%65,65-i*u%65)-1))&1)<<(i-1) for i in range(1,33))
def exact_matrix(masks):
    # For symmetric circulants, the first row of M^2 is periodic autocorrelation.
    # Checking all 65 shifts therefore checks every entry of all 65 matrix rows.
    x=[[1]+[-1 if (m>>(min(i,65-i)-1))&1 else 1 for i in range(1,65)] for m in masks]
    for k in range(65):
        a=sum(row[j]*row[(j+k)%65] for row in x for j in range(65))
        require(a==(260 if k==0 else 0),f'exact matrix check shift={k} value={a}')
def member(mm,c,m):
    lo,hi=c['off'],c['off']+c['n']
    while lo<hi:
        mid=(lo+hi)//2; v=struct.unpack_from('<I',mm,mid*4)[0]
        if v<m:lo=mid+1
        else:hi=mid
    return lo<c['off']+c['n'] and struct.unpack_from('<I',mm,lo*4)[0]==m
def check_receipts(directory,units_path,classes,counts_path,rows_path,begin,end):
    units=read_units(units_path,classes);counts=read_counts(counts_path,classes)
    require(0<=begin<end<=len(units),'requested receipt range')
    got={};ranges=[];batch_cpu=0.;batch_wall=0.;line_cpu=0.;batches=0
    prefix='pair=1 xor=1 kmin=1 keybits=64'
    for path in sorted(Path(directory).iterdir()):
        if path.name.endswith('.tmp') or path.name=='solutions.tsv':continue
        match=re.fullmatch(r'batch_([0-9]{6})_([0-9]{6})\.tsv',path.name)
        require(match is not None,f'unrecognized receipt file {path.name}')
        b0,b1=map(int,match.groups());require(0<=b0<b1<=len(units),'batch range bounds')
        if b1<=begin or b0>=end:continue
        require(begin<=b0<b1<=end,'batch straddles restricted receipt range')
        require(all(b1<=a or b0>=b for a,b in ranges),'overlapping batch ranges');ranges.append((b0,b1))
        lines=path.read_text().splitlines();require(bool(lines),'empty batch')
        last=lines[-1].split('\t');require(len(last)==6 and last[0]=='END','missing/malformed END')
        require(integers(last[1:3])==[b0,b1],'END filename range mismatch')
        batch_cpu+=seconds(last[3]);batch_wall+=seconds(last[4]);flags=last[5]
        require(flags==prefix or flags.startswith(prefix+' '),'production flags prefix')
        tokens=flags.split(); require(len({s.split('=')[0] for s in tokens})==len(tokens),'duplicate production flag')
        require(all(re.fullmatch(r'[A-Za-z0-9_]+=[A-Za-z0-9_]+',s) for s in tokens),'flag syntax')
        require(len(lines)-1==b1-b0,'batch receipt line count')
        local=set()
        for line in lines[:-1]:
            f=line.split('\t');require(len(f)==20 and f[0]=='U','receipt syntax')
            vals=integers(f[1:19]);unit=vals[0];q=tuple(vals[1:5]);pairing,desig=vals[5:7]
            sizes=vals[7:11];npass,store,probe,ss,sp,matches,sols=vals[11:18]
            line_cpu+=seconds(f[19])
            require(b0<=unit<b1,'unit outside batch range');require(unit not in got,'duplicate unit receipt')
            require(q==units[unit][0],'receipt unit classes')
            require(pairing in (0,1,2) and desig in range(4),'pairing/designated position')
            expected=[counts[c][int(p==desig)] for p,c in enumerate(q)]
            require(sizes==expected,'list size differs from regenerated kernel/full counts')
            a,b,c,d=((0,1,2,3),(0,2,1,3),(0,3,1,2))[pairing]
            products=sorted((sizes[a]*sizes[b],sizes[c]*sizes[d]))
            require([store,probe]==products,'pairs counts inconsistent with pairing/list sizes')
            require(0<=ss<=store and 0<=sp<=probe,'survivors outside pair bounds')
            require(matches>=sols>=0 and npass>=0,'negative/inconsistent matches/solutions/npass')
            got[unit]=dict(q=q,desig=desig,sols=sols);local.add(unit)
        require(local==set(range(b0,b1)),'batch missing unit');batches+=1
    require(set(got)==set(range(begin,end)),'missing unit receipt')
    solutions=Path(directory)/'solutions.tsv';require(solutions.is_file(),'missing solutions.tsv')
    actual={u:0 for u in got};unique=set()
    with open(rows_path,'rb') as f, mmap.mmap(f.fileno(),0,access=mmap.ACCESS_READ) as mm:
        for line in solutions.read_text().splitlines():
            f=line.split();require(len(f)==6 and f[0]=='SOLUTION','solution syntax');u,*m=integers(f[1:])
            require(0<=u<len(units),'solution unit range')
            if not begin<=u<end:continue
            require(all(0<=v<2**32 for v in m),'solution mask range')
            exact_matrix(m)
            rec=got[u];require(all(member(mm,classes[c],v) for c,v in zip(rec['q'],m)),'solution row outside its retained class')
            d=rec['desig'];require(all(m[d]<=mask_image(m[d],v) for v in (14,27,53)),'solution designated mask not kernel minimal')
            require((u,*m) not in unique,'duplicate solution');unique.add((u,*m));actual[u]+=1
    require(all(actual[u]==got[u]['sols'] for u in got),'solution lines differ from receipt totals')
    return f'range={begin}..{end-1} units={len(got)} batches={batches} solutions={sum(actual.values())} reported_line_cpu={line_cpu:.3f} reported_batch_cpu={batch_cpu:.3f} reported_batch_wall_sum={batch_wall:.3f}'
def timed(label,fn,reject=False):
    cpu=time.process_time();wall=time.perf_counter();detail='';valid=False
    try:detail=fn();valid=True
    except (Invalid,OSError,ValueError,IndexError,KeyError) as e: detail=str(e)
    passed=valid!=reject
    print(f'{"PASS" if passed else "FAIL"} {label} '+('rejected: ' if reject and not valid else '')+detail+f' cpu={time.process_time()-cpu:.6f} wall={time.perf_counter()-wall:.6f}',flush=True)
    return passed
def main():
    p=argparse.ArgumentParser();p.add_argument('--classes',required=True);p.add_argument('--units',required=True);p.add_argument('--results',required=True);p.add_argument('--receipts',required=True);p.add_argument('--begin',type=int,default=0);p.add_argument('--end',type=int);p.add_argument('--corruptions',action='store_true');a=p.parse_args()
    try: classes=read_classes(a.classes)
    except Exception as e:print('FAIL class_manifest',e);return 1
    end=len(read_units(a.units,classes)) if a.end is None else a.end
    result=Path(a.results);rows=result/'rows.bin';counts=result/'class-counts.tsv';minima=result/'cover-minima.tsv'
    receipts=lambda d=a.receipts,u=a.units:check_receipts(d,u,classes,counts,rows,a.begin,end)
    checks=[timed('rows_file',lambda:check_rows(rows,classes)),timed('cover_manifest',lambda:check_cover(a.units,classes,minima)),timed('receipts_unmodified',receipts)]
    if not a.corruptions:return 0 if all(checks) else 1
    dest=result/'corruptions';dest.mkdir(exist_ok=True)
    original=Path(a.receipts);batch_names=sorted(q.name for q in original.glob('batch_*.tsv'))
    require(len(batch_names)>=2,'corruption fixture needs two batches')
    def fixture(name):
        d=dest/name
        if d.exists():shutil.rmtree(d)
        shutil.copytree(original,d);return d
    def edit_line(d,field=None):
        q=d/batch_names[0];lines=q.read_text().splitlines()
        if field is None:del lines[0]
        else:
            fields=lines[0].split('\t');fields[field]=str(int(fields[field])+1);lines[0]='\t'.join(fields)
        q.write_text('\n'.join(lines)+'\n')
    d=fixture('deleted_receipt');edit_line(d);checks.append(timed('corrupt_deleted_receipt',lambda:receipts(d),True))
    d=fixture('duplicate_unit');q=d/batch_names[1];lines=q.read_text().splitlines();lines.insert(0,(d/batch_names[0]).read_text().splitlines()[0]);q.write_text('\n'.join(lines)+'\n');checks.append(timed('corrupt_duplicate_unit',lambda:receipts(d),True))
    d=fixture('list_size');edit_line(d,8);checks.append(timed('corrupt_list_size',lambda:receipts(d),True))
    d=fixture('pairs_count');edit_line(d,13);checks.append(timed('corrupt_pairs_count',lambda:receipts(d),True))
    d=fixture('keybits12');q=d/batch_names[0];q.write_text(q.read_text().replace('keybits=64','keybits=12'));checks.append(timed('corrupt_keybits12',lambda:receipts(d),True))
    u=dest/'units-deleted.tsv';u.write_text('\n'.join(Path(a.units).read_text().splitlines()[:-1])+'\n');checks.append(timed('corrupt_units_cover_gap',lambda:check_cover(u,classes,minima),True))
    damaged=dest/'rows-truncated.bin';shutil.copyfile(rows,damaged)
    with damaged.open('r+b') as f:f.truncate(rows.stat().st_size-4)
    checks.append(timed('corrupt_rows_removed_mask',lambda:check_rows(damaged,classes),True))
    # Keep the large corrupted rows in scratch, but package only its size/hash recipe.
    with open(rows,'rb') as f:
        f.seek(-4,2);removed_mask=struct.unpack('<I',f.read(4))[0]
    (dest/'rows-truncated.json').write_text(json.dumps(dict(operation='copy rows.bin, truncate final uint32-LE mask',removed_mask=removed_mask,bytes=damaged.stat().st_size),indent=2)+'\n')
    d=fixture('false_solution');q=d/'solutions.tsv';q.write_text(q.read_text()+'SOLUTION 0 0 0 0 0\n');checks.append(timed('corrupt_false_solution',lambda:receipts(d),True))
    return 0 if all(checks) else 1
if __name__=='__main__':sys.exit(main())
