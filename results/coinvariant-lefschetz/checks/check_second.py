#!/usr/bin/env python3
"""Independent pair-cover audit and Singular arithmetic replay, with NO std/lift.
This program imports neither the search generator nor the C++ checker.
"""
import pathlib,sys,ast,re,json,subprocess,concurrent.futures,time,resource

def parse(s,names,p):
 out={}
 for t in re.findall(r'[+-]?[^+-]+',s):
  sign=-1 if t.startswith('-') else 1;t=t.lstrip('+-');factors=t.split('*');coef=sign;e=[0]*len(names)
  for f in factors:
   if f.isdigit():coef*=int(f);continue
   v,_,power=f.partition('^');assert v in names,('unknown variable',v);e[names.index(v)]+=int(power) if power else 1
  e=tuple(e);assert e not in out,'duplicate term';out[e]=coef%p
 return {e:c for e,c in out.items() if c}
def lead(s,names,p,w):
 terms=parse(s,names,p);assert terms,'zero basis';degrees={sum(a*b for a,b in zip(e,w)) for e in terms};assert len(degrees)==1,'inhomogeneous'
 e=max(terms,key=lambda e:tuple(-a for a in reversed(e)))
 return e,terms[e]
def monomial(e,names):return '*'.join(f'{v}^{k}' for v,k in zip(names,e) if k) or '1'
def div(a,b):return all(x<=y for x,y in zip(a,b))
def lcm(a,b):return tuple(max(x,y) for x,y in zip(a,b))

def prepare(cert,plan,dest,workers,corrupt=False):
 dest.mkdir(parents=True,exist_ok=True)
 with cert.open() as f:
  assert f.readline().strip()=='CFG_POLY_V1';p,n,ni,ng=map(int,f.readline().split());assert (p,n,ni) in [(1009,6,6),(73,5,5)]
  names=list('abcdyz') if n==6 else ['x1','x2','x3','x4','x5'];w=[3,4,6,9,1,1] if n==6 else [1]*5
  order=(cert.parent/'unit-order.txt').read_text().split();assert order[:4]==['CFG_ORDER_V1',str(p),str(n),'weighted_degree_reverse_lex'],'bad declared order'
  assert order[4:4+n]==names and len(order)==4+2*n,'declared variable order'
  declared_weights=list(map(int,order[4+n:]));assert all(v>0 for v in declared_weights) and declared_weights==w,'nonpositive or incorrect declared weights'
  Is=[None]*ni;Gs=[None]*ng;firstT=None
  while True:
   offset=f.tell();line=f.readline()
   if not line:break
   tag,i,expr=line.split(maxsplit=2)
   if tag=='I':assert Is[int(i)-1] is None;Is[int(i)-1]=expr.strip()
   elif tag=='G':assert Gs[int(i)-1] is None;Gs[int(i)-1]=expr.strip()
   else:assert tag=='T';firstT=offset;break
  assert all(x is not None for x in Is+Gs)
  L=[lead(s,names,p,w) for s in Gs]
  init=[tuple(ast.literal_eval(l.replace('{','[').replace('}',']'))) for l in (cert.parent/'unit-initial.txt').read_text().splitlines() if l.strip()]
  assert init==[e for e,c in L],'certificate/initial mismatch'
  pure_bounds=[]
  for j in range(n):
   powers=[e[j] for e,c in L if e[j]>0 and all(x==0 for k,x in enumerate(e) if k!=j)]
   assert powers,('missing pure power',j);pure_bounds.append(min(powers))
  if n==6:
   for i,k in enumerate([6,12,18,24,30,42]):
    anchor={}
    for line in (pathlib.Path(__file__).resolve().parents[1]/'data/inputs'/f'input-{k}.txt').read_text().splitlines():
     e,c=line.split(':');anchor[tuple(ast.literal_eval(e.replace('{','[').replace('}',']')))]=int(c)%p
    assert parse(Is[i],names,p)==anchor,'frozen input mismatch'
  # G33 input pinning is checked by separate invariant/substitution validator.
  ring=f'ring R={p},({",".join(names)}),'+('wp(3,4,6,9,1,1);' if n==6 else 'dp;')+'\nshort=0;\n'
  base=ring+'ideal I;\n'+''.join(f'I[{i+1}]={s};\n' for i,s in enumerate(Is))
  writers=[(dest/f'member-{b}.sing').open('w') for b in range(workers)]
  counts=[0]*workers
  for h in writers:h.write(base+'poly q;int errors=0;\n')
  # column-grouped T permits a genuinely streamed replay.
  seen=set();last=0;f.seek(firstT);current=0;h=None
  for line in f:
   tag,i,j,expr=line.split(maxsplit=3);i=int(i);j=int(j);assert re.fullmatch(r'[0-9abcdyzx*^+\-]+',expr.strip()),'unsafe transformation syntax';assert tag=='T' and 1<=i<=ni and 1<=j<=ng
   assert (i,j) not in seen;seen.add((i,j));assert j>=last,'nonstreaming T order';last=j
   if j!=current:
    if current:
     h.write(f'q=q-({Gs[current-1]});if(q!=0){{print("FAIL_MEM {current}");errors++;}}\n');counts[(current-1)%workers]+=1
    current=j;h=writers[(j-1)%workers];h.write('q=0;\n')
   h.write(f'q=q+I[{i}]*({expr.strip()});\n')
  if current:h.write(f'q=q-({Gs[current-1]});if(q!=0){{print("FAIL_MEM {current}");errors++;}}\n');counts[(current-1)%workers]+=1
  assert sum(counts)==ng,'zero/missing T column'
  for b,h in enumerate(writers):h.write(f'if(errors==0){{print("ACCEPT_MEM {counts[b]}");}}else{{print("REJECT_MEM");}}quit;\n');h.close()
 if corrupt:return {'n':n,'ng':ng,'membership_counts':counts}
 # Every unordered pair occurs exactly once. A chain may only cite earlier
 # accepted pairs, so this is a finite acyclic proof, not a circular skip.
 status=bytearray(ng*ng);direct=[];counts2={'D':0,'C':0,'P':0}
 def ix(i,j):return max(i,j)*ng+min(i,j)
 with plan.open() as f:
  assert f.readline().split()==['CFG_PAIRS_V1',str(ng)]
  for line in f:
   a=line.split();i,j=int(a[0])-1,int(a[1])-1;flag=a[2];assert 0<=i<j<ng and not status[ix(i,j)],'pair duplicate/range'
   u,v=L[i][0],L[j][0];m=lcm(u,v)
   if flag=='P':assert len(a)==3 and all(not(x and y) for x,y in zip(u,v)),'invalid product'
   elif flag=='C':
    assert len(a)==4;k=int(a[3])-1;assert 0<=k<ng and k not in (i,j)
    assert div(L[k][0],m) and status[ix(i,k)] and status[ix(j,k)],'invalid chain dependency'
   else:assert flag=='D' and len(a)==3;direct.append((i,j,m))
   status[ix(i,j)]=1;counts2[flag]+=1
 assert sum(counts2.values())==ng*(ng-1)//2,'pair cover gap'
 for j in range(ng):assert all(status[j*ng+i] for i in range(j)),'pair cover gap'
 base+= 'ideal G;\n'+''.join(f'G[{j+1}]={s};\n' for j,s in enumerate(Gs))+'attrib(G,"isSB",1);\npoly s;int errors=0;\n'
 writers=[(dest/f'pairs-{b}.sing').open('w') for b in range(workers)];paircounts=[0]*workers
 for h in writers:h.write(base)
 for i in range(ni):writers[i%workers].write(f'if(reduce(I[{i+1}],G)!=0){{print("FAIL_INPUT {i+1}");errors++;}}\n')
 for k,(i,j,m) in enumerate(direct):
  a=tuple(x-y for x,y in zip(m,L[i][0]));b=tuple(x-y for x,y in zip(m,L[j][0]));h=writers[k%workers];paircounts[k%workers]+=1
  h.write(f's={pow(L[i][1],-1,p)}*({monomial(a,names)})*G[{i+1}]-{pow(L[j][1],-1,p)}*({monomial(b,names)})*G[{j+1}];if(reduce(s,G)!=0){{print("FAIL_PAIR {i+1} {j+1}");errors++;}}\n')
 for k,h in enumerate(writers):h.write(f'if(errors==0){{print("ACCEPT_PAIR {paircounts[k]}");}}else{{print("REJECT_PAIR");}}quit;\n');h.close()
 return {'n':n,'ng':ng,'membership_counts':counts,'pair_counts':paircounts,'pairs':counts2,'inputs_reduced':ni,'initial_matches':True,'pair_cover_accepted':True,'positive_weights':w,'pure_power_bounds':pure_bounds,'leading_terms_recomputed':True}

def execute(dest,phase,counts,workers):
 def one(b):
  log=dest/f'{phase}-{b}.log'
  with log.open('w') as f:rc=subprocess.call(['/usr/bin/time','-v','-o',str(dest/f'{phase}-{b}.time'),'Singular','-q',str(dest/f'{phase}-{b}.sing')],stdout=f,stderr=subprocess.STDOUT)
  s=log.read_text();want=f'ACCEPT_{"MEM" if phase=="member" else "PAIR"} {counts[b]}'
  assert rc==0 and want in s and '?' not in s and 'FAIL_' not in s and 'REJECT_' not in s,(phase,b,'arithmetic rejection/setup failure; see receipt')
 with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:list(pool.map(one,range(workers)))

if __name__=='__main__':
 cert=pathlib.Path(sys.argv[1]).resolve();plan=pathlib.Path(sys.argv[2]).resolve();dest=pathlib.Path(sys.argv[3]).resolve();workers=int(sys.argv[4]);corrupt=len(sys.argv)>5
 start=time.monotonic();r=prepare(cert,plan,dest,workers,corrupt);r['prepare_wall_seconds']=time.monotonic()-start;print('PREPARED',r,flush=True)
 t=time.monotonic();execute(dest,'member',r['membership_counts'],workers);r['membership_wall_seconds']=time.monotonic()-t
 if not corrupt:
  t=time.monotonic();execute(dest,'pairs',r['pair_counts'],workers);r['spair_wall_seconds']=time.monotonic()-t
 r.update(accepted=True,unresolved=0,whole_wall_seconds=time.monotonic()-start,cpu_seconds=time.process_time()+resource.getrusage(resource.RUSAGE_CHILDREN).ru_utime+resource.getrusage(resource.RUSAGE_CHILDREN).ru_stime)
 (dest/'receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r),flush=True)
