#!/usr/bin/env python3
"""Independent finite cover checker. Python standard library; no production imports."""
import concurrent.futures
import argparse,collections,itertools,json,math,os,pathlib,subprocess,sys,time
ROOT=pathlib.Path(__file__).resolve().parent
SCRATCH=pathlib.Path(os.environ['DS243_COVER_WORK'])
KEEP=SCRATCH/'results'
THREADS=int(os.environ.get('COVER_THREADS','2'))
DATA=ROOT.parent/'data'
O=SCRATCH/'observations'
G=list(itertools.product(range(3),range(9),range(9)))
H=list(itertools.product(range(3),repeat=3))
idx=lambda p:81*p[0]+9*p[1]+p[2]
hidx=lambda p:9*p[0]+3*p[1]+p[2]
add=lambda p,q:((p[0]+q[0])%3,(p[1]+q[1])%9,(p[2]+q[2])%9)
scale=lambda n,p:((n*p[0])%3,(n*p[1])%9,(n*p[2])%9)
qidx=lambda p:9*p[0]+3*(p[1]%3)+p[2]%3
hp=[idx((x,3*y,3*z)) for x,y,z in H]
S0=24909666
sbits=lambda m:{i for i in range(27) if m>>i&1}
S={hp[i] for i in sbits(S0)}
class Reject(Exception):pass
def require(b,msg):
 if not b:raise Reject(msg)
def dump(name,obj):
 (KEEP/name).write_text(json.dumps(obj,sort_keys=True,indent=2)+'\n')
def aff(a,b,c,d,e,f,g,h,i,t0,t1,t2):
 return [idx(((a*x+b*y+c*z+t0)%3,(3*d*x+e*y+f*z+3*t1)%9,(3*g*x+h*y+i*z+3*t2)%9)) for x,y,z in G]
def legal(p,all_pairs=False):
 require(len(p)==243 and set(p)==set(range(243)),'full-G map is not bijective')
 t=G[p[0]];require(scale(61,t)==t,'translation is outside H')
 lin=[idx(add(G[y],scale(-1,t))) for y in p]
 # Every directed generator edge is checked. These generate the full Cayley graph,
 # hence this establishes additivity for every group pair, not a sample.
 bases=(81,9,1)
 for x in range(243):
  require(p[idx(scale(61,G[x]))]==idx(scale(61,G[p[x]])),'scalar commutation fails')
  for y in (range(243) if all_pairs else bases):
   require(lin[idx(add(G[x],G[y]))]==idx(add(G[lin[x]],G[lin[y]])),'linear additivity fails')
 return p
def orbit_partition():
 seen=set();orbs=[]
 for x in range(243):
  if x not in seen:
   cyc=[];y=x
   while y not in cyc:
    cyc.append(y);y=idx(scale(61,G[y]))
   require(y==x,'scalar orbit does not close');z=sorted(cyc);seen.update(z);orbs.append(z)
 require(seen==set(range(243)),'partition missing point')
 require({n for n in range(243) if idx(scale(61,G[n]))==n}==set(hp),'scalar fixed subgroup differs from H')
 require(all(scale(61**3,p)==p for p in G),'scalar order does not divide three')
 expected=sorted(orbs,key=lambda z:(-len(z),z[0]))
 lines=[list(map(int,z.split())) for z in (DATA/'p243.txt').read_text().splitlines() if z.strip()]
 require(lines[0]==[3,3,9,9] and lines[1][:2]==[121,60],'p243 group/parameters')
 actual=lines[2:]
 for row in actual:require(row[0]==len(row)-1,'p243 orbit shape')
 require([r[1:] for r in actual]==expected,'p243 scalar partition or canonical ordering differs')
 require(lines[1][2]==len(orbs),'p243 declared orbit count')
 return expected

def singleton_matrix(matrix):
 e,f,h,i=matrix
 full={};normal=set();stabilizers=[]
 permutations=[(a,t) for a in (1,2) for t in range(3)]
 xmaps={(a,t):legal(aff(a,0,0,0,1,0,0,0,1,t,0,0)) for a,t in permutations}
 for d,g,w1,w2 in itertools.product(range(3),repeat=4):
  params=(1,0,0,d,e,f,g,h,i,0,w1,w2)
  p=legal(aff(*params))
  hm=[hp.index(p[n]) for n in hp]
  im=sum(1<<hm[n] for n in sbits(S0));normal.add(im)
  if im==S0:stabilizers.append(params)
  for a,t in permutations:
   xp=xmaps[a,t];cp=[xp[n] for n in p]
   image=sum(1<<hp.index(cp[hp[n]]) for n in sbits(S0))
   if image not in full:
    inv=[0]*243
    for u,v in enumerate(cp):inv[v]=u
    require({inv[hp[n]] for n in sbits(image)}==S,'normalization does not send mask to S0')
    trans=G[inv[0]];cols=[add(G[inv[b]],scale(-1,trans)) for b in (81,9,1)]
    reconstructed=[idx(add(trans,add(scale(x,cols[0]),add(scale(y,cols[1]),scale(z,cols[2]))))) for x,y,z in G]
    require(reconstructed==inv,'inverse full-G affine witness differs')
    full[image]=[inv[0]]+[idx(c) for c in cols]
 return full,normal,stabilizers

def singleton():
 moments=[v for v in itertools.product(range(82),repeat=3) if sum(v)==121 and sum(x*x for x in v)==4921]
 require(set(moments)==set(itertools.permutations((36,40,45))),'index-three moment solutions')
 layers=[v for v in itertools.product(range(10),repeat=3) if sum(v)==13 and sum(x*x for x in v)%9==7 and sorted(x%3 for x in v)==[0,0,1]]
 raw=list(map(int,(KEEP/'passing-masks.txt').read_text().split()));passed=set(raw)
 require(raw==sorted(passed),'passing mask output duplicates/order')
 kr=json.loads((KEEP/'singleton-result.json').read_text())
 require(kr['tested']==sum(math.prod(math.comb(9,n) for n in v) for v in layers) and kr['passing']==len(passed) and kr['threads']==THREADS and kr['smoke'] is False,'full singleton execution receipt')
 require({tuple((m>>(9*k)&511).bit_count() for k in range(3)) for m in passed}==set(itertools.permutations((4,3,6))),'surviving layer orders differ')
 # Construct all H-affine maps through independently enumerated GL2(3),d,w.
 matrices=[v for v in itertools.product(range(3),repeat=4) if (v[0]*v[3]-v[1]*v[2])%3]
 full={};normal=set();stabilizers=[];legal_maps=len(matrices)*81
 with concurrent.futures.ProcessPoolExecutor(max_workers=THREADS) as pool:
  for ff,nn,ss in pool.map(singleton_matrix,matrices):
   full.update(ff);normal.update(nn);stabilizers.extend(ss)
 require(set(full)==passed,'singleton exhaustive/affine set mismatch missing='+str(sorted(passed-set(full))[:1])+' extra='+str(sorted(set(full)-passed)[:1]))
 normalized={m for m in passed if tuple((m>>(9*k)&511).bit_count() for k in range(3)) in [(4,0,9),(4,3,6)]}
 require(normal==normalized,'normalized singleton affine orbit not exactly admissible set')
 # Recompute all congruences for every retained mask from H addition, independent of C++ bit shifts.
 for m in passed:
  st=sbits(m)
  for hx,hy,hz in H[1:]:
   shifted={hidx(((x+hx)%3,(y+hy)%3,(z+hz)%3)) for n in st for x,y,z in [H[n]]}
   require(len(st&shifted)%3==0,'retained singleton violates a congruence')
 dump('normalization-witnesses.json',{'format':'mask: [translation, linear(e_x), linear(e_y), linear(e_z)]; inverse affine map sends mask to S0','witnesses':full})
 receipt=(DATA/'singletons.txt').read_text().splitlines()
 require(list(map(int,receipt[0].split()))==[S0,len(passed)],'singleton receipt representative/weight')
 fields=dict(x.split('=') for x in receipt[1].split())
 counts={'maps':legal_maps,'normalized':sum(math.comb(9,a)*math.comb(9,b)*math.comb(9,c) for a,b,c in [(4,0,9),(4,3,6)]),'congruence_pass':len(normal),'representatives':1,'covered':len(normal),'full_weight':len(passed)}
 require({k:int(v) for k,v in fields.items()}==counts,'singleton receipt counts differ from derivation')
 return {'moment_triples':moments,'layer_triples':layers,'tested':sum(math.prod(math.comb(9,n) for n in v) for v in layers),'passing':len(passed),'normalized':counts,'normalization_maps':len(matrices)*81*6},stabilizers

def quotients():
 forms=[v for v in H[1:] if next(x for x in v if x)!=2]
 values=[[sum(a*b for a,b in zip(l,q))%3 for q in H] for l in forms]
 require(len(forms)==13,'projective form enumeration')
 # Prove the actual finite incidence identity used for inversion.
 for p in range(27):
  for q in range(27):require(sum(v[p]==v[q] for v in values)==(13 if p==q else 4),'incidence multiplicity')
 images=set();special={0:4,9:3,18:6}
 for bits in range(1<<len(forms)):
  lines=[[40,36,45] if not bits>>j&1 else [40,45,36] for j in range(len(forms))]
  nums=[sum(lines[j][values[j][q]] for j in range(len(forms)))-4*121 for q in range(27)]
  if any(n%9 for n in nums):continue
  r=tuple(n//9 for n in nums)
  if any(not 0<=n<=9 or (q in special and n!=special[q]) or (q not in special and n%3) for q,n in enumerate(r)):continue
  require(sum(r)==121,'quotient total')
  for j,v in enumerate(values):require([sum(r[q] for q in range(27) if v[q]==n) for n in range(3)]==lines[j],'inverted line sums')
  for hx,hy,hz in H:
   corr=sum(r[q]*r[hidx(((x+hx)%3,(y+hy)%3,(z+hz)%3))] for q,(x,y,z) in enumerate(H))
   require(corr==(601 if (hx,hy,hz)==(0,0,0) else 540),'quotient difference equation')
  require(collections.Counter(r[q] for q in range(27) if q not in special)=={3:12,6:12},'derived cell values differ')
  images.add(r)
 actual=[tuple(map(int,l.split())) for l in (DATA/'images.txt').read_text().splitlines() if l.strip()]
 require(len(actual)==len(set(actual)) and set(actual)==images,'actual images omitted or duplicated a quotient')
 dump('derived-images.json',sorted(images))
 return images

def stabilizer_maps(stabilizers):
 maps=[]
 for p in stabilizers:
  for b,c in itertools.product(range(3),repeat=2):
   par=list(p);par[1]=b;par[2]=c
   f=legal(aff(*par),all_pairs=True)
   require({f[n] for n in S}==S,'full stabilizer fails to preserve S')
   qp=[]
   for q in range(27):
    cells={qidx(G[f[n]]) for n in range(243) if qidx(G[n])==q}
    require(len(cells)==1,'map does not induce quotient map');qp.append(cells.pop())
   require(set(qp)==set(range(27)),'induced Q not bijective')
   maps.append({'parameters':par,'full_G':f,'Q':qp})
 require(len({tuple(m['Q']) for m in maps})==len(maps),'duplicate quotient stabilizer')
 dump('stabilizer-maps.json',maps)
 return maps

def case_cover(cases,images,maps):
 def orbit(r):
  out=set()
  for m in maps:
   z=[None]*27
   for q,to in enumerate(m['Q']):z[to]=r[q]
   out.add(tuple(z))
  return out
 covered=set();witness=[]
 for weight,r in cases:
  require(r in images,'case is not an admissible quotient')
  ob=orbit(r);require(ob<=images,'stabilizer left admissible images')
  mw=[]
  for image in sorted(ob):
   choices=[]
   for j,m in enumerate(maps):
    z=[None]*27
    for q,to in enumerate(m['Q']):z[to]=r[q]
    if tuple(z)==image:choices.append(j)
   require(bool(choices),'missing actual full-G map witness')
   mw.append({'image':image,'full_G_map_index':choices[0]})
  witness.append({'representative':r,'weight':weight,'orbit':sorted(ob),'map_witnesses':mw})
  covered|=ob
 missing=images-covered
 require(not missing,'MISSING IMAGE ORBIT witness='+json.dumps(min(missing) if missing else None))
 require(sum(len(orbit(r)) for w,r in cases)==len(covered),'duplicate representative orbit')
 for w,r in cases:require(w==len(orbit(r)),'case weight does not equal actual orbit size')
 return witness

def options_for(cases,orbs):
 bycell=collections.defaultdict(list)
 for orb in orbs:
  if len(orb)==3:
   qs={qidx(G[n]) for n in orb};require(len(qs)==1,'scalar orbit spans cells');bycell[qs.pop()].append(orb)
 options=[];orders=[];families=[]
 for w,r in cases:
  order=sorted(bycell,key=lambda q:(-r[q],q));cs=[];fams=[]
  for q in order:
   cell={n for n in range(243) if qidx(G[n])==q};require(len(cell)==9,'cell size')
   need=r[q]
   # Enumerate ALL subsets of the nine actual points of required size. Testing
   # scalar closure, rather than choosing known orbit unions, is independent.
   fam={tuple(z) for z in itertools.combinations(sorted(cell),need) if {idx(scale(61,G[n])) for n in z}==set(z)}
   oo=bycell[q];require(len(oo)==3,'cell scalar orbit count')
   choices=[sorted(n for j,z in enumerate(oo) if j!=k for n in z) for k in range(3)] if need==6 else [sorted(z) for z in oo]
   require(set(map(tuple,choices))==fam and len(choices)==len(fam),'derived choices not bijection')
   cs.append(choices);fams.append(fam)
  require(len(order)==24,'nonspecial cells');options.append(cs);orders.append(order);families.append(fams)
 return options,orders,families

def check_options(actual,orders,families,cases):
 require(set(actual['initial_points'])==S and len(actual['initial_points'])==len(S),'initial singleton set')
 require(len(actual['options'])==len(cases),'case dimension')
 for cs,(rows,order,fams) in enumerate(zip(actual['options'],orders,families)):
  require(len(rows)==len(order),'cell dimension')
  seen=set()
  for slot,(opts,q,fam) in enumerate(zip(rows,order,fams)):
   require(len(opts)==3,'option dimension')
   for opt in opts:
    require(opt==sorted(set(opt)),'option not sorted distinct points')
    require(all(0<=n<243 and qidx(G[n])==q for n in opt),'option cell identity')
    require(len(opt)==cases[cs][1][q],'option required size')
    require({idx(scale(61,G[n])) for n in opt}==set(opt),'option not scalar invariant')
   supplied=set(map(tuple,opts));missing=fam-supplied
   require(not missing,'MISSING ACTUAL INVARIANT SUBSET case='+str(cs)+' slot='+str(slot)+' Q='+str(H[q])+' witness='+json.dumps(min(missing) if missing else None))
   require(len(supplied)==len(opts) and supplied==fam,'option labels not a bijection')
   require(q not in seen,'duplicated cell');seen.add(q)
  require(seen=={q for q in range(27) if q not in (0,9,18)},'omitted nonspecial cell')
 return True

def ranges_cover(cert,case_count):
 # Metadata can change. The universe is derived from actual case/tree geometry.
 universe=case_count*3**12;intervals=[]
 for r in cert['ranges']:
  a,b=r['first'],r['stop'];require(type(a)==int and type(b)==int and 0<=a<b<=universe,'interval bounds')
  intervals.append((a,b))
 end=0
 for a,b in sorted(intervals):
  if a>end:
   cs,n=divmod(end,3**12);digits=[]
   for power in range(11,-1,-1):digits.append(n//3**power%3)
   raise Reject('MISSING PREFIX witness ID='+str(end)+' case='+str(cs)+' digits='+json.dumps(digits))
  require(a==end,'overlapping intervals');end=b
 require(end==universe,'MISSING PREFIX witness ID='+str(end))
 require(cert['range_count']==len(intervals),'range_count metadata')
 require(cert['cases']==case_count and cert['depth']==12,'certificate geometry')
 sums={k:sum(r[k] for r in cert['ranges']) for k in ('nodes','valid','solutions')}
 require(cert['counts']==sums,'certificate counter metadata')
 # Compare pinned formula AFTER semantic coverage, never substitute it for coverage.
 require(all(r['range']==j and (r['first'],r['stop'])==(4096*j,min(4096*(j+1),universe)) for j,r in enumerate(cert['ranges'])),'declared range indexing')
 return {'intervals':len(intervals),'covered_ids':end,'counter_metadata_only':sums}

def main():
 global THREADS
 ap=argparse.ArgumentParser();ap.add_argument('--threads',type=int,default=THREADS);ap.add_argument('mode',choices=['baseline','gap-prefix','gap-option','gap-case']);args=ap.parse_args();THREADS=args.threads
 require(THREADS>=1,'--threads must be positive')
 KEEP.mkdir(parents=True,exist_ok=True)
 start=time.time();orbs=orbit_partition()
 cases=[(row[0],tuple(row[1:])) for l in (DATA/'cases.txt').read_text().splitlines() if (row:=list(map(int,l.split())))]
 cert=json.loads((DATA/'ranges.json').read_text())
 cert['counts']={k:sum(r[k] for r in cert['ranges']) for k in ('nodes','valid','solutions')}
 if args.mode=='baseline':
  singles,stab=singleton();print('singleton normalization complete',flush=True)
  images=quotients();maps=stabilizer_maps(stab);witness=case_cover(cases,images,maps);dump('case-orbits.json',witness)
  opts,orders,families=options_for(cases,orbs);dump('derived-options.json',{'schema':'independent-cover-options-v1','initial_points':sorted(S),'options':opts,'cell_order':orders})
  observations={}
  for mode in ('fast','direct'):
   actual=json.loads((O/(mode+'-options.json')).read_text());require(actual['schema']=='ds243-production-cover-export-v1' and actual['mode']==mode,'observation schema/mode')
   check_options(actual,orders,families,cases)
   require(actual['initial_points']==sorted(S) and actual['options']==opts,'actual option label/order differs from independent derived convention')
   observations[mode]={'actual_option_bijections':True,'exact_derived_order_match':True,'cells':sum(len(z) for z in actual['options'])}
  ranges=ranges_cover(cert,len(cases))
  # The complete prefix comparison is a separate C++ job using the requested threads; bind its success.
  text=(KEEP/'prefix-result.txt').read_text()
  require(text==''.join(mode+' records='+str(len(cases)*3**12)+' result=MATCH\n' for mode in ('fast','direct'))+'threads='+str(THREADS)+'\n','full actual decoder comparison incomplete')
  result={'status':'FINITE_COVER_CHECK_COMPLETE','seconds':time.time()-start,'threads':THREADS,'scalar_partition':dict(collections.Counter(map(len,orbs))),'singleton':singles,'quotient_sign_assignments':8192,'quotient_images':len(images),'stabilizer_full_maps':len(maps),'case_orbit_sizes':[len(w['orbit']) for w in witness],'options':observations,'certificate':ranges,'prefixes_per_case':3**12,'leaves_per_case':3**24,'cylinder_leaves':3**12,'external_mathematical_dependency':'multiplier theorem; see checks/README.md'}
  dump('baseline-result.json',result);print(json.dumps(result,sort_keys=True))
 elif args.mode=='gap-prefix':
  # Preserve 1038 rows and total interval length: omit 4095, duplicate 8192.
  cert['ranges'][0]['stop']-=1;cert['ranges'][0]['valid']-=1
  cert['ranges'][1]['stop']+=1;cert['ranges'][1]['valid']+=1
  cert['range_count']=len(cert['ranges']);cert['counts']={k:sum(r[k] for r in cert['ranges']) for k in ('nodes','valid','solutions')}
  require(len(cert['ranges'])==1038 and sum(r['stop']-r['first'] for r in cert['ranges'])==8*3**12,'gap fixture must preserve row count and summed interval lengths')
  dump('gap-prefix-fixture.json',cert);ranges_cover(cert,len(cases))
 elif args.mode=='gap-option':
  opts,orders,families=options_for(cases,orbs)
  actual=json.loads((O/'fast-options.json').read_text());actual['options'][0][0][1]=list(actual['options'][0][0][0]);dump('gap-option-fixture.json',actual)
  check_options(actual,orders,families,cases)
 else:
  images={tuple(v) for v in json.loads((KEEP/'derived-images.json').read_text())};maps=json.loads((KEEP/'stabilizer-maps.json').read_text())
  cases[1]=cases[0];dump('gap-case-fixture.json',cases);case_cover(cases,images,maps)
if __name__=='__main__':
 try:main()
 except Reject as e:print('REJECT: '+str(e),file=sys.stderr);sys.exit(1)
