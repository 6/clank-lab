#!/usr/bin/env python3
"""Adversarial certificate acceptance tests.
Retains receipts; all large mutated certificates/replay scripts are regenerated.
"""
import pathlib,sys,json,tempfile,os,subprocess,time,shutil,re,ast,copy
import check_second,rank_chain,rank_dfs
unit=pathlib.Path(sys.argv[1]).resolve();workers=int(sys.argv[2]);binary=os.environ.get('CFG_CHECK_BIN','/tmp/cfg-check');out=unit/'audit-suite';out.mkdir(exist_ok=True)
start=time.monotonic();records=[]

def cpp_reject(bad,name,reason):
 with (out/(name+'-cpp.log')).open('w') as f:rc=subprocess.call(['/usr/bin/time','-v','-o',str(out/(name+'-cpp.time')),binary,str(bad/'certificate.txt'),str(workers),str(bad/'cpp'),'membership-only'],stdout=f,stderr=subprocess.STDOUT)
 s=(out/(name+'-cpp.log')).read_text();assert rc==1 and reason in s,(name,'portable mutation not rejected for expected obligation',s[-400:]);return s.splitlines()[-1]
def second_reject(bad,name,reason,arithmetic=False):
 try:
  r=check_second.prepare(bad/'certificate.txt',unit/'check.pairs',bad/'second',workers,True)
  if arithmetic:check_second.execute(bad/'second','member',r['membership_counts'],workers)
 except AssertionError as e:
  text=str(e)
  if not arithmetic:assert reason in text,(name,'wrong independent rejection',text)
  else:
   logs=[p.read_text() for p in (bad/'second').glob('member-*.log')];
   for k,s in enumerate(logs):
    if 'FAIL_MEM' in s:(out/(name+f'-second-kernel-{k}.log')).write_text(s)
   assert any('FAIL_MEM' in s and 'REJECT_MEM' in s for s in logs),('expected arithmetic failure absent',name)
  (out/(name+'-second-rejection.txt')).write_text(text+'\n');return text
 else:raise AssertionError((name,'independent checker accepted corruption'))
def sandbox(base):
 for name in ['unit-order.txt','unit-initial.txt','unit-starts.txt']:os.link(unit/name,base/name)
def coeff_plus_one(expr):
 m=re.match(r'[+-]?\d+',expr)
 if m:return str(int(m[0])+1)+expr[m.end():]
 if expr.startswith('-'):return '-2*'+expr[1:]
 return '2*'+expr

with tempfile.TemporaryDirectory(prefix='cfg-certificate-adversarial-',dir=str(unit)) as tmp:
 base=pathlib.Path(tmp)
 # Keep the trusted package anchor when moving a certificate into a sandbox.
 # An altered I must be rejected as a frozen-input mismatch by BOTH parsers,
 # before the (also invalid) membership arithmetic is reached.
 with (unit/'certificate.txt').open() as f:
  assert f.readline().strip()=='CFG_POLY_V1';prime=int(f.readline().split()[0])
 if prime==1009:
  assert os.environ.get('CFG_INPUT_DIR'),'mutation harness lost trusted input binding'
  bad=base/'changed-input';bad.mkdir();sandbox(bad);changed=False
  with (unit/'certificate.txt').open() as f,(bad/'certificate.txt').open('w') as g:
   for line in f:
    if not changed and line.startswith('I 1 '):
     line='I 1 '+coeff_plus_one(line.split(maxsplit=2)[2].strip())+'\n';changed=True
    g.write(line)
  assert changed
  st=time.monotonic();a=cpp_reject(bad,'changed-input','frozen input mismatch');b=second_reject(bad,'changed-input','frozen input mismatch')
  records.append({'mutation':'one frozen input coefficient +1, trusted package unchanged','portable_rejected':a,'independent_rejected':b,'wall_seconds':time.monotonic()-st});shutil.rmtree(bad)
 # T mutation changes an actual coefficient, preserving degree/support.
 bad=base/'bad-T';bad.mkdir();sandbox(bad);changed=None
 with (unit/'certificate.txt').open() as f,(bad/'certificate.txt').open('w') as g:
  for line in f:
   if changed is None and line.startswith('T '):
    tag,i,j,expr=line.split(maxsplit=3);line=f'T {i} {j} '+coeff_plus_one(expr.strip())+'\n';changed=[int(i),int(j)]
   g.write(line)
 assert changed
 st=time.monotonic();a=cpp_reject(bad,'T-coefficient','coefficientwise I*T=G rejected');b=second_reject(bad,'T-coefficient','',True)
 records.append({'mutation':'one transformation-matrix coefficient +1','T_entry':changed,'portable_rejected':a,'independent_rejected':b,'wall_seconds':time.monotonic()-st});shutil.rmtree(bad)
 # Declared LT corruption does not change G or T.
 bad=base/'bad-LT';bad.mkdir();sandbox(bad);os.link(unit/'certificate.txt',bad/'certificate.txt');(bad/'unit-initial.txt').unlink()
 lines=(unit/'unit-initial.txt').read_text().splitlines();e=list(ast.literal_eval(lines[0].replace('{','[').replace('}',']')));e[0]+=1;lines[0]=','.join(map(str,e));(bad/'unit-initial.txt').write_text('\n'.join(lines)+'\n')
 st=time.monotonic();a=cpp_reject(bad,'declared-LT','declared LT differs');b=second_reject(bad,'declared-LT','certificate/initial mismatch');records.append({'mutation':'incorrect declared LT, polynomial unchanged','portable_rejected':a,'independent_rejected':b,'wall_seconds':time.monotonic()-st});shutil.rmtree(bad)
 # Drop the pure last-variable basis polynomial, renumbering the entire valid
 # matrix and basis. Membership of every retained column is still valid;
 # finite cover, not a malformed header, must reject the omission.
 bad=base/'dropped-generator';bad.mkdir();sandbox(bad);(bad/'unit-initial.txt').unlink();lines=(unit/'unit-initial.txt').read_text().splitlines();gs=rank_chain.read(unit/'unit-initial.txt');n=len(gs[0]);which=[i for i,e in enumerate(gs) if e[-1]>0 and not any(e[:-1])];assert len(which)==1;drop=which[0]+1
 (bad/'unit-initial.txt').write_text('\n'.join(s for i,s in enumerate(lines,1) if i!=drop)+'\n')
 with (unit/'certificate.txt').open() as f,(bad/'certificate.txt').open('w') as g:
  for k,line in enumerate(f):
   if k==1:
    p0,n0,ni,ng=map(int,line.split());line=f'{p0} {n0} {ni} {ng-1}\n'
   elif line.startswith('G '):
    tag,i,expr=line.split(maxsplit=2);i=int(i)
    if i==drop:continue
    line=f'G {i-(i>drop)} {expr}'
   elif line.startswith('T '):
    tag,i,j,expr=line.split(maxsplit=3);j=int(j)
    if j==drop:continue
    line=f'T {i} {j-(j>drop)} {expr}'
   g.write(line)
 st=time.monotonic();a=cpp_reject(bad,'dropped-generator','missing pure power');b=second_reject(bad,'dropped-generator','missing pure power');records.append({'mutation':'drop pure last-variable G generator and matching T column, renumber consistently','dropped_index':drop,'portable_rejected':a,'independent_rejected':b,'wall_seconds':time.monotonic()-st});shutil.rmtree(bad)
 # Declared positive weights are an explicit acceptance obligation.
 bad=base/'bad-weight';bad.mkdir();sandbox(bad);os.link(unit/'certificate.txt',bad/'certificate.txt');(bad/'unit-order.txt').unlink();tok=(unit/'unit-order.txt').read_text().split();n=int(tok[2]);tok[4+n]='0';(bad/'unit-order.txt').write_text('\n'.join(tok)+'\n')
 st=time.monotonic();a=cpp_reject(bad,'zero-weight','nonpositive or incorrect declared weight');b=second_reject(bad,'zero-weight','nonpositive or incorrect declared weights');records.append({'mutation':'zero declared weight','portable_rejected':a,'independent_rejected':b,'wall_seconds':time.monotonic()-st});shutil.rmtree(bad)
# Rank table explicitly declares the strict exponent bound e_last<k. Planted
# k+1 data at k=1 are rejected by chain intervals and by full DFS separately.
rank=json.loads((unit/'rank-table.json').read_text());rank_chain.verify(unit,rank);rank_dfs.verify(unit,rank)
bad=copy.deepcopy(rank);bad['rows'][0]['hilbert']=bad['rows'][1]['hilbert'][:]
rejections={}
for name,check in [('chain_intervals',rank_chain.verify),('standard_monomial_DFS',rank_dfs.verify)]:
 try:check(unit,bad)
 except AssertionError as e:rejections[name]=str(e)
 else:raise AssertionError(('z-power off-by-one accepted',name))
(out/'corrupt-z-power.json').write_text(json.dumps(bad,indent=2)+'\n');records.append({'mutation':'row k=1 replaced by quotient data for k=2 (z-power off-by-one)','independent_rejections':rejections})
result={'accepted_baseline':True,'all_requested_mutations_rejected':True,'mutations':records,'wall_seconds':time.monotonic()-start,'retention':'large corrupted certificates and arithmetic batches are regenerated; logs/parsed receipts retained'}
(out/'receipt.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
