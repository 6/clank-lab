#!/usr/bin/env python3
import pathlib,sys,time,json,tempfile,shutil,ast,resource,concurrent.futures
root=pathlib.Path(__file__).resolve().parent;sys.path.insert(0,str(root))
import check_chains,check_monomials_independent
unit=pathlib.Path(sys.argv[1]).resolve();kind=sys.argv[2];st=time.monotonic();cpu=time.process_time()
a=check_chains.run(unit/'unit',kind);assert not a['failures'] and not a['unresolved']
b=check_monomials_independent.verify(unit/'unit-initial.txt',kind);assert b['accepted'] and not b['unresolved']
corrupt={}
with tempfile.TemporaryDirectory() as tmp:
 p=pathlib.Path(tmp)/'bad';lines=(unit/'unit-initial.txt').read_text().splitlines();e=list(ast.literal_eval(lines[0].replace('{','[').replace('}',']')));j=next(i for i,v in enumerate(e) if v);e[j]-=1;lines[0]=','.join(map(str,e));pathlib.Path(str(p)+'-initial.txt').write_text('\n'.join(lines)+'\n');shutil.copyfile(unit/'unit-starts.txt',str(p)+'-starts.txt')
 for name,f in [('chain_cover',lambda:check_chains.run(p,kind)),('full_monomial_enumeration',lambda:check_monomials_independent.verify(str(p)+'-initial.txt',kind))]:
  try:r=f()
  except AssertionError:corrupt[name]='rejected'
  else:assert r.get('failures'),('initial corruption accepted',name);corrupt[name]='rejected by quotient mismatch'
(unit/'chains.json').write_text(json.dumps(a,indent=2)+'\n');(unit/'monomials.json').write_text(json.dumps(b,indent=2)+'\n')
r={'kind':kind,'dimension':a['dimension'],'chain_count':a['chain_count'],'quotients':b['quotients_checked'],'failures':0,'unresolved':0,'independent_accepted':True,'initial_corruption':corrupt,'cpu_seconds':time.process_time()-cpu,'wall_seconds':time.monotonic()-st};(unit/'quotient-receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
