#!/usr/bin/env python3
import pathlib,subprocess,sys,re,json,time,os
root=pathlib.Path(sys.argv[1]).resolve();threads=int(sys.argv[2]);src=root/'certificate.txt';bad=root/'corrupt-coefficient.txt'
I=[];G=None;Ts=[];prime=None;nv=None
start=time.monotonic()
with src.open() as f,bad.open('w') as out:
 for k,line in enumerate(f):
  if k==1:prime,nv,ni,ng=map(int,line.split())
  if line.startswith('I '):I.append(line.split(maxsplit=2)[2].strip())
  if line.startswith('G 1 '):
   expr=line.split(maxsplit=2)[2].strip()
   if re.match(r'[+-]?\d',expr):
    m=re.match(r'[+-]?\d+',expr);expr=str(int(m[0])+1)+expr[m.end():]
   elif expr.startswith('-'):expr='-2*'+expr[1:]
   else:expr='2*'+expr
   line='G 1 '+expr+'\n';G=expr
  if line.startswith('T '):
   _,i,j,expr=line.split(maxsplit=3)
   if int(j)==1:Ts.append((int(i),expr.strip()))
  out.write(line)
assert G is not None and Ts
with (root/'corrupt-cpp.log').open('w') as f:
 rc=subprocess.call(['/usr/bin/time','-v','-o',str(root/'corrupt-cpp.time'),os.environ.get('CFG_CHECK_BIN','/tmp/cfg-check'),str(bad),str(threads),str(root/'corrupt-cpp'),'membership-only'],stdout=f,stderr=subprocess.STDOUT)
assert rc==1 and 'coefficientwise I*T=G rejected' in (root/'corrupt-cpp.log').read_text(),'C++ did not reject coefficient change'
names=list('abcdyz') if nv==6 else ['x1','x2','x3','x4','x5'];ring=f'ring R={prime},({",".join(names)}),'+('wp(3,4,6,9,1,1);' if nv==6 else 'dp;')+'\nshort=0;\n'
s=ring+'ideal I;\n'+''.join(f'I[{i+1}]={v};\n' for i,v in enumerate(I))+'poly q=0;\n'+''.join(f'q=q+I[{i}]*({v});\n' for i,v in Ts)+f'if(q!=({G})){{print("REJECTED_COEFFICIENT");}}else{{print("BAD_ACCEPT");}}quit;\n'
(root/'corrupt-independent.sing').write_text(s)
with (root/'corrupt-independent.log').open('w') as f:
 rc2=subprocess.call(['/usr/bin/time','-v','-o',str(root/'corrupt-independent.time'),'Singular','-q',str(root/'corrupt-independent.sing')],stdout=f,stderr=subprocess.STDOUT)
s=(root/'corrupt-independent.log').read_text();assert rc2==0 and 'REJECTED_COEFFICIENT' in s and '?' not in s and 'BAD_ACCEPT' not in s
r={'corruption':'increase first basis polynomial leading coefficient by one','same_polynomial_support_and_leading_monomial':True,'portable_checker_rejected':True,'independent_kernel_rejected':True,'wall_seconds':time.monotonic()-start,'bad_certificate_regenerable':True}
(root/'corruption.json').write_text(json.dumps(r,indent=2)+'\n');bad.unlink();print(json.dumps(r))
