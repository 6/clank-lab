#!/usr/bin/env python3
import ast,pathlib,sys,json
ROOT=pathlib.Path(__file__).resolve().parents[1]
OUT=pathlib.Path(sys.argv[1]).resolve()

def export():
 return r'''
short=0;
link ff="certificate.txt";
write(ff,"CFG_POLY_V1");
write(ff,string(char(basering))+" "+string(nvars(basering))+" "+string(size(I))+" "+string(size(G)));
for(int i=1;i<=size(I);i++){write(ff,"I "+string(i)+" "+string(I[i]));}
int ng=0;int nt=0;int mt=0;int nz=0;
for(int j=1;j<=size(G);j++){ng=ng+size(G[j]);write(ff,"G "+string(j)+" "+string(G[j]));}
for(i=1;i<=nrows(T);i++){for(j=1;j<=ncols(T);j++){if(T[i,j]!=0){nz++;nt=nt+size(T[i,j]);if(size(T[i,j])>mt){mt=size(T[i,j]);}}}}
print("SIZES G="+string(size(G))+" Gterms="+string(ng)+" Tnonzero="+string(nz)+" Tterms="+string(nt)+" Tmax="+string(mt));
for(j=1;j<=ncols(T);j++){for(i=1;i<=nrows(T);i++){if(T[i,j]!=0){write(ff,"T "+string(i)+" "+string(j)+" "+string(T[i,j]));}}}
close(ff);
ideal J=lead(G);
link lf="unit-initial.txt";for(i=1;i<=size(J);i++){write(lf,string(leadexp(J[i])));}close(lf);
ideal B=kbase(std(J+ideal(var(nvars(basering)))));
link ls="unit-starts.txt";for(j=1;j<=size(B);j++){write(ls,string(leadexp(B[j])));}close(ls);
print("DONE_EXPORT");quit;
'''
def target():
 lines=['ring R=1009,(a,b,c,d,y,z),wp(3,4,6,9,1,1);','short=0;']
 for k in [6,12,18,24,30,42]:
  terms=[]
  for l in (ROOT/'data/inputs'/f'input-{k}.txt').read_text().splitlines():
   e,c=l.split(':');e=ast.literal_eval(e.replace('{','[').replace('}',']'))
   terms.append('*'.join([f'({c})']+[f'{v}^{a}' for v,a in zip('abcdyz',e) if a]))
  lines.append(f'poly f{k}='+ '+'.join(terms)+';')
 lines+=['ideal I=f6,f12,f18,f24,f30,f42;','matrix T; int st=rtimer; ideal G=liftstd(I,T); print("LIFTSTD_CPU "+string(rtimer-st));',export()]
 (OUT/'target/run.sing').write_text('\n'.join(lines))
if __name__ == '__main__':
 (OUT/'target').mkdir(parents=True, exist_ok=True)
 (OUT/'target/unit-order.txt').write_text('CFG_ORDER_V1\n1009 6\nweighted_degree_reverse_lex\na b c d y z\n3 4 6 9 1 1\n')
 target()
