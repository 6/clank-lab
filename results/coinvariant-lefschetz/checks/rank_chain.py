#!/usr/bin/env python3
"""Rank table checker A: complete start cover plus chain interval arithmetic.
No polynomial search or other rank-checker implementation is imported.
"""
import pathlib,sys,json,ast,collections,time

def read(p):return [tuple(ast.literal_eval(x.replace('{','(').replace('}',')'))) for x in p.read_text().splitlines() if x.strip()]
def divide(a,b):return all(x<=y for x,y in zip(a,b))
def series(ws,ds):
 h=[1]+[0]*(sum(ds)-sum(ws))
 for w in ws:
  for j in range(w,len(h)):h[j]+=h[j-w]
 for d in ds:
  for j in range(len(h)-1,d-1,-1):h[j]-=h[j-d]
 return h
def convolution(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return c

def verify(unit,table=None):
 n=6 if unit.name=='target' else 5
 # Mutation sandboxes preserve the kind in an explicit frozen table/spec.
 order=(unit/'unit-order.txt').read_text().split();n=int(order[2]);p=int(order[1]);ws=list(map(int,order[4+n:]));assert len(ws)==n and all(w>0 for w in ws)
 assert (p,n,ws) in [(1009,6,[3,4,6,9,1,1]),(73,5,[1]*5)]
 target=n==6;ds=[6,12,18,24,30,42] if target else [4,6,10,12,18];hilb=series(ws,ds);K=81 if target else 45
 gs=read(unit/'unit-initial.txt');starts=read(unit/'unit-starts.txt')
 for j in range(n):assert any(g[j]>0 and sum(g[k] for k in range(n) if k!=j)==0 for g in gs),'missing pure power'
 zero=(0,)*n;seen={zero};todo=[zero]
 for e in todo:
  for j in range(n-1):
   v=list(e);v[j]+=1;v=tuple(v)
   if v not in seen and not any(divide(g,v) for g in gs):seen.add(v);todo.append(v)
 assert len(starts)==len(set(starts)) and set(starts)==seen,'dropped start generator/cover gap'
 chains=[];whole=[0]*len(hilb)
 for e in starts:
  assert e[-1]==0;length=min(g[-1] for g in gs if divide(g[:-1],e[:-1]));d=sum(a*b for a,b in zip(e,ws));assert length>0 and d+length<=len(hilb)
  chains.append((d,length))
  for j in range(length):whole[d+j]+=1
 assert whole==hilb,'whole Hilbert mismatch'
 A=series([1,4,10],[24,30,42]) if target else hilb;B=series([1,3,4,6,9],[4,6,10,12,18]) if target else [1]
 rows=[]
 for k in range(1,K+1):
  h=[0]*len(hilb)
  for d,length in chains:
   for j in range(min(k,length)):h[d+j]+=1
  lower=[max(0,a-(A[j-k] if j>=k else 0)) for j,a in enumerate(A)]
  assert h==convolution(lower,B),('quotient mismatch',k)
  rows.append({'k':k,'hilbert':h})
 expected={'format':'CFG_RANK_V1','prime':p,'weights':ws,'k_min':1,'k_max':K,'convention':'last_exponent_strictly_less_than_k','rows':rows}
 if table is not None:assert table==expected,'rank-table mismatch (including z-power off-by-one)'
 return expected
if __name__=='__main__':
 st=time.monotonic();unit=pathlib.Path(sys.argv[1]);path=pathlib.Path(sys.argv[2]);write=len(sys.argv)>3 and sys.argv[3]=='--write';table=None if write else json.loads(path.read_text());r=verify(unit,table)
 if write:path.write_text(json.dumps(r,indent=2)+'\n')
 print(json.dumps({'accepted':True,'method':'chain intervals','quotients':len(r['rows']),'wall_seconds':time.monotonic()-st}))
