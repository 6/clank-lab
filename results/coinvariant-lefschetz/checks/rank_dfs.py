#!/usr/bin/env python3
"""Rank table checker B: enumerate every standard monomial, count e_last<k.
Independent parser, traversal and Hilbert recurrence; no other checker import.
"""
import json,pathlib,sys,time,ast

def verify(unit,table):
 tok=(unit/'unit-order.txt').read_text().split();prime,n=int(tok[1]),int(tok[2]);ws=[int(x) for x in tok[4+n:]];assert tok[0]=='CFG_ORDER_V1' and tok[3]=='weighted_degree_reverse_lex'
 assert len(ws)==n and min(ws)>0
 if prime==1009:assert n==6 and ws==[3,4,6,9,1,1];degrees=[6,12,18,24,30,42];limit=81
 else:assert prime==73 and n==5 and ws==[1,1,1,1,1];degrees=[4,6,10,12,18];limit=45
 G=[]
 for line in (unit/'unit-initial.txt').read_text().splitlines():
  if not line.strip():continue
  g=ast.literal_eval(line.replace('{','[').replace('}',']'));assert len(g)==n and all(isinstance(e,int) and e>=0 for e in g);G.append(list(g))
 for i in range(n):assert any(g[i] and all(g[j]==0 for j in range(n) if i!=j) for g in G),'nonfinite pure-power cover'
 def hilbert(weights,rels):
  end=sum(rels)-sum(weights);h=[1]+[0]*end
  for w in weights:
   for j in range(w,end+1):h[j]+=h[j-w]
  for d in rels:h=[a-(h[j-d] if j>=d else 0) for j,a in enumerate(h)]
  return h
 expected=hilbert(ws,degrees);counts=[[0]*len(expected) for _ in range(limit)];whole=[0]*len(expected);monos=0
 def visit(prefix,active):
  nonlocal monos
  axis=len(prefix)
  if axis==n:
   assert not active;monos+=1;degree=sum(v*w for v,w in zip(prefix,ws));assert degree<len(expected);whole[degree]+=1
   for k in range(prefix[-1]+1,limit+1):counts[k-1][degree]+=1
   return
  bounds=[g[axis] for g in active if not any(g[axis+1:])];assert bounds,'unbounded monomial branch'
  for e in range(min(bounds)):visit(prefix+[e],[g for g in active if g[axis]<=e])
 visit([],G);assert whole==expected,'full Hilbert mismatch'
 assert set(table)=={'format','prime','weights','k_min','k_max','convention','rows'} and table['format']=='CFG_RANK_V1'
 assert table['prime']==prime and table['weights']==ws and table['k_min']==1 and table['k_max']==limit and table['convention']=='last_exponent_strictly_less_than_k'
 rows=table['rows'];assert len(rows)==limit
 for i,row in enumerate(rows):assert set(row)=={'k','hilbert'} and row['k']==i+1 and row['hilbert']==counts[i],('rank-table z-power mismatch',i+1)
 return {'accepted':True,'method':'all standard monomials','monomials':monos,'quotients':limit}
if __name__=='__main__':
 st=time.monotonic();r=verify(pathlib.Path(sys.argv[1]),json.loads(pathlib.Path(sys.argv[2]).read_text()));r['wall_seconds']=time.monotonic()-st;print(json.dumps(r))
