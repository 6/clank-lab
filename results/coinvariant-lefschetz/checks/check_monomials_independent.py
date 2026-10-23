#!/usr/bin/env python3
"""Second checker: enumerate every standard monomial by constrained DFS.

Does not import the first checker, a search program, or the exported starts.
The expected rank uses max(h[j]-h[j-k],0), not a chain decomposition.
"""
import argparse,ast,json,pathlib

def series(ws,ds):
    a=[1]+[0]*(sum(ds)-sum(ws))
    for v in ws:
        for i in range(v,len(a)):a[i]+=a[i-v]
    for v in ds:
        a=[a[i]-(a[i-v] if i>=v else 0) for i in range(len(a))]
    return a
def product(a,b):
    out=[0]*(len(a)+len(b)-1)
    for i in range(len(a)):
        for j in range(len(b)):out[i+j]+=a[i]*b[j]
    return out
def verify(path,kind):
    gs=[tuple(ast.literal_eval(l.replace('{','(').replace('}',')'))) for l in pathlib.Path(path).read_text().splitlines() if l.strip()]
    ws=[3,4,6,9,1,1] if kind=='target' else [1]*5
    ds=[6,12,18,24,30,42] if kind=='target' else [4,6,10,12,18]
    expected=series(ws,ds);n=len(ws);monomials=[]
    def visit(prefix,active):
        j=len(prefix)
        if j==n:
            assert not active
            monomials.append(prefix);return
        bounds=[g[j] for g in active if all(t==0 for t in g[j+1:])]
        assert bounds,'not a finite monomial ideal'
        for e in range(min(bounds)):
            visit(prefix+(e,),[g for g in active if g[j]<=e])
    visit((),gs)
    actual=[0]*len(expected)
    for m in monomials:
        d=sum(x*w for x,w in zip(m,ws));assert d<len(actual)
        actual[d]+=1
    assert actual==expected,'Hilbert mismatch'
    if kind=='target':
        h=series([1,4,10],[24,30,42]);b=series([1,3,4,6,9],[4,6,10,12,18]);checks=81
        for k in range(1,82):
            observed=[0]*len(expected)
            for m in monomials:
                if m[-1]<k:observed[sum(x*w for x,w in zip(m,ws))]+=1
            lower=[max(v-(h[j-k] if j>=k else 0),0) for j,v in enumerate(h)]
            assert observed==product(lower,b),('rank mismatch',k)
    else:
        checks=0
        for k in range(1,len(expected)):
            observed=[0]*len(expected)
            for m in monomials:
                if m[-1]<k:observed[sum(m)]+=1
            lower=[max(v-(expected[j-k] if j>=k else 0),0) for j,v in enumerate(expected)]
            assert observed==lower,('rank mismatch',k)
            checks+=1
    return {'kind':kind,'standard_monomials':len(monomials),'quotients_checked':checks,'unresolved':0,'accepted':True}
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('initial');p.add_argument('kind',choices=['target','neighbor']);p.add_argument('--out',type=pathlib.Path,required=True);a=p.parse_args();result=verify(a.initial,a.kind);a.out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
