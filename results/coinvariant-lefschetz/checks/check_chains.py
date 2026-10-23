#!/usr/bin/env python3
"""Check exported weighted monomial chains, independently of the CAS search.

This checks the monomial certificate ONLY, not ideal equality or Buchberger.
"""
import argparse,ast,collections,json,pathlib

def read(p):
    return [tuple(ast.literal_eval(l.replace('{','[').replace('}',']'))) for l in pathlib.Path(p).read_text().splitlines() if l.strip()]
def div(a,b):return all(x<=y for x,y in zip(a,b))
def mul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    return c
def hilb(weights,degrees):
    D=sum(degrees)-sum(weights);a=[0]*(D+1);a[0]=1
    for w in weights:
        for i in range(w,D+1):a[i]+=a[i-w]
    for d in degrees:
        for i in range(D,d-1,-1):a[i]-=a[i-d]
    return a
def run(prefix,kind):
    gs=read(str(prefix)+'-initial.txt');starts=read(str(prefix)+'-starts.txt')
    w=[3,4,6,9,1,1] if kind=='target' else [1]*5
    expected=hilb(w,[6,12,18,24,30,42] if kind=='target' else [4,6,10,12,18])
    # Reconstruct the complete set of start monomials by a breadth-first
    # traversal of the downward-closed standard set with last exponent zero.
    zero=(0,)*len(w);seen={zero};todo=[zero]
    for e in todo:
        for j in range(len(w)-1):
            v=list(e);v[j]+=1;v=tuple(v)
            if v not in seen and not any(div(g,v) for g in gs):seen.add(v);todo.append(v)
    assert len(starts)==len(set(starts)) and set(starts)==seen,'start cover'
    chains=[];actual=[0]*len(expected)
    for s in starts:
        assert s[-1]==0
        candidates=[g[-1] for g in gs if div(g[:-1],s[:-1])]
        assert candidates,'unbounded last variable'
        n=min(candidates);d=sum(a*b for a,b in zip(w,s));assert n>0
        assert d+n<=len(expected)
        chains.append((d,n))
        for j in range(n):actual[d+j]+=1
    assert actual==expected,'complete intersection Hilbert mismatch'
    if kind=='target':
        ha=hilb([1,4,10],[24,30,42])
        hb=hilb([1,3,4,6,9],[4,6,10,12,18])
        assert mul(ha,hb)==expected
        pred=[]
        for d in range((len(ha)+1)//2):
            pred += [(d,len(ha)-2*d)]*(ha[d]-(ha[d-1] if d else 0))
        failures=[];quotients=[]
        for k in range(1,82):
            obs=[0]*len(expected);base=[0]*len(ha)
            for d,n in chains:
                for j in range(min(k,n)):obs[d+j]+=1
            for d,n in pred:
                for j in range(min(k,n)):base[d+j]+=1
            want=mul(base,hb)[:len(expected)]
            if obs!=want:failures.append({'k':k,'first_degree':next(i for i,(a,b) in enumerate(zip(obs,want)) if a!=b),'observed_length':sum(obs),'expected_length':sum(want)})
            quotients.append({'k':k,'observed_length':sum(obs),'expected_length':sum(want)})
        return dict(kind=kind,dimension=sum(actual),gb_generators=len(gs),chain_count=len(chains),tested=81,failures=failures,unresolved=0,quotients=quotients,relative_hilbert=ha,fiber_hilbert=hb,chain_histogram=[list(k)+[v] for k,v in sorted(collections.Counter(chains).items())])
    failures=[(d,n) for d,n in chains if 2*d+n-1!=len(expected)-1]
    return dict(kind=kind,dimension=sum(actual),gb_generators=len(gs),chain_count=len(chains),tested=len(chains),failures=failures,unresolved=0,chain_histogram=[list(k)+[v] for k,v in sorted(collections.Counter(chains).items())])
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('prefix');p.add_argument('kind',choices=['target','neighbor']);p.add_argument('--out',required=True);a=p.parse_args()
    result=run(pathlib.Path(a.prefix),a.kind);pathlib.Path(a.out).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k not in ['quotients','relative_hilbert','fiber_hilbert','chain_histogram']}))
