"""Exact full-hull R2 checker A. No certificate generator is imported."""
from collections import Counter
from functools import lru_cache
from itertools import combinations
import argparse
import json
from pathlib import Path
from q5_math import *


def need(test,why):
    if not test:raise ArithmeticError(why)


def check_perms(perms,D):
    n=len(D);expected=list(range(n))
    for p in perms:
        need(sorted(p)==expected,'not a permutation')
        need(all(D[i][j]==D[p[i]][p[j]] for i in range(n) for j in range(i)),'not an exact metric symmetry')
    need(transitive(perms,n),'not vertex transitive')


def check_plane(E,data,parent,dim):
    S=data['vertices'];frame=data['frame'];n=list(map(decode,data['normal']));h=decode(data['offset'])
    need(len(S)==len(set(S)) and set(S)<=set(parent),'invalid vertex set')
    need(len(frame)==dim+1 and len(set(frame))==dim+1 and set(frame)<=set(S),'invalid affine frame')
    need(rank([vsub(E[i],E[frame[0]]) for i in frame[1:]])==dim,'affine frame rank')
    need(len(n)==4 and any(sign(x) for x in n),'zero functional')
    need(all(sign(sub(dot(n,E[i]),h))==0 for i in S),'not exactly on plane')
    need(all(sign(sub(dot(n,E[i]),h))<0 for i in parent if i not in S),'not strictly supporting')
    need(len(parent)>len(S),'face is not proper')
    return S


def cyclic(E,P):
    rows=[vsub(E[i],E[P[0]]) for i in P[1:]]
    cols=next((cc for cc in combinations(range(4),2) if rank([[r[j] for j in cc] for r in rows])==2),None)
    need(cols is not None,'polygon not planar rank two')
    for a,b in zip(P,P[1:]+P[:1]):
        u=vsub(E[b],E[a]); signs=[]
        for c in P:
            if c in (a,b):continue
            v=vsub(E[c],E[a]);x=sub(mul(u[cols[0]],v[cols[1]]),mul(u[cols[1]],v[cols[0]]))
            signs.append(sign(x))
        need(all(x>0 for x in signs) or all(x<0 for x in signs),'not convex cyclic order')


def check_enclosures(name,E,indices):
    """Exact model indices, followed by actual interval containment.

    geom.cell600's closed forms are the exact quadratic coordinates of
    tcert.cell600_exact, in the same signed/permutation order. The check
    uses containment of a tighter rigorous enclosure, never proximity.
    """
    import geom
    from mpmath import iv,mp
    raw=geom.cell600();actual=geom.polytope4(name);exact600=tcert.cell600_exact()
    need(indices==[exact600.index(e) for e in E],'exact 600-cell index projection')
    need(len(actual)==len(E),'geometry cardinality')
    need(all(actual[i] is raw[k] for i,k in enumerate(indices)),'geometry subset/index correspondence')
    saved_iv,saved_mp=iv.prec,mp.prec
    try:
        iv.prec=mp.prec=320
        for e,v in zip(E,actual):
            for x,y in zip(e,v):
                ref=tcert.qiv(x)
                need(y.a<=ref.a and ref.b<=y.b,'exact coordinate not contained in geometry enclosure')
    finally:
        iv.prec,mp.prec=saved_iv,saved_mp


@lru_cache(None)
def model_geometry(name):
    E=tuple(tuple(v) for v in vertices(name))
    return E,tuple(tuple(row) for row in distances(E))


def check_model(data,enclosures=True):
    name=data['name'];E,D=model_geometry(name);n=len(E)
    need(len(data['frame'])==5 and rank([vsub(E[i],E[data['frame'][0]]) for i in data['frame'][1:]])==4,'full dimension')
    r=dot(E[0],E[0]);need(sign(r)>0 and all(dot(v,v)==r for v in E),'sphere identity')
    need(all(sign(sub(D[i][j],O))>=0 for i in range(n) for j in range(i)),'subunit or repeated vertices')
    check_perms(data['symmetries'],distance_ids(D))
    if enclosures:check_enclosures(name,E,data['vertices_600'])
    facets=set();ridges=Counter();labels=Counter();edges=set()
    for C in data['cells']:
        S=check_plane(E,C,range(n),3);key=frozenset(S)
        need(key not in facets,'duplicate cell');facets.add(key)
        need(rank([vsub(E[i],E[S[0]]) for i in S[1:]])==3,'cell rank not three')
        check_perms(C['symmetries'],distance_ids([[D[i][j] for j in S] for i in S]))
        polys=set();boundary=Counter();configs={i:[] for i in S}
        for Pdata in C['polygons']:
            P=check_plane(E,Pdata,S,2);pk=frozenset(P)
            need(pk not in polys,'duplicate polygon');polys.add(pk);ridges[pk]+=1
            need(rank([vsub(E[i],E[P[0]]) for i in P[1:]])==2,'polygon rank not two')
            cyclic(E,P)
            for a,b in zip(P,P[1:]+P[:1]):
                need(D[a][b]==O,'edge not exactly unit')
                boundary[frozenset((a,b))]+=1;edges.add(frozenset((a,b)))
            for i in P:configs[i].append(len(P))
        need(polys and all(k==2 for k in boundary.values()),'cell face closure')
        expected={'tet':(3,3,3),'ico':(3,3,3,3,3),'A5':(3,3,3,5)}.get(C['label'])
        need(expected is not None and all(tuple(sorted(c))==expected for c in configs.values()),'uniform cell label')
        labels[C['label']]+=1
    need(facets and all(k==2 for k in ridges.values()),'full hull facet closure')
    return dict(name=name,vertices=n,cells=len(facets),ridges=len(ridges),edges=len(edges),cell_types=dict(labels))


def check_certificate(cert):
    need(cert['schema']==1,'schema')
    need(cert['claim']=='R2 exceptional convex hulls are uniform with unit edges; exact independent model indices','claim')
    names=[m['name'] for m in cert['models']]
    need(len(names)==2 and set(names)=={'sadi','gap'},'required model inventory: exactly one sadi and one gap')
    return [check_model(m) for m in cert['models']]


def main():
    p=argparse.ArgumentParser();p.add_argument('certificate',type=Path);a=p.parse_args()
    for result in check_certificate(json.loads(a.certificate.read_text())):
        print(json.dumps(result,sort_keys=True))

if __name__=='__main__':main()
