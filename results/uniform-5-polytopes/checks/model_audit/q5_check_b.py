"""Independent exact R2 checker B, using SymPy's number field Q(sqrt 5).

No generator, checker A, or q5_math arithmetic is imported. Affine ranks
are checked by Gram determinants; polygon order is checked by intrinsic
Gram coordinates rather than coordinate projections.
"""
import argparse
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import permutations
import json
from pathlib import Path
import sys
from sympy import QQ,Rational,sqrt
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'check_u3'))
import tcert
K=QQ.algebraic_field(sqrt(5));zero=K.zero;one=K.one


def insist(x,msg):
    if not x:raise ArithmeticError(msg)


def scalar(pair):
    return _scalar(tuple(pair))


@lru_cache(None)
def _scalar(pair):
    a,b=map(Fraction,pair)
    return K.from_sympy(Rational(a.numerator,a.denominator)+Rational(b.numerator,b.denominator)*sqrt(5))


def sg(x):
    rep=list(x.to_list())
    if not rep:return 0
    a=rep[-1];b=rep[0] if len(rep)==2 else 0
    if b==0:return (a>0)-(a<0)
    if a==0 or (a>0)==(b>0):return (b>0)-(b<0)
    v=a*a-5*b*b
    return ((a>0)-(a<0))*((v>0)-(v<0))


def dp(a,b):return sum((x*y for x,y in zip(a,b)),zero)
def minus(a,b):return [x-y for x,y in zip(a,b)]
def det(M):
    ans=zero
    for p in permutations(range(len(M))):
        term=one
        for i,j in enumerate(p):term*=M[i][j]
        if sum(p[i]>p[j] for i in range(len(p)) for j in range(i+1,len(p)))%2:ans-=term
        else:ans+=term
    return ans


def independent(points,dim):
    insist(len(points)==dim+1,'wrong frame length')
    rows=[minus(v,points[0]) for v in points[1:]]
    insist(sg(det([[dp(a,b) for b in rows] for a in rows]))>0,'dependent affine frame')


def permutations_transitive(gens,D):
    n=len(D)
    for g in gens:
        insist(len(g)==n and set(g)==set(range(n)),'nonbijection')
        for i in range(n):
            insist(all(D[i][j]==D[g[i]][g[j]] for j in range(i)),'distance not preserved')
    orbit={0}
    while True:
        more={g[i] for g in gens for i in orbit}
        if more<=orbit:break
        orbit|=more
    insist(len(orbit)==n,'nontransitive generators')


def plane(data,V,parent,dim):
    S=data['vertices'];frame=data['frame']
    insist(len(S)==len(set(S)) and set(S)<set(parent),'not a proper distinct face')
    insist(set(frame)<=set(S) and len(frame)==len(set(frame)),'invalid frame indices')
    independent([V[i] for i in frame],dim)
    n=list(map(scalar,data['normal']));h=scalar(data['offset'])
    insist(len(n)==4 and any(n),'zero plane')
    inside=set(S)
    for i in parent:
        val=sg(dp(n,V[i])-h)
        insist(val==0 if i in inside else val<0,'inexact or nonsupporting plane')
    return S


def polygon_cycle(P,V,D,frame):
    a,b,c=[V[i] for i in frame]
    e=minus(b,a);f=minus(c,a)
    for i,j in zip(P,P[1:]+P[:1]):
        insist(D[i][j]==one,'nonunit polygon edge')
        u=minus(V[j],V[i]);signs=[]
        for k in P:
            if k in (i,j):continue
            w=minus(V[k],V[i])
            signs.append(sg(dp(u,e)*dp(w,f)-dp(u,f)*dp(w,e)))
        insist(all(s>0 for s in signs) or all(s<0 for s in signs),'polygon is not convexly ordered')


def index_enclosures(name,E,indices):
    import geom
    from mpmath import iv,mp
    raw=geom.cell600();got=geom.polytope4(name);all_exact=tcert.cell600_exact()
    insist(indices==[all_exact.index(e) for e in E],'incorrect exact indices')
    insist(len(got)==len(E) and all(got[i] is raw[k] for i,k in enumerate(indices)),'independent model index disagreement')
    old_iv,old_mp=iv.prec,mp.prec
    try:
        iv.prec=mp.prec=320
        for a,b in zip(E,got):
            for (r,s),ball in zip(a,b):
                ref=iv.mpf(r.numerator)/r.denominator+iv.mpf(s.numerator)/s.denominator*iv.sqrt(5)
                insist(ball.a<=ref.a and ball.b>=ref.b,'reference coordinate not contained')
    finally:iv.prec,mp.prec=old_iv,old_mp


@lru_cache(None)
def model_geometry(name):
    E=tcert.sadi_exact() if name=='sadi' else tcert.gap_exact() if name=='gap' else None
    insist(E is not None,'unknown exceptional model')
    E=tuple(tuple(v) for v in E)
    V=tuple(tuple(scalar(c) for c in v) for v in E)
    D=tuple(tuple(dp(minus(v,w),minus(v,w)) for w in V) for v in V)
    return E,V,D


def check_model(model,enclosures=True):
    name=model['name'];E,V,D=model_geometry(name);n=len(V)
    independent([V[i] for i in model['frame']],4)
    radius=dp(V[0],V[0]);insist(sg(radius)>0 and all(dp(v,v)==radius for v in V),'unequal radii')
    insist(all(sg(D[i][j]-one)>=0 for i in range(n) for j in range(i)),'subunit/repeated points')
    permutations_transitive(model['symmetries'],D)
    if enclosures:index_enclosures(name,E,model['vertices_600'])
    cellsets=[];all_ridges=[];all_edges=set();types=Counter()
    for cell in model['cells']:
        C=plane(cell,V,range(n),3)
        permutations_transitive(cell['symmetries'],[[D[i][j] for j in C] for i in C])
        faces=[];edges=[];conf={v:[] for v in C}
        for poly in cell['polygons']:
            P=plane(poly,V,C,2);polygon_cycle(P,V,D,poly['frame'])
            faces.append(frozenset(P));all_ridges.append(frozenset(P))
            for i,j in zip(P,P[1:]+P[:1]):edges.append(frozenset((i,j)));all_edges.add(frozenset((i,j)))
            for i in P:conf[i].append(len(P))
        insist(faces and len(faces)==len(set(faces)),'missing/repeated cell polygons')
        insist(all(k==2 for k in Counter(edges).values()),'open cell boundary')
        expected={'tet':[3,3,3],'ico':[3,3,3,3,3],'A5':[3,3,3,5]}.get(cell['label'])
        insist(expected is not None and all(sorted(c)==expected for c in conf.values()),'wrong uniform cell label')
        types[cell['label']]+=1;cellsets.append(frozenset(C))
    insist(cellsets and len(cellsets)==len(set(cellsets)),'missing/repeated cells')
    insist(all(k==2 for k in Counter(all_ridges).values()),'open four-dimensional boundary')
    return dict(name=name,vertices=n,cells=len(cellsets),ridges=len(set(all_ridges)),edges=len(all_edges),cell_types=dict(types))


def check_certificate(data):
    insist(data['schema']==1,'schema')
    insist(data['claim']=='R2 exceptional convex hulls are uniform with unit edges; exact independent model indices','claim')
    names=[m['name'] for m in data['models']]
    insist(len(names)==2 and set(names)=={'sadi','gap'},'required model inventory: exactly one sadi and one gap')
    return [check_model(m) for m in data['models']]


def main():
    p=argparse.ArgumentParser();p.add_argument('certificate',type=Path);a=p.parse_args()
    for result in check_certificate(json.loads(a.certificate.read_text())):
        print(json.dumps(result,sort_keys=True))

if __name__=='__main__':main()
