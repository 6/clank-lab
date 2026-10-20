"""Small independent R=1 probe using ONLY the three paper DEV facet types.

This is NOT complete class coverage (other library types are absent). It
can supply candidate full stars for unconditional individual refutation.
Cycles are a rigorous superset: angle interval exclusion only.
"""
import json
from itertools import product
from flint import arb
from geometry import ball_interval,sub,norm2,dot,positive_sqrt
from s3_arith import independent,circumcentre
from s3_stars import model_geometry
from combinatorics import word_key
from stage2 import search_class

INTERVAL=['0.99999999999999999999206','1.00000000000000000000867']

def make_class(provider):
    names=('A40001','duoprism-3-3','pr-tet')
    models={name:provider.facet(name) for name in names}
    R=ball_interval(*INTERVAL);transitions={}
    for name,m in models.items():
        points,b,ns=model_geometry(m);edges=[sub(points[i],points[b]) for i in ns]
        for (i,j),p in m.edge_p.items():
            rs=[r for r in m.ridges if i in r['vertices'] and j in r['vertices']]
            if not (len(rs)==2):
                raise AssertionError()
            oG=circumcentre([edges[i],edges[j]]);rho2=norm2(oG)
            rays=[]
            for r in rs:
                ee=[edges[i] for i in r['vertices']];ids=independent(ee,3)
                rays.append(sub(circumcentre([ee[k] for k in ids]),oG))
            d2=[norm2(u) for u in rays]
            ca=dot(*rays)/positive_sqrt(d2[0]*d2[1]);h2=R*R-rho2
            cs=[positive_sqrt(d/h2) for d in d2]
            z=(ca-cs[0]*cs[1])/positive_sqrt((1-cs[0]*cs[0])*(1-cs[1]*cs[1]))
            if not (z>-1 and z<1):
                raise AssertionError()
            theta=z.acos()
            for a,c in ((0,1),(1,0)):
                key=(p,name,rs[a]['label'],rs[c]['label'])
                transitions[key]=theta if key not in transitions else transitions[key].union(theta)
    minimum=min(t.lower() for t in transitions.values())
    if not (minimum>0):
        raise AssertionError()
    maxk=2
    while not (maxk+1)*minimum>2*arb.pi(): maxk+=1
    cycles={}
    for p in sorted({t[0] for t in transitions}):
        ts=[(t,theta) for t,theta in transitions.items() if t[0]==p]
        for k in range(3,maxk+1):
            for seq in product(ts,repeat=k):
                if any(seq[i][0][3]!=seq[(i+1)%k][0][2] for i in range(k)): continue
                residual=sum((t for _,t in seq),arb(0))-2*arb.pi()
                if residual>0 or residual<0: continue
                word=tuple((t[1],t[3]) for t,_ in seq);key=(p,word_key(word))
                cycles[key]={'p':p,'facets':[t[1] for t,_ in seq],'cells':[t[3] for t,_ in seq]}
    return {'index':18,'R':INTERVAL,'cycles':list(cycles.values())},models

if __name__=='__main__':
    import models,sys
    c,ms=make_class(models)
    print('cycle superset',json.dumps(c),flush=True)
    r=search_class(c,ms,node_limit=5000)
    Path=__import__('pathlib').Path
    Path('r1-probe-s2.jsonl').write_text(json.dumps(r.record(include_states=True))+'\n')
    print('probe',json.dumps(r.record()),flush=True)
