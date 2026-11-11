"""GPT-6.1 Sol builder; direct independent certificate checker, no search import.

Cycle indices give unique cone centres, ordered after graph vertices.
Boundary keys (edge, cycle index) represent an unordered edge/disk cell.
"""
import json,sys
from collections import Counter

def check(path):
    d=json.load(open(path));assert d['format']=='cycle-vk-mod2-v1','format'
    n=d['vertices'];assert type(n) is int and n>=3,'vertices'
    edges=[tuple(e) for e in d['edges']]
    assert len(edges)==len(set(edges)) and all(len(e)==2 and 0<=e[0]<e[1]<n for e in edges),'edges'
    edge_set=set(edges);cycles=d['cycles'];assert len({tuple(c) for c in cycles})==len(cycles),'duplicate cycle'
    boundaries=[]
    for c in cycles:
        assert len(c)>=3 and len(set(c))==len(c) and all(type(v) is int and 0<=v<n for v in c),'simple cycle'
        assert c[0]==min(c) and c[1]<c[-1],'canonical cycle'
        b=[tuple(sorted((c[k],c[(k+1)%len(c)]))) for k in range(len(c))]
        assert all(e in edge_set for e in b),'cycle nonedge'
        boundaries.append(b)
    pairs=d['pairs'];assert len({tuple(p) for p in pairs})==len(pairs),'duplicate pair'
    boundary=Counter();intersection=0
    for pair in pairs:
        assert len(pair)==2,'pair length'
        i,j=pair;assert 0<=i<j<len(cycles),'pair range'
        assert set(cycles[i]).isdisjoint(cycles[j]),'disjointness'
        for e in boundaries[i]:boundary[(e,j)]^=1
        for e in boundaries[j]:boundary[(e,i)]^=1
        for e in boundaries[i]:
            t=set(e+(n+i,))
            for f in boundaries[j]:
                sequence=sorted(t|set(f+(n+j,)))
                # The unique affine dependence of six moment-curve points
                # in R4 has alternating coefficient signs.
                intersection^=int({sequence[0],sequence[2],sequence[4]}==t or {sequence[1],sequence[3],sequence[5]}==t)
    assert not any(boundary.values()),'nonzero boundary'
    assert intersection==1,'even intersection'
    return {'accepted':True,'vertices':n,'edges':len(edges),'cycles':len(cycles),'pairs':len(pairs),'boundary':0,'intersection':intersection}
if __name__=='__main__':
    try:print(json.dumps(check(sys.argv[1]),sort_keys=True))
    except (AssertionError,ValueError,KeyError,IndexError,TypeError) as e:print('REJECT: '+str(e));sys.exit(1)
