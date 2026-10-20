"""Solved simplex controls built directly from their exact Gram matrix."""
from itertools import permutations
from flint import arb


class SimplexFacet:
    name='A40001'
    def __init__(self):
        self.radius2=arb(2)/5
        t=1/(2*arb(2).sqrt())
        self.vf_points=[tuple(t*x for x in v) for v in [(1,1,1),(1,-1,-1),(-1,1,-1),(-1,-1,1)]]
        self.ridges=[{'vertices':list(v),'label':'tet'} for v in [(0,1,2),(0,1,3),(0,2,3),(1,2,3)]]
        self.edge_p={(i,j):3 for i in range(4) for j in range(i+1,4)}
        self.stabilizers=list(permutations(range(4)))
    def verify_stabilizer(self,perm):
        # Exact Gram entries: 3/8 on the diagonal, -1/8 elsewhere.
        return sorted(perm)==list(range(4))


def simplex_class():
    return {'index':0, 'R':['0.645497224367902814194992677287662690218078294','0.645497224367902814197224805093123402837246877'],
            'cycles':[{'p':3,'facets':['A40001']*3,'cells':['tet']*3}]}


if __name__=='__main__':
    import json
    from stage2 import search_class
    result=search_class(simplex_class(),{'A40001':SimplexFacet()})
    print(json.dumps(result.record(),indent=2))
    if not (not result.open_reasons):
        raise AssertionError()
    if not (len(result.record()['vfs'])==1):
        raise AssertionError()
    if not (len(result.states[0]['points'])==5):
        raise AssertionError()
    if not (len(result.states[0]['facets'])==5):
        raise AssertionError()
