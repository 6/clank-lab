"""Corrupt full exceptional-model certificates; both checkers must reject."""
from copy import deepcopy
import json
from pathlib import Path
import q5_check_a as a
import q5_check_b as b


def main():
    model=json.loads((Path(__file__).resolve().parent/'q5_certificate.json').read_text())['models'][0]
    cases=[]
    def bad(name,fn):
        m=deepcopy(model);fn(m);cases.append((name,m))
    bad('index-swap',lambda m:m['vertices_600'].__setitem__(slice(0,2),m['vertices_600'][:2][::-1]))
    bad('nonmetric-global-permutation',lambda m:m['symmetries'][0].__setitem__(0,m['symmetries'][0][1]))
    bad('nontransitive-global-model',lambda m:m.__setitem__('symmetries',[]))
    bad('nonsupporting-cell-plane',lambda m:m['cells'][0].__setitem__('offset',['0','0']))
    bad('wrong-polygon-vertex',lambda m:m['cells'][0]['polygons'][0]['vertices'].__setitem__(0,next(i for i in m['cells'][0]['vertices'] if i not in m['cells'][0]['polygons'][0]['vertices'])))
    bad('wrong-uniform-cell-label',lambda m:m['cells'][0].__setitem__('label','A5'))
    bad('missing-cell-polygon',lambda m:m['cells'][0]['polygons'].pop())
    bad('missing-all-cells',lambda m:m.__setitem__('cells',[]))
    for checker in (a,b):
        for name,m in cases:
            try:checker.check_model(m)
            except (ArithmeticError,ValueError,KeyError,IndexError):
                print(checker.__name__,name,'rejected',flush=True)
            else:raise ArithmeticError(checker.__name__+' accepted '+name)
    print('Q5 corruptions rejected 8/8 by each checker')

if __name__=='__main__':main()
