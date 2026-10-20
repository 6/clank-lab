"""One exact known-model control: stericated regular5-simplex A510001.

Uses the independent helper's exact Coxeter construction, never legacy code.
The five maximal standard parabolics are A4(0001), A1(1)xA3(001),
A2(10)xA2(01), A3(100)xA1(1), A4(1000): hence exactly the three stated
facet types. This is the usual supporting-parabolic face theorem for the
Wythoff construction used in the paper's known-model construction rules.
"""
import models
from exact import dot,sub
facet=models.facet

class KnownR1:
    name='A510001'
    facet_types=('A40001','duoprism-3-3','pr-tet')
    def __init__(self):
        self.model=models.wythoff(self.name)
        self.points5=self.model.points4
        self.radius2=self.model.radius2
        self.base_index=self.model.base_index
        self.neighbours=tuple(self.model.neighbours)
    def certify_known_model(self):
        m=self.model;F=m.field;G=m.metric;pts=m.exact_vertices
        if m.radius2_exact!=F(1):return False
        if any(dot(p,p,G)!=F(1) for p in pts):return False
        exact_near=tuple(i for i,p in enumerate(pts) if dot(sub(p,pts[0]),sub(p,pts[0]),G)==F(1))
        return len(pts)==30 and len(exact_near)==8 and set(exact_near)==set(self.neighbours)

def known(name):
    if name!='A510001':raise NotImplementedError('R1 control provider supports only A510001')
    return KnownR1()
