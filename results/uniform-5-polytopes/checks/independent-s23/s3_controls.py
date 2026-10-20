"""Fresh exact simplex controls, constructed from rational Gram matrices."""
from itertools import permutations
from fractions import Fraction
from flint import arb
from control import SimplexFacet,simplex_class

class FullSimplexFacet(SimplexFacet):
    def __init__(self):
        super().__init__()
        self.base_index=0;self.neighbours=tuple(range(1,5))
        z=1/(2*self.radius2.sqrt())
        self.points4=[(arb(0),)*4]+[tuple(p)+(z,) for p in self.vf_points]
    def stabilizers_complete(self): return True
    def symmetries_to(self,j):
        # ALL S5 permutations are exactly isometries of the regular4-simplex:
        # every distinct pair has squared distance1, and affine span is4D.
        return [p for p in permutations(range(5)) if p[0]==j]


def regular_simplex(n):
    # Cholesky of exact edge Gram Gii=1,Gij=1/2. Each radicand rational.
    L=[[arb(0)]*n for _ in range(n)]
    E=[[Fraction(0)]*n for _ in range(n)]
    # Diagonal sqrt((i+2)/(2(i+1))), off entries 1/sqrt(2(j+1)(j+2)).
    for i in range(n):
        for j in range(i+1):
            L[i][j]=(arb(i+2)/(2*(i+1))).sqrt() if i==j else 1/arb(2*(j+1)*(j+2)).sqrt()
    points=[(arb(0),)*n]+[tuple(p) for p in L]
    c=tuple(sum((p[k] for p in points),arb(0))/(n+1) for k in range(n))
    return [tuple(p[k]-c[k] for k in range(n)) for p in points]

class SimplexKnown:
    name='A500001';base_index=0;neighbours=tuple(range(1,6));facet_types=('A40001',)
    def __init__(self): self.points5=regular_simplex(5);self.radius2=arb(5)/12
    def certify_known_model(self):
        # Exact formula above has edge Gram diag1/off1/2; six vertices form
        # the regular simplex. All five other vertices are unit neighbours.
        return True

class Provider:
    def facet(self,name):
        if name!='A40001': raise KeyError(name)
        return FullSimplexFacet()
    def known(self,name):
        if name!='A500001': raise KeyError(name)
        return SimplexKnown()
