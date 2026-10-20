"""Faces through a Wythoff vertex, by exact parabolic combinatorics.

No full H4 vertex orbit, hull proposal, tolerance, or existing table is used.
Roots are coefficient vectors in the unit simple-root basis.
"""
from itertools import combinations
from functools import lru_cache
from quadratic import Field

DIAGRAMS = {
    'A4': {(0,1):3,(1,2):3,(2,3):3},
    'B4': {(0,1):3,(1,2):3,(2,3):4},
    'D4': {(0,1):3,(1,2):3,(1,3):3},
    'F4': {(0,1):3,(1,2):4,(2,3):3},
    'H4': {(0,1):5,(1,2):3,(2,3):3},
    'A3': {(0,1):3,(1,2):3},
    'B3': {(0,1):3,(1,2):4},
    'H3': {(0,1):5,(1,2):3},
}

CONFIG_LABEL = {
    (3,3,3):'tet', (3,3,3,3):'oct', (4,4,4):'cube',
    (3,3,3,3,3):'ico', (5,5,5):'doe',
    (3,6,6):'tut', (3,3,4,4):'co', (3,8,8):'tic',
    (4,6,6):'toe', (3,4,4,4):'sirco', (4,6,8):'girco',
    (3,3,5,5):'id', (5,6,6):'tid', (3,10,10):'ti',
    (3,4,4,5):'srid', (4,6,10):'grid',
    (3,3,3,3,4):'snic', (3,3,3,3,5):'snid',
}


def config_label(sizes):
    c = tuple(sorted(sizes))
    if c in CONFIG_LABEL:
        return CONFIG_LABEL[c]
    if len(c) == 3 and c.count(4) == 2:
        n = sum(c)-8
        return 'cube' if n == 4 else 'P'+str(n)
    if len(c) == 4 and c.count(3) == 3:
        n = sum(c)-9
        return 'oct' if n == 3 else 'A'+str(n)
    raise ValueError(('unresolved polyhedron configuration',c))


class Coxeter:
    def __init__(self, group):
        self.group = group
        self.n = int(group[1:])
        self.edges = DIAGRAMS[group]
        self.f = Field(5 if 5 in self.edges.values() else 2 if 4 in self.edges.values() else 0)
        f = self.f
        self.G = [[f.one if i == j else f.zero for j in range(self.n)] for i in range(self.n)]
        for (i,j),m in self.edges.items():
            v = f.q('-1/2') if m == 3 else f.q(0,'-1/2') if m == 4 else f.q('-1/4','-1/4')
            self.G[i][j] = self.G[j][i] = v
        self.basis = tuple(tuple(f.one if i == j else f.zero for i in range(self.n)) for j in range(self.n))
        self.Ginv = tuple(f.solve(self.G,e) for e in self.basis)

    def reflect(self, v, i):
        a = list(v)
        a[i] = self.f.sub(a[i],self.f.mul(self.f.q(2),self.f.dot(self.G[i],v)))
        return tuple(a)

    def root_orbit(self, seeds, nodes):
        seen = set(seeds)
        todo = list(seen)
        for v in todo:
            for i in nodes:
                w = self.reflect(v,i)
                if w not in seen:
                    seen.add(w)
                    todo.append(w)
        return frozenset(seen)

    def active(self, I, J):
        rest = set(I)
        while rest:
            C = {rest.pop()}
            todo = list(C)
            for i in todo:
                new = {j for j in rest if tuple(sorted((i,j))) in self.edges}
                C.update(new)
                rest.difference_update(new)
                todo.extend(new)
            if not C.intersection(J):
                return False
        return True

    def radius_squared(self, J, I=None):
        I = tuple(range(self.n) if I is None else I)
        b = tuple(self.f.q('1/2') if i in J else self.f.zero for i in I)
        x = self.f.solve([[self.G[i][j] for j in I] for i in I],b)
        return self.f.dot(b,x)

    def facet_normals(self, J, cells):
        f = self.f
        b = tuple(f.q('1/2') if i in J else f.zero for i in range(self.n))
        x = f.solve(self.G,b)
        ans = {}
        for C in cells:
            frame = []
            for root in sorted(C):
                if f.rank(frame+[root]) > len(frame):
                    frame.append(root)
            if not (len(frame) == self.n-1):
                raise AssertionError()
            # Covector h, normalized h(x)=1, annihilating cell edges.
            h = f.solve(frame+[x],[f.zero]*(self.n-1)+[f.one])
            n = tuple(f.dot(row,h) for row in self.Ginv)
            if not (f.sign(f.dot(h,n)) > 0):
                raise AssertionError()
            ans[C] = (h,n)
        return ans

    def internal_cosine(self, normals, A, B):
        f = self.f
        h,n = normals[A]
        k,m = normals[B]
        numerator = f.neg(f.dot(h,m))
        denominator_squared = f.mul(f.dot(h,n),f.dot(k,m))
        square = f.div(f.mul(numerator,numerator),denominator_squared)
        return f.sign(numerator),square

    def face_stars(self, J, dim):
        """Map each face's incident edge roots to a standard parabolic I."""
        U = tuple(i for i in range(self.n) if i not in J)
        result = {}
        for I in combinations(range(self.n),dim):
            if not self.active(I,J):
                continue
            seed = self.root_orbit([self.basis[j] for j in I if j in J],[i for i in I if i in U])
            faces = {seed}
            todo = [seed]
            for face in todo:
                for i in U:
                    new = frozenset(self.reflect(v,i) for v in face)
                    if new not in faces:
                        faces.add(new)
                        todo.append(new)
            for face in faces:
                if face in result:
                    raise AssertionError('two standard parabolics yield the same face')
                result[face] = I
        return result

    def polygon_size(self, I, J):
        i,j = I
        m = self.edges.get(tuple(sorted((i,j))),2)
        return m*(2 if i in J and j in J else 1)

    def local_data(self, J):
        J = frozenset(J)
        edges = self.face_stars(J,1)
        polygons = self.face_stars(J,2)
        cells = self.face_stars(J,3) if self.n == 4 else {}
        polygon_sizes = {F:self.polygon_size(I,J) for F,I in polygons.items()}
        for F in polygons:
            if not (len(F) == 2):
                raise AssertionError()
            if not (all(frozenset([v]) in edges for v in F)):
                raise AssertionError()
        labels = {}
        for C,I in cells.items():
            conf = [p for F,p in polygon_sizes.items() if F <= C]
            labels[C] = config_label(conf)
        words = []
        for F,p in polygon_sizes.items():
            incident = [C for C in cells if F <= C]
            if self.n == 4:
                if not (len(incident) == 2):
                    raise AssertionError((self.group,J,p,len(incident)))
                A,B = sorted(labels[C] for C in incident)
                words.append((p,A,B))
        return {'edges':edges,'polygons':polygons,'cells':cells,
                'polygon_sizes':polygon_sizes,'labels':labels,'occurrences':words}


@lru_cache(None)
def coxeter(group):
    return Coxeter(group)
