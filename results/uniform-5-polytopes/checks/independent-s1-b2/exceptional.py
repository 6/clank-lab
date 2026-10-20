"""Exact local hull reconstruction for the two 600-cell deletions.

The only inputs are the standard mathematical 600-cell coordinates and
the two deletion descriptions in the paper. No repository data is read.
Every supporting inequality is checked in the ordered field Q(sqrt(5)).
"""
from itertools import permutations,product,combinations
from collections import Counter
from functools import lru_cache
from quadratic import Field
from parabolic import config_label

F = Field(5)


def even_permutations(n):
    return [p for p in permutations(range(n))
            if sum(p[i]>p[j] for i in range(n) for j in range(i+1,n)) % 2 == 0]


@lru_cache(None)
def cell600():
    """Radius-one 600-cell: 8 axes, 16 half-signs, 96 even permutations."""
    points = set()
    for i in range(4):
        for sign in (-1,1):
            points.add(tuple(F.q(sign if j == i else 0) for j in range(4)))
    for signs in product((-1,1),repeat=4):
        points.add(tuple(F.q(str(s)+'/2') for s in signs))
    phi = F.q('1/2','1/2')
    invphi = F.q('-1/2','1/2')
    for signs in product((-1,1),repeat=3):
        seed = (F.zero,F.q(str(signs[0])+'/2'),
                F.mul(F.q(str(signs[1])+'/2'),phi),
                F.mul(F.q(str(signs[2])+'/2'),invphi))
        for perm in even_permutations(4):
            points.add(tuple(seed[i] for i in perm))
    points = tuple(sorted(points))
    if not (len(points) == 120):
        raise AssertionError()
    if not (all(F.dot(v,v) == F.one for v in points)):
        raise AssertionError()
    edge_squared = F.q('3/2','-1/2')
    for v in points:
        distances = Counter(F.dot(F.vecsub(v,w),F.vecsub(v,w)) for w in points)
        if not (distances[edge_squared] == 12):
            raise AssertionError()
        if not (all(F.sign(d) >= 0 and (d == F.zero or F.sign(F.sub(d,edge_squared)) >= 0) for d in distances)):
            raise AssertionError()
    return points


def exceptional_points(name):
    full = cell600()
    if name == 'sadi':
        kept = [v for v in full if any(x[1] != 0 for x in v)]
        description = {'deletion':'coordinate 24-cell'}
    else:
        a = tuple(F.q(1 if j == 0 else 0) for j in range(4))
        b = next(v for v in full if F.dot(a,v) == F.q('1/4','1/4'))
        plane = [v for v in full if F.rank([a,b,v]) == 2]
        perp = [v for v in full if F.dot(a,v) == F.zero and F.dot(b,v) == F.zero]
        if not (len(plane) == len(perp) == 10):
            raise AssertionError()
        if not (not set(plane).intersection(perp)):
            raise AssertionError()
        edge_squared = F.q('3/2','-1/2')
        # Ten points on each unit circle, degree two in the unit-edge
        # graph: all adjacent arcs are pi/5, so these are great decagons.
        for decagon in (plane,perp):
            if not (all(sum(F.dot(F.vecsub(v,w),F.vecsub(v,w)) == edge_squared
                           for w in decagon) == 2 for v in decagon)):
                raise AssertionError()
        kept = [v for v in full if v not in plane and v not in perp]
        description = {'deletion':'two orthogonal great decagons',
                       'plane_basis':[[str(F.expr(x)) for x in v] for v in (a,b)]}
    phi = F.q('1/2','1/2')
    points = tuple(sorted(F.scale(phi,v) for v in kept))
    if not (len(points) == (96 if name == 'sadi' else 100)):
        raise AssertionError()
    return points,description


def exceptional_record(name):
    from library import make_record,cell_radius_squared
    points,description = exceptional_points(name)
    base = points[0]
    radius = F.dot(base,base)
    neighbors = tuple(v for v in points if F.dot(F.vecsub(v,base),F.vecsub(v,base)) == F.one)
    roots = tuple(F.vecsub(v,base) for v in neighbors)
    if not (len(roots) == (9 if name == 'sadi' else 10)):
        raise AssertionError()
    facets = {}
    # Any VF facet has three affinely independent points. Solve its
    # normal perpendicular to the sphere radius, normalized n.d=1.
    for ids in combinations(range(len(roots)),3):
        matrix = [base]+[roots[i] for i in ids]
        if F.rank(matrix) != 4:
            continue
        normal = F.solve(matrix,(F.zero,F.one,F.one,F.one))
        signs = [F.sign(F.sub(F.dot(normal,v),F.one)) for v in roots]
        if max(signs) > 0:
            continue
        face = frozenset(i for i,s in enumerate(signs) if s == 0)
        if not (len(face) >= 3):
            raise AssertionError()
        full_normal = F.vecadd(normal,F.scale(F.q(2),base))
        values = [F.dot(full_normal,F.vecsub(v,base)) for v in points]
        if not (all(F.sign(t) <= 0 for t in values)):
            raise AssertionError()
        full_cell = [v for v,t in zip(points,values) if t == F.zero]
        if not (F.rank([F.vecsub(v,base) for v in full_cell]) == 3):
            raise AssertionError()
        # The sphere centre projected onto this supporting hyperplane
        # is the unique cell circumcentre; derive its radius directly.
        h = F.dot(full_normal,base)
        cell_radius = F.sub(radius,F.div(F.mul(h,h),F.dot(full_normal,full_normal)))
        if face in facets:
            if not (facets[face]['radius_squared'] == cell_radius):
                raise AssertionError()
        facets[face] = {'radius_squared':cell_radius,'full_vertex_count':len(full_cell),
                        'normal':full_normal}
    cells = sorted(facets,key=lambda Ff:tuple(sorted(Ff)))
    edges = set()
    for i,C in enumerate(cells):
        for D in cells[:i]:
            e = C.intersection(D)
            if len(e) == 2:
                edges.add(frozenset(e))
    sizes = {}
    for edge in edges:
        if not (sum(edge <= cell for cell in cells) == 2):
            raise AssertionError()
        i,j = sorted(edge)
        chord_squared = F.dot(F.vecsub(roots[i],roots[j]),F.vecsub(roots[i],roots[j]))
        p = 3 if chord_squared == F.one else 5 if chord_squared == F.q('3/2','1/2') else None
        if not (p is not None):
            raise AssertionError(('unresolved polygon',name,chord_squared))
        sizes[edge] = p
    labels = {}
    for C in cells:
        face_edges = [edge for edge in edges if edge <= C]
        if not (len(face_edges) == len(C)):
            raise AssertionError()
        if not (all(sum(i in edge for edge in face_edges) == 2 for i in C)):
            raise AssertionError()
        label = config_label(sizes[edge] for edge in face_edges)
        if not (label in ('tet','ico','A5')):
            raise AssertionError()
        if not (F.expr(facets[C]['radius_squared']).expand() == cell_radius_squared(label).expand()):
            raise AssertionError()
        if not (facets[C]['full_vertex_count'] == {'tet':4,'ico':12,'A5':10}[label]):
            raise AssertionError()
        labels[C] = label
    if not (len(roots)-len(edges)+len(cells) == 2):
        raise AssertionError()
    if not (all(sum(i in edge for edge in edges) >= 3 for i in range(len(roots)))):
        raise AssertionError()
    occurrences = []
    cosines = {}
    for edge,p in sizes.items():
        C,D = [C for C in cells if edge <= C]
        A,B = sorted((labels[C],labels[D]))
        occurrences.append((p,A,B))
        n,m = facets[C]['normal'],facets[D]['normal']
        numerator = F.neg(F.dot(n,m))
        square = F.div(F.mul(numerator,numerator),F.mul(F.dot(n,n),F.dot(m,m)))
        import sympy as sp
        cosine = F.sign(numerator)*sp.sqrt(F.expr(square))
        if (p,A,B) in cosines:
            if not (cosines[p,A,B] == cosine):
                raise AssertionError()
        cosines[p,A,B] = cosine
    incidences = {**description,
        'base_vertex':[str(F.expr(x)) for x in base],
        'neighbor_vectors':[[str(F.expr(x)) for x in v] for v in roots],
        'cells':[{'neighbors':sorted(C),'label':labels[C],
                  'full_vertex_count':facets[C]['full_vertex_count']} for C in cells],
        'polygons':[{'neighbors':sorted(e),'p':sizes[e],
                     'cells':[i for i,C in enumerate(cells) if e <= C]} for e in sorted(edges,key=lambda e:tuple(sorted(e)))],
    }
    return make_record(name,F.expr(radius),occurrences,incidences,cosines)


def exceptional_records():
    return [exceptional_record(name) for name in ('sadi','gap')]
