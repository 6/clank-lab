"""Exact quadratic arithmetic and authoritative exceptional-model inputs."""
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'check_u3'))
import tcert

Z = (F(0), F(0))
O = (F(1), F(0))
add = tcert.qadd
sub = tcert.qsub
mul = tcert.qmul
inv = tcert.qinv
dot = tcert.qdot
vsub = tcert.qvsub


def sign(x):
    a, b = x
    if not b:
        return (a > 0) - (a < 0)
    if not a or (a > 0) == (b > 0):
        return (b > 0) - (b < 0)
    c = a*a - 5*b*b
    return ((a > 0) - (a < 0)) * ((c > 0) - (c < 0))


def det(A):
    n = len(A)
    if not n:
        return O
    out = Z
    for j in range(n):
        minor = [row[:j] + row[j+1:] for row in A[1:]]
        term = mul(A[0][j], det(minor))
        out = add(out, term) if j % 2 == 0 else sub(out, term)
    return out


def rank(A):
    return tcert.qrank(A)


def encode(x):
    return [str(x[0]), str(x[1])]


def decode(x):
    return F(x[0]), F(x[1])


def vertices(name):
    if name == 'sadi':
        return tcert.sadi_exact()
    if name == 'gap':
        return tcert.gap_exact()
    raise ValueError(name)


def distances(V):
    return [[dot(vsub(a,b),vsub(a,b)) for b in V] for a in V]


def normal_frame(V, S, dimension):
    """An affine frame and supporting functional in the affine span of S.

    For a 4D cell choose 3 independent coordinate columns of its affine
    direction space, then use a 3D cross product for its polygon planes.
    """
    for frame in combinations(S, dimension+1):
        rows = [vsub(V[i], V[frame[0]]) for i in frame[1:]]
        if rank(rows) == dimension:
            return list(frame)
    raise ArithmeticError('affine rank too small')


def hyperplane(V, frame, columns):
    rows = [[vsub(V[i],V[frame[0]])[j] for j in columns] for i in frame[1:]]
    n = []
    for j in range(len(columns)):
        x = det([list(r[:j]+r[j+1:]) for r in rows])
        n.append(x if j % 2 == 0 else sub(Z,x))
    out = [Z]*4
    for j,x in zip(columns,n):
        out[j]=x
    return out, dot(out,V[frame[0]])


def orient(V, S, parent, frame, columns):
    n,h = hyperplane(V,frame,columns)
    off = [sub(dot(n,V[i]),h) for i in parent if i not in S]
    if all(sign(x)>0 for x in off):
        n,h = [sub(Z,x) for x in n],sub(Z,h)
    if not off or not all(sign(sub(dot(n,V[i]),h))<0 for i in parent if i not in S):
        raise ArithmeticError('not supporting')
    return n,h


def distance_ids(D):
    keys = {x for row in D for x in row}
    ids = {x:i for i,x in enumerate(sorted(keys))}
    return [[ids[x] for x in row] for row in D]


def transitive(perms,n):
    seen={0}; todo=[0]
    for i in todo:
        for p in perms:
            j=p[i]
            if j not in seen:
                seen.add(j);todo.append(j)
    return len(seen)==n
