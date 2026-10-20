"""Outward Arb arithmetic for the independent S3 implementation."""
from itertools import combinations
from flint import arb, arb_mat, ctx
from geometry import Undecided, Impossible, add, sub, dot, scale, norm2, positive_sqrt

ctx.prec = max(ctx.prec, 256)


def finite(x, reason='nonfinite enclosure'):
    if not x.is_finite():
        raise Undecided(reason)
    return x


def square(x):
    # Arb **2 can return nan for intervals meeting zero in python-flint 0.8.
    return x*x


def columns(vectors):
    return arb_mat([[v[i] for v in vectors] for i in range(len(vectors[0]))])


def apply(A, v):
    return tuple(finite(sum((A[i,j]*v[j] for j in range(len(v))),arb(0)))
                 for i in range(A.nrows()))


def inverse(A):
    try:
        B=A.inv()
    except (ValueError, ZeroDivisionError) as exc:
        raise Undecided('matrix inverse not certified') from exc
    for i in range(B.nrows()):
        for j in range(B.ncols()): finite(B[i,j], 'nonfinite inverse')
    return B


def independent(vectors, dimension):
    for ids in combinations(range(len(vectors)), dimension):
        A=columns([vectors[i] for i in ids])
        G=A.transpose()*A
        if G.det()>0:
            return ids
    raise Undecided('no certified independent anchor subset')


def circumcentre(edges):
    """Minimum norm centre through 0 and all edges in their span.

    Inputs are a certified affinely spanning subset of a cospherical face.
    """
    A=columns(edges)
    b=arb_mat([[norm2(e)/2] for e in edges])
    c=A*inverse(A.transpose()*A)*b
    return tuple(finite(c[i,0]) for i in range(c.nrows()))


def frobenius_upper(A):
    # Sum absolute upper endpoints, then take sqrt. Avoid negative square
    # lower endpoints when an entry enclosure crosses zero.
    s=sum((square(A[i,j].abs_upper()) for i in range(A.nrows())
           for j in range(A.ncols())),arb(0))
    return finite(s.sqrt()).upper()


def apart(a,b):
    """Unconditional apartness, valid across different polytopes."""
    if any((x-y)>0 or (x-y)<0 for x,y in zip(a,b,strict=True)):
        return True
    return finite(norm2(sub(a,b)))>0


def conditional_same(a,b):
    """Only call when both are vertices of ONE hypothetical unit-edge P."""
    d=finite(norm2(sub(a,b)))
    if d>0:
        if d<1: raise Impossible('separation 0<distance²<1')
        return False
    if d<arb(1)/4: return True
    raise Undecided('conditional vertex identity undecided')


def perfect_matching(graph, right_count):
    """Inject all left vertices into right vertices; no greedy exclusions."""
    if len(graph)>right_count: return None
    matched={}
    def augment(i,seen):
        for j in graph[i]:
            if not 0<=j<right_count: raise ValueError('bad bipartite index')
            if j in seen: continue
            seen.add(j)
            if j not in matched or augment(matched[j],seen):
                matched[j]=i
                return True
        return False
    for i in range(len(graph)):
        if not augment(i,set()): return None
    result=[None]*len(graph)
    for j,i in matched.items(): result[i]=j
    return result
