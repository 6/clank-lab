"""Exact Q(sqrt(2),sqrt(3)); no external packages or model imports."""
from fractions import Fraction as F
from math import lcm

ZERO = (F(0),) * 4
ONE = (F(1), F(0), F(0), F(0))

def q(a=0, b=0, c=0, d=0):
    return tuple(map(F, (a,b,c,d)))

def add(x,y): return tuple(a+b for a,b in zip(x,y))
def neg(x): return tuple(-a for a in x)
def sub(x,y): return add(x,neg(y))
def scale(x,n): return tuple(a*n for a in x)
def mul(x,y):
    out=[F(0)]*4
    for i,a in enumerate(x):
        if not a: continue
        for j,b in enumerate(y):
            if b: out[i^j] += a*b*(2 if i&j&1 else 1)*(3 if i&j&2 else 1)
    return tuple(out)
def inv(x):
    # Product of the other three Galois conjugates, divided by the norm.
    y=ONE
    for s,t in [(-1,1),(1,-1),(-1,-1)]:
        y=mul(y,(x[0],s*x[1],t*x[2],s*t*x[3]))
    n=mul(x,y)
    if not (n[0] and not any(n[1:])):
        raise AssertionError('noninvertible field element')
    return scale(y,1/n[0])
def dot(x,y):
    out=ZERO
    for a,b in zip(x,y): out=add(out,mul(a,b))
    return out

def solve(a,b):
    """Exact Gauss-Jordan solve of a square nonsingular field matrix."""
    a=[list(row)+[v] for row,v in zip(a,b)]
    n=len(a)
    for i in range(n):
        pivot=next((j for j in range(i,n) if a[j][i]!=ZERO),None)
        if pivot is None: raise ValueError('singular matrix')
        a[i],a[pivot]=a[pivot],a[i]
        s=inv(a[i][i]); a[i]=[mul(v,s) for v in a[i]]
        for j in range(n):
            if j!=i and a[j][i]!=ZERO:
                s=a[j][i]; a[j]=[sub(v,mul(s,w)) for v,w in zip(a[j],a[i])]
    return tuple(row[-1] for row in a)

def integral(points, denominator=None):
    d=denominator or lcm(*(a.denominator for p in points for x in p for a in x))
    return d, tuple(tuple(tuple(int(a*d) for a in x) for x in p) for p in points)

def distance(x,y):
    """Numerators of squared distance for common-denominator coordinates."""
    out=[0,0,0,0]
    for v,w in zip(x,y):
        a,b,c,d=(v[i]-w[i] for i in range(4))
        out[0]+=a*a+2*b*b+3*c*c+6*d*d
        out[1]+=2*a*b+6*c*d
        out[2]+=2*a*c+4*b*d
        out[3]+=2*a*d+2*b*c
    return tuple(out)
