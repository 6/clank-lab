"""Exact number-field arithmetic; Arb is used only for enclosing embeddings."""
from fractions import Fraction
from functools import lru_cache
import sympy as sp
from flint import arb, ctx, fmpq

class Undecided(Exception): pass

class Field:
    def __init__(self, expression=sp.sqrt(2)):
        ctx.prec=max(ctx.prec,320)
        self.domain=sp.QQ.algebraic_field(*(expression if isinstance(expression,tuple) else (expression,)))
        self.theta=self.domain.ext.as_expr()
        self.zero=self.domain.zero; self.one=self.domain.one
    def __call__(self,x):
        if isinstance(x,(float,sp.Float)) or (isinstance(x,sp.Basic) and x.has(sp.Float)):raise TypeError('inexact floating input is forbidden')
        if isinstance(x, Fraction): x=sp.Rational(x.numerator,x.denominator)
        return self.domain.convert(x)
    def expr(self,x): return self.domain.to_sympy(x)
    def ball(self,x):return self._ball(x,ctx.prec)
    @lru_cache(maxsize=32768)
    def _ball(self,x,precision):
        out=arb(0)
        theta=eval_ball(self.theta)
        for q in x.to_list(): out=out*theta+arb(fmpq(int(q.numerator),int(q.denominator)))
        return out
    def sign(self,x):
        if not x: return 0
        old=ctx.prec
        try:
            for bits in (max(320,old),640,1280,2560,5120):
                ctx.prec=bits; a=self.ball(x)
                if a>0:return 1
                if a<0:return -1
            raise Undecided('algebraic sign embedding not separated')
        finally:ctx.prec=old

def eval_ball(x):
    if isinstance(x,fmpq):return arb(x)
    if x.is_Rational:return arb(fmpq(int(x.p),int(x.q)))
    if x==sp.pi:return arb.pi()
    if x.is_Add:return sum((eval_ball(a) for a in x.args),arb(0))
    if x.is_Mul:
        z=arb(1)
        for a in x.args:z=z*eval_ball(a)
        return z
    if x.is_Pow:
        a,b=x.args
        if b==sp.Rational(1,2):return eval_ball(a).sqrt()
        if b.is_Integer:return eval_ball(a)**int(b)
    if x.func==sp.cos:return eval_ball(x.args[0]).cos()
    if x.func==sp.sin:return eval_ball(x.args[0]).sin()
    if x.func==sp.CRootOf:
        # SymPy's exact rational isolator identifies the intended real embedding.
        lo,hi=x._get_interval().as_tuple()
        while hi-lo>sp.Rational(1,2)**(ctx.prec+16):
            it=x._get_interval().refine();x._set_interval(it);lo,hi=it.as_tuple()
        return eval_ball(lo).union(eval_ball(hi))
    raise Undecided('unsupported exact embedding '+str(x))

def dot(x,y,G):return sum((x[i]*sum((G[i][j]*y[j] for j in range(len(y))),G[0][0]*0) for i in range(len(x))),G[0][0]*0)
def add(x,y):return tuple(a+b for a,b in zip(x,y))
def sub(x,y):return tuple(a-b for a,b in zip(x,y))
def scale(x,a):return tuple(a*b for b in x)
def solve(A,b):
    a=[list(r)+[v] for r,v in zip(A,b)];n=len(a)
    for i in range(n):
        j=next((j for j in range(i,n) if a[j][i]),None)
        if j is None:raise Undecided('singular exact solve')
        a[i],a[j]=a[j],a[i];t=a[i][i];a[i]=[v/t for v in a[i]]
        for j in range(n):
            if j!=i:
                t=a[j][i];a[j]=[v-t*w for v,w in zip(a[j],a[i])]
    return tuple(r[-1] for r in a)
def identity(n,F):return tuple(tuple(F(int(i==j)) for j in range(n)) for i in range(n))
def orbit(seed,generators):
    out=[seed];seen={seed:0}
    for p in out:
        for g in generators:
            q=g(p)
            if q not in seen:seen[q]=len(out);out.append(q)
    return out
