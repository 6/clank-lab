"""Independent cycle enumeration and certified closure roots.

Input is exclusively the independently reconstructed library. Legacy tables
are loaded only by compare.py after this program has finished.
"""
from collections import defaultdict, Counter
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
import argparse
import hashlib
import json
import time
from pathlib import Path
import sympy as sp
from flint import arb
from arithmetic import (ball, endpoints, hull, acos_clip, decimal_bounds,
                        evaluate, Undecided)


@lru_cache(None)
def exact_zero(expr):
    """An algebraic equality is accepted only by exact symbolic reduction."""
    expr = sp.sympify(expr)
    z = sp.simplify(sp.expand(expr))
    if z == 0:
        return True
    if z.is_Rational:
        return False
    # AlgebraicNumber computes an exact minimal polynomial / field embedding.
    # It never promotes a small numerical value to zero.
    return all(a == 0 for a in sp.polys.numberfields.to_number_field(z).coeffs())


@lru_cache(None)
def rational_angle(c):
    """Numerics propose a rational angle; exact equality alone accepts it."""
    a = acos_clip(evaluate(c)) / arb.pi()
    candidate = Fraction(float(a)).limit_denominator(120)
    if not 0 < candidate < 1:
        return None
    if not (a - ball(candidate)).contains(0):
        return None
    exact = sp.cos(sp.pi * sp.Rational(candidate.numerator, candidate.denominator))
    return candidate if exact_zero(c - exact) else None


@lru_cache(None)
def prove_flat(cosines):
    a = sum((acos_clip(evaluate(c)) for c in cosines), arb(0))
    if not (a > arb.pi() and a < 3*arb.pi()):
        raise Undecided('angle winding not certified')
    rational = Fraction(0)
    re, im = sp.Integer(1), sp.Integer(0)
    for c in cosines:
        r = rational_angle(c)
        if r is not None:
            rational += r
        else:
            s = sp.sqrt(1-c*c)
            re, im = sp.expand(re*c-im*s), sp.expand(im*c+re*s)
    angle = sp.pi * sp.Rational(rational.numerator, rational.denominator)
    if not (exact_zero(re-sp.cos(angle)) and exact_zero(im+sp.sin(angle))):
        raise Undecided('unproved flat identity: '+str(cosines))
    return True


@dataclass
class Edge:
    name: str
    p: int
    left: str
    right: str
    r2: object
    cosine: object
    ex_r2: object
    ex_cos: object
    angle: object = None
    def __post_init__(self):
        self.angle = acos_clip(self.cosine)
        if not (-1 < self.cosine and self.cosine < 1):
            raise Undecided('angle not strictly between zero and pi')
        # Bound the length of every allowed walk by six.
        if not self.cosine < ball(Fraction(1,2)):
            if self.ex_cos is None or not exact_zero(self.ex_cos-sp.Rational(1,2)):
                raise Undecided('minimum angle pi/3 not proved')


def canonical(pairs):
    pairs = tuple(pairs)
    n = len(pairs)
    rev = tuple((pairs[i][0], pairs[(i-1) % n][1]) for i in range(n-1,-1,-1))
    return min(seq[i:]+seq[:i] for seq in (pairs, rev) for i in range(n))


def certify_monotonicity(A, B, T, cosine):
    """Certify decreasing closure cosine on the entire admissible u interval.

    Its derivative has positive denominator and affine numerator
    N(u)=-sqrt(AB)+c(A+B)/2+u*(sqrt(AB)(A+B)/2-cAB).
    Negativity at both endpoints of [0,1/T] certifies the whole interval.
    """
    if not (A > 0 and B > 0 and T > A and T > B):
        raise Undecided('invalid monotonicity domain')
    d = (A*B).sqrt()
    constant = -d + cosine*(A+B)/2
    slope = d*(A+B)/2 - cosine*A*B
    if not (constant < 0 and constant+slope/T < 0):
        raise Undecided('closure monotonicity not certified on entire domain')


def enumerate_cycles(edges):
    by_p = defaultdict(list)
    for e in edges:
        by_p[e.p].append(e)
    cycles = []
    for p, es in sorted(by_p.items()):
        graph = defaultdict(list)
        for e in es:
            graph[e.left].append((e.right,e))
            if e.left != e.right:
                graph[e.right].append((e.left,e))
        found = set()
        for start in sorted(graph):
            def dfs(v, path, angle):
                for w,e in graph[v]:
                    if w < start:
                        continue
                    a = angle + e.angle
                    if a > 2*arb.pi():
                        continue
                    new = path+((e.name,w),)
                    if w == start and len(new) >= 3:
                        found.add(canonical(new))
                    if len(new) < 6:
                        dfs(w,new,a)
            dfs(start,(),arb(0))
        cycles.extend((p,c) for c in sorted(found))
    return cycles


class Solver:
    def __init__(self, edges, cell_r2, exact_cell_r2):
        self.lookup = {(e.p,e.name,*sorted((e.left,e.right))):e for e in edges}
        if len(self.lookup) != len(edges):
            raise ValueError('duplicate incidence word')
        self.cell_r2 = cell_r2
        self.exact_cell_r2 = exact_cell_r2

    def data(self,p,pairs):
        es = [self.lookup[(p,k,*sorted((pairs[i-1][1],c)))]
              for i,(k,c) in enumerate(pairs)]
        rho = 1 / (4*(arb.pi()/p).sin()**2)
        ds = [self.cell_r2[c]-rho for _,c in pairs]
        for i,e in enumerate(es):
            if not (ds[i] > 0 and e.r2 > self.cell_r2[pairs[i][1]]
                    and e.r2 > self.cell_r2[pairs[i-1][1]]):
                raise Undecided('invalid facet or cell radius')
            # Strict derivative proof: see MATHEMATICS.md.
            A,B = ds[i-1],ds[i]
            T=e.r2-rho
            expected=((A*B).sqrt()-((T-A)*(T-B)).sqrt())/T
            if not expected.overlaps(e.cosine):
                raise Undecided('word-angle formula disagreement')
            certify_monotonicity(A, B, T, e.cosine)
        return es,rho,ds

    def algebraic_sign(self,value,expr):
        if value > 0:
            return 1
        if value < 0:
            return -1
        if expr is not None and exact_zero(expr):
            return 0
        raise Undecided('unresolved algebraic sign')

    def solve(self,p,pairs):
        es,rho,ds = self.data(p,pairs)
        a = sum((e.angle for e in es),arb(0))-2*arb.pi()
        if a > 0:
            raise AssertionError('enumerator admitted excessive angle')
        if not a < 0:
            if any(e.ex_cos is None for e in es):
                raise Undecided('flat identity lacks algebraic input')
            prove_flat(tuple(sorted((e.ex_cos for e in es),key=str)))
            return {'status':'FLAT'}
        if len(pairs)==3:
            return self.triangle(p,pairs,es,rho,ds)
        return self.long_cycle(p,pairs,es,rho,ds)

    def triangle(self,p,pairs,es,rho,ds):
        # Cell indices are the outgoing cells in pairs. Edges i connect i-1,i.
        a,b,c = es[1].cosine,es[0].cosine,es[2].cosine
        determinant = 1+2*a*b*c-a*a-b*b-c*c
        exact = all(e.ex_cos is not None for e in es)
        ea,eb,ec = (es[1].ex_cos,es[0].ex_cos,es[2].ex_cos)
        edet = 1+2*ea*eb*ec-ea**2-eb**2-ec**2 if exact else None
        detsign = self.algebraic_sign(determinant,edet)
        if detsign <= 0:
            return {'status':'NO_ROOT','reason':'nonpositive Gram determinant'}
        d = [x.sqrt() for x in ds]
        cof = [[1-c*c,b*c-a,a*c-b],
               [b*c-a,1-b*b,a*b-c],
               [a*c-b,a*b-c,1-a*a]]
        nums = [sum((cof[i][j]*d[j] for j in range(3)),arb(0)) for i in range(3)]
        exnums = [None]*3
        if any(not (x>0 or x<0) for x in nums):
            if exact and all(self.exact_cell_r2.get(n) is not None for _,n in pairs):
                erho = 1/(4*sp.sin(sp.pi/p)**2)
                ed = [sp.sqrt(self.exact_cell_r2[n]-erho) for _,n in pairs]
                ecof = [[1-ec*ec,eb*ec-ea,ea*ec-eb],
                        [eb*ec-ea,1-eb*eb,ea*eb-ec],
                        [ea*ec-eb,ea*eb-ec,1-ea*ea]]
                exnums = [sum(ecof[i][j]*ed[j] for j in range(3)) for i in range(3)]
        signs = [self.algebraic_sign(x,y) for x,y in zip(nums,exnums)]
        if min(signs)<0:
            return {'status':'NO_ROOT','reason':'centre outside ray cone'}
        r2 = rho + sum((d[i]*nums[i] for i in range(3)),arb(0))/determinant
        if 0 in signs:
            # Zero coefficient puts the unique centre on its opposite facet.
            # A positive definite Gram matrix makes the centre unique.
            return {'status':'DEGENERATE','R':decimal_bounds(r2.sqrt())}
        if not all(r2 > e.r2 for e in es):
            raise Undecided('root not strictly above every facet')
        return {'status':'ROOT','R':decimal_bounds(r2.sqrt())}

    def long_cycle(self,p,pairs,es,rho,ds):
        # u=1/(R²-rho²), increasing toward the maximal-facet boundary.
        # g(0)<0, and at the boundary one angle is pi and at least three
        # other angles are strictly greater than pi/3. Thus g>0 there.
        boundary = min(endpoints(1/(e.r2-rho))[0] for e in es)
        lo,hi = Fraction(0),boundary
        def g(u):
            u = ball(u)
            vals = []
            for i,e in enumerate(es):
                A,B = ds[i-1],ds[i]
                cos = (e.cosine-(A*B).sqrt()*u)/((1-A*u)*(1-B*u)).sqrt()
                vals.append(acos_clip(cos))
            return sum(vals,arb(0))-2*arb.pi()
        # The lower rational approximation to the exact boundary is only
        # accepted after its positive sign is certified. No fixed offset.
        if not g(hi)>0:
            raise Undecided('positive finite closure endpoint not certified')
        for iteration in range(400):
            mid = (lo+hi)/2
            v = g(mid)
            if v<0:
                lo=mid
            elif v>0:
                hi=mid
            else:
                # An exact dyadic root can hit a midpoint. Test a bracket
                # around it, retaining strict signs as the only authority.
                left,right=(lo+mid)/2,(mid+hi)/2
                if g(left)<0 and g(right)>0:
                    lo,hi=left,right
                else:
                    raise Undecided('closure midpoint undecided')
            if lo>0:
                r = (rho+1/hull(lo,hi)).sqrt()
                rl,rh=endpoints(r)
                if rh-rl < Fraction(1,10**30):
                    return {'status':'ROOT','R':decimal_bounds(r)}
        raise Undecided('closure bisection exhausted')


def write_json(path,obj):
    Path(path).write_text(json.dumps(obj,sort_keys=True,separators=(',',':'))+'\n')


def run(edges,cell_r2,exact_cell_r2,out):
    out=Path(out);out.mkdir(parents=True,exist_ok=True)
    t=time.monotonic()
    cycles=enumerate_cycles(edges)
    solver=Solver(edges,cell_r2,exact_cell_r2)
    records=[];intervals=[];counts=Counter()
    for i,(p,pairs) in enumerate(cycles):
        try:
            result=solver.solve(p,pairs)
        except Exception:
            print('FAILED CYCLE',i,p,pairs,flush=True)
            raise
        counts[result['status']]+=1
        result.update(p=p,word=pairs)
        records.append(result)
        if result['status']=='ROOT':
            intervals.append([*result['R'],i])
        if i%1000==0:
            print('cycles',i,dict(counts),flush=True)
    intervals.sort(key=lambda x:(Fraction(x[0]),Fraction(x[1]),x[2]))
    write_json(out/'cycles.json',records)
    write_json(out/'omega.json',{'intervals':intervals})
    summary={'cycles':len(cycles),'counts':dict(counts),'words':len(edges),
             'omega_intervals':len(intervals),
             'omega_sha256':hashlib.sha256((out/'omega.json').read_bytes()).hexdigest(),
             'elapsed_seconds':time.monotonic()-t,'undecided':0}
    write_json(out/'stage1-result.json',summary)
    print(json.dumps(summary,indent=2),flush=True)
    return summary
