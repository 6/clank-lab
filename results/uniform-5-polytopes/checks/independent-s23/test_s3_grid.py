"""Grid proof controls: dyadic endpoints, boundaries, fallback and matching."""
from fractions import Fraction
from itertools import product
from random import Random
from flint import arb,ctx
from s3_grid import covered_cells,endpoint_floor,PointIndex
from s3_arith import apart,perfect_matching


def main():
    ctx.prec=320
    for k in range(-32,33):
        for shift in range(-8,9):
            x=arb(k)*arb(2)**shift
            exact=Fraction(k)*Fraction(2)**shift
            if not (endpoint_floor(x,2)==(4*exact).__floor__()):
                raise AssertionError()
    if not (covered_cells((arb('0.25'),))==((1,),)):
        raise AssertionError()
    if not (covered_cells((arb('0.25','1e-60'),))==((0,),(1,))):
        raise AssertionError()
    if not (covered_cells((arb('-0.25','1e-60'),))==((-2,),(-1,))):
        raise AssertionError()
    if not (set(covered_cells((arb(0,'1e-60'),arb(0,'1e-60'))))==set(product((-1,0),repeat=2))):
        raise AssertionError()
    if not (covered_cells((arb(0,100),)) is None):
        raise AssertionError()
    if not (covered_cells((arb('nan'),)) is None):
        raise AssertionError()
    if not (covered_cells((arb('inf'),)) is None):
        raise AssertionError()
    if not (covered_cells((arb(1),),max_cells=0) is None):
        raise AssertionError()
    # Exhaustive 1D intervals around dyadic boundaries: every intersecting
    # exact rational pair MUST be a candidate, including endpoint contact.
    specs=[(Fraction(k,8),Fraction(r,16)) for k in range(-8,9) for r in range(3)]
    points=[(arb(str(c.numerator))/c.denominator+arb(0,str(r.numerator))/r.denominator,)
            for c,r in specs]
    index=PointIndex(points)
    checks=0
    for i,(c,r) in enumerate(specs):
        candidates=set(index.candidates(points[i]))
        for j,(d,s) in enumerate(specs):
            if c-r<=d+s and d-s<=c+r:
                if not (j in candidates):
                    raise AssertionError()
            if not apart(points[i],points[j]):
                if not (j in candidates):
                    raise AssertionError()
            checks+=1
    # Nonfinite/wide targets are ALWAYS considered; broad queries see ALL.
    fallback=PointIndex([(arb(0),),(arb(0,100),),(arb('nan'),)])
    if not ({1,2}<=set(fallback.candidates((arb(20),)))):
        raise AssertionError()
    if not (set(fallback.candidates((arb(0,100),)))=={0,1,2}):
        raise AssertionError()
    if not (set(fallback.candidates((arb('nan'),)))=={0,1,2}):
        raise AssertionError()
    # Complete matching graph is unchanged by covered-cell indexing.
    rng=Random(314159)
    for dim in (1,2,4,5):
        for _ in range(100):
            target=[tuple(arb(rng.randrange(-8,9))/4+arb(0,'1e-60') for _ in range(dim)) for _ in range(8)]
            source=[tuple(arb(rng.randrange(-8,9))/4+arb(0,'1e-60') for _ in range(dim)) for _ in range(5)]
            ix=PointIndex(target)
            full=[[j for j,q in enumerate(target) if not apart(p,q)] for p in source]
            indexed=[[j for j in ix.candidates(p) if not apart(p,target[j])] for p in source]
            if not (full==indexed):
                raise AssertionError()
            if not (perfect_matching(full,len(target))==perfect_matching(indexed,len(target))):
                raise AssertionError()
    # Widely separated large point sets give constant-size candidate lists;
    # this is a count check, not an elapsed-time performance assertion.
    large=[(arb(2*i),arb(0),arb(0),arb(0),arb(0)) for i in range(14400)]
    ix=PointIndex(large)
    for i in (0,1,7200,14399):
        if not (list(ix.candidates(large[i]))==[i]):
            raise AssertionError()
    print(f'PASS dyadic covered-grid: {checks} interval pairs, 400 complete matching graphs, boundary/fallback/14400-point controls')

if __name__=='__main__':main()
