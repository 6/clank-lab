"""Rigorous interval-covered dyadic grid: equality candidates only.

Every point enclosure occupies EVERY grid cell crossed by its coordinate
intervals, using exact dyadic Arb endpoints and integer arithmetic. Equal
exact points must share a cell in every coordinate. Disjoint covered-cell
sets therefore prove apartness; shared cells only propose candidates.

Nonfinite intervals, costly integer exponents or wide Cartesian products
fall back to ALL candidates. No rounded midpoint or fixed error tolerance
can omit a point. Existing outward apartness tests decide the shortlist.
"""
from itertools import product


def endpoint_floor(endpoint,power):
    """Exact floor(2**power * a) for an exact dyadic Arb endpoint a.

    None means only that this optimisation was declined. Endpoint mantissa
    and exponent are exact integers; no decimal conversion/rounding occurs.
    """
    if not endpoint.is_finite() or not endpoint.is_exact():return None
    try:mantissa,exponent=endpoint.man_exp()
    except (AttributeError,ValueError,OverflowError):return None
    m=int(mantissa);shift=int(exponent)+power
    if m==0:return 0
    if shift>=0:
        if abs(m).bit_length()+shift>16384:return None
        return m<<shift
    bits=-shift
    if bits>abs(m).bit_length():return 0 if m>0 else -1
    return m//(1<<bits)


def covered_cells(point,power=2,max_cells=256):
    """All floor(2**power*x) tuples compatible with the enclosure.

    The interval need not describe independent coordinate uncertainties:
    Cartesian coverage over-encloses all possible exact points safely.
    """
    bounds=[];count=1
    for x in point:
        if not x.is_finite():return None
        try:
            lo=endpoint_floor(x.lower(),power);hi=endpoint_floor(x.upper(),power)
        except (AttributeError,ValueError,OverflowError):return None
        if lo is None or hi is None or lo>hi:return None
        width=hi-lo+1
        if width>max_cells or count*width>max_cells:return None
        count*=width;bounds.append(range(lo,hi+1))
    return tuple(product(*bounds))


class PointIndex:
    """Certified superset of points which could equal a queried point."""
    def __init__(self,points,power=2,max_cells=256):
        self.points=points;self.power=power;self.max_cells=max_cells
        self.grid={};self.fallback=[]
        for i,p in enumerate(points):
            cells=covered_cells(p,power,max_cells)
            if cells is None:self.fallback.append(i)
            else:
                for cell in cells:self.grid.setdefault(cell,[]).append(i)
    def candidates(self,point):
        cells=covered_cells(point,self.power,self.max_cells)
        if cells is None:return range(len(self.points))
        found=set(self.fallback)
        for cell in cells:found.update(self.grid.get(cell,()))
        return sorted(found)
