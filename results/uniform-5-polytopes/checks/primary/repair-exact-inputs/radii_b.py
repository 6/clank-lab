"""Independent radius authentication from construction equations.

Uses SymPy Gram solves, not the library's coefficient-pair solver. Snub
radii satisfy the eliminated neighbor-circle equation with a uniquely
isolated real branch. Product and exceptional formulas fix unit-edge scale.
"""
from functools import lru_cache
import sympy as sp
from exact_source import evaluate, require

DIAGRAMS = {
    'A3': ((0,1,3),(1,2,3)), 'B3': ((0,1,3),(1,2,4)), 'H3': ((0,1,5),(1,2,3)),
    'A4': ((0,1,3),(1,2,3),(2,3,3)), 'B4': ((0,1,3),(1,2,3),(2,3,4)),
    'D4': ((0,1,3),(1,2,3),(1,3,3)), 'F4': ((0,1,3),(1,2,4),(2,3,3)),
    'H4': ((0,1,5),(1,2,3),(2,3,3)),
}
LABELS = {
    'A3': {'001':'tet','100':'tet','010':'oct','011':'tut','110':'tut','101':'co','111':'toe'},
    'B3': {'001':'cube','100':'oct','010':'co','011':'tic','110':'toe','101':'sirco','111':'girco'},
    'H3': {'001':'ico','100':'doe','010':'id','011':'tid','110':'ti','101':'srid','111':'grid'},
}


@lru_cache(None)
def gram_radius(group, mask):
    n = int(group[1]); G = sp.eye(n)
    for i,j,m in DIAGRAMS[group]:
        G[i,j] = G[j,i] = -sp.cos(sp.pi/m)
    b = sp.Matrix([sp.Rational(int(x),2) for x in mask])
    x = G.inv()*b
    require(all(sp.simplify(e) == 0 for e in G*x-b), 'independent Gram solution residual')
    return sp.factor((b.T*x)[0])


def polygon(p):
    return 1/(4*sp.sin(sp.pi/p)**2)


@lru_cache(None)
def known_cells():
    out = {}
    for g,masks in LABELS.items():
        for mask,label in masks.items():
            R = gram_radius(g,mask)
            if label in out:
                require(sp.simplify(R-out[label]) == 0, 'independent repeated cell radius')
            out[label] = R
    return out


def cell_guard(name, R, zero):
    if name in ('snic','snid'):
        r = sp.Symbol('r')
        if name == 'snic':
            P = 32*r**3-80*r**2+44*r-7
        else:
            P = 4096*r**6-27648*r**5+47104*r**4-35776*r**3+13872*r**2-2696*r+209
        # Eliminate z from 16(1-z)(1-2z)^2=c², R=z/(4z-1).
        # R>1 corresponds exactly to 1/4<z<1/3. The conjugate H3
        # equation has no root there. Sturm counting certifies uniqueness.
        require(sp.Poly(P,r).count_roots(1,sp.oo) == 1, 'unique snub radius branch')
        require(evaluate(R) > 1 and zero(P.subs(r,R)), 'independent snub radius equation')
        return
    if name.startswith('P'):
        expected = polygon(int(name[1:]))+sp.Rational(1,4)
    elif name.startswith('A'):
        n = int(name[1:]); t = sp.cos(sp.pi/n)
        # Explicit antiprism coordinates: circle radius 1/(2 sin(pi/n))
        # and squared height 1-4r² sin(pi/(2n))².
        radial = polygon(n)
        expected = radial+(1-4*radial*sp.sin(sp.pi/(2*n))**2)/4
    else:
        require(name in known_cells(), 'unknown independent cell construction')
        expected = known_cells()[name]
    require(zero(R-expected), 'independent cell construction radius: '+name)


def facet_guard(name, R, cells, zero):
    if name[:2] in ('A4','B4','D4','F4','H4'):
        expected = gram_radius(name[:2],name[2:])
    elif name in ('sadi','gap'):
        # Radius-one 600-cell has squared unit-edge length phi^-2.
        expected = ((1+sp.sqrt(5))/2)**2
    elif name.startswith('pr-'):
        expected = cells[name[3:]]+sp.Rational(1,4)
    elif name.startswith('antiprism-prism-'):
        n = int(name.split('-')[-1])
        expected = cells['A'+str(n)]+sp.Rational(1,4)
    elif name.startswith('duoprism-'):
        p,q = map(int,name.split('-')[1:])
        expected = polygon(p)+polygon(q)
    else:
        raise ValueError('unknown independent facet construction')
    require(zero(R-expected), 'independent facet construction radius: '+name)
