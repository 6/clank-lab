"""Authenticated algebraic operands and exact S1 exclusion acceptance.

No floating orbit/incidence matching participates. Exact constructions are
replayed by the small input checker; incident words select the positive-root
radius formula. The JSON is a certificate proposal, never trusted by hash.
"""
from functools import lru_cache
from fractions import Fraction
from pathlib import Path
import json
import os
import sys
import sympy as sp
from flint import arb, ctx

TARGET = Path(os.environ.get('U5_EXACT_INPUT_ROOT', Path(__file__).resolve().parents[1]))
REPAIR = TARGET / 'repair-exact-inputs'
sys.path.insert(0, str(REPAIR))
from check_inputs import check, zero
from exact_source import evaluate, require, constructions, consumer_ball, in_family


class ExactInputs:
    def __init__(self, records, cells, pmax):
        self.records, self.cells, self.pmax = records, cells, pmax

    def radius2(self, name):
        require(name in self.records, 'uncertified facet construction: '+name)
        return self.records[name][0]

    def cell_radius2(self, name):
        require(name in self.cells, 'uncertified cell construction: '+name)
        return self.cells[name]

    def cosine(self, name, p, a, b):
        require(type(p) is int and 3 <= p <= 16, 'polygon outside certified range')
        self.radius2(name)
        words = self.records[name][1]
        # P bounds the product-family parameters. Fixed Wythoff/prism
        # types can contain decagons even at P6; do not discard them.
        if name.startswith('antiprism-prism-'):
            require(int(name.split('-')[-1]) <= self.pmax, 'antiprism parameter outside P')
        if name.startswith('duoprism-'):
            require(max(map(int, name.split('-')[1:])) <= self.pmax, 'duoprism parameters outside P')
        key = (p, *sorted((a, b)))
        require(key in words, 'uncertified incident word: '+repr((name, key)))
        return words[key]

    def sides(self, rec):
        facets, cells = rec['facets'], rec['cells']
        require(len(facets) == len(cells) and 3 <= len(cells) <= 8, 'invalid cycle word')
        return tuple(self.cosine(f, rec['p'], cells[i-1], cells[i]) for i, f in enumerate(facets))


@lru_cache(None)
def load_authenticated(pmax=16):
    require(type(pmax) is int and 3 <= pmax <= 16, 'exact input range is P <= 16')
    saved = ctx.prec
    try:
        ctx.prec = 256
        records, cells = check(json.loads((REPAIR / 'inputs.json').read_text()))
        return ExactInputs(records, cells, pmax)
    finally:
        ctx.prec = saved


@lru_cache(None)
def rational_angle(c):
    # A numerical proposal is harmless only because its exact residual is
    # checked. In particular 10^-40 is never rounded to an exact zero.
    a = evaluate(c).acos()/arb.pi()
    fr = Fraction(float(a)).limit_denominator(240)
    if not 0 < fr < 1:
        return None
    proposed = sp.cos(sp.pi*sp.Rational(fr.numerator, fr.denominator))
    return fr if zero(c-proposed) else None


@lru_cache(None)
def prove_flat(cosines):
    total = sum((evaluate(c).acos() for c in cosines), arb(0))
    require(total > arb.pi() and total < 3*arb.pi(), 'flat winding branch')
    rational = Fraction(0)
    irr = []
    for c in cosines:
        r = rational_angle(c)
        if r is None:
            irr.append(c)
        else:
            rational += r
    if not irr:
        return rational == 2
    z = sp.prod(c+sp.I*sp.sqrt(1-c*c) for c in irr)
    a = sp.pi*(2-sp.Rational(rational.numerator, rational.denominator))
    return zero(sp.expand(z-sp.cos(a)-sp.I*sp.sin(a)))


def gram(cosines):
    G = sp.eye(3)
    for i, c in enumerate(cosines):
        G[i-1, i] = G[i, i-1] = c
    return G


@lru_cache(None)
def prove_degenerate(p, cells_r2, cosines):
    """Nonsingular Gram and one zero opposite coefficient suffice.

    For an admissible centre, its coordinates in the three ray directions
    are sigma*G^-1*d with sigma>0. A zero coordinate puts it on the opposite
    facet hyperplane, contradicting strict interiority. No numerical radius
    equality or sign of the other coefficients is an equality premise.
    """
    G = gram(cosines)
    det = sp.expand(G.det())
    require(not zero(det), 'singular Gram matrix')
    rho = 1/(4*sp.sin(sp.pi/p)**2)
    d = sp.Matrix([sp.sqrt(sp.factor(r-rho)) for r in cells_r2])
    for j in range(3):
        M = G.copy(); M[:, j] = d
        if zero(sp.expand(M.det())):
            return True
    return False


def boundary_candidate(p, cells_r2, cosines):
    """Outward arithmetic can only select an exact test, never delete a case."""
    rho = evaluate(1/(4*sp.sin(sp.pi/p)**2))
    d = [(evaluate(r)-rho).sqrt() for r in cells_r2]
    # Off-diagonal entries in ray-index order: 01=c1,02=c0,12=c2.
    a, b, c = map(evaluate, (cosines[1], cosines[0], cosines[2]))
    cof = ((1-c*c, b*c-a, a*c-b), (b*c-a, 1-b*b, a*b-c), (a*c-b, a*b-c, 1-a*a))
    return any(sum((x*y for x, y in zip(row, d)), arb(0)).contains(0) for row in cof)


def exclusion_lists(cycles, pmax):
    """Replay exact flat/degenerate exclusions on the actual S1 cycle words."""
    inputs = load_authenticated(pmax)
    flat, boundary, failed, identities = [], [], [], {}
    saved = ctx.prec
    try:
        ctx.prec = 256
        for i, rec in enumerate(cycles):
            cosines = inputs.sides(rec)
            ordered = tuple(sorted(cosines, key=str))
            total = sum((evaluate(c).acos() for c in cosines), arb(0))
            if (total-2*arb.pi()).contains(0):
                ok = prove_flat(ordered)
                identities[(tuple(map(str, ordered)), 'word-radius')] = ok
                (flat if ok else failed).append(i)
                continue
            if rec['status'] != 'ROOT' or len(cosines) != 3:
                continue
            radii = tuple(inputs.cell_radius2(c) for c in rec['cells'])
            if boundary_candidate(rec['p'], radii, cosines) and prove_degenerate(rec['p'], radii, cosines):
                require(len(rec['R']) == 1, 'degenerate exclusion requires one root interval')
                boundary.append(i)
    finally:
        ctx.prec = saved
    return flat, boundary, failed, identities


def authenticate_table(facets, pmax, inputs=None):
    """Authenticate the live S1 library and its entire word inventory.

    Containment is used only for interval enclosure of a known exact
    geometric value; it never asserts equality of two algebraic operands.
    """
    inputs = inputs or load_authenticated(pmax)
    originals, _ = constructions()
    expected = {n for n in originals if in_family(n,pmax)}
    require(isinstance(facets,list) and len(facets) == len(expected), 'complete live facet inventory')
    names = [f['name'] for f in facets]
    require(len(set(names)) == len(names) and set(names) == expected, 'live canonical facet names')
    saved = ctx.prec
    try:
        ctx.prec = 256
        for f in facets:
            n = f['name']; R, words = inputs.records[n]
            aliases = f['aliases']
            require(isinstance(aliases,list) and len(aliases) == len(set(aliases)) and
                    set(aliases) == set(originals[n]['aliases']), 'certified alias inventory')
            radius = consumer_ball(f['R'])
            require(radius.is_finite() and radius > 0 and radius.contains(evaluate(R).sqrt()),
                    'live facet radius does not enclose exact construction')
            actual = {}
            for row in f['orbits']:
                require(len(row) == 5, 'live word format')
                p,a,b,mid,rad = row; key = p,a,b
                require(type(p) is int and a <= b and key not in actual, 'duplicate or noncanonical live word')
                actual[key] = consumer_ball([mid,rad])
            require(set(actual) == set(words), 'complete certified live word inventory')
            for key, c in words.items():
                al = actual[key]
                require(al.is_finite() and 0 < al and al < arb.pi() and 9*al > 2*arb.pi(), 'live S1 depth branch')
                require(al.contains(evaluate(c).acos()), 'live angle does not enclose certified exact word')
    finally:
        ctx.prec = saved
    return dict(facets=len(facets),words=sum(len(inputs.records[n][1]) for n in names))


def authenticate_exclusions(cycles, flat, boundary, pmax=16, *, facets=None):
    """Fail closed on every supplied deletion; usable by FILTER and Omega.

    The proof is rerun on actual cycle words/operands. Neither an input hash,
    a status marker, an index list, nor an interval overlap is accepted as
    proof. Root coverage/completeness remains the separate S1 guard's duty.
    """
    require(flat['pmax'] == pmax and boundary['pmax'] == pmax, 'exclusion polygon bound')
    require(not flat['failed'] and not boundary['unhandled'], 'unproved exact exclusions')
    ff, bb = flat['flat'], boundary['degenerate']
    require(isinstance(ff, list) and isinstance(bb, list), 'exclusion list format')
    require(len(ff) == len(set(ff)) and len(bb) == len(set(bb)), 'duplicate exclusion')
    require(not set(ff) & set(bb), 'overlapping exclusions')
    require(all(type(i) is int and 0 <= i < len(cycles) for i in ff+bb), 'exclusion index')
    inputs = load_authenticated(pmax)
    if facets is None:
        facets = json.loads(Path('cert_facets4_p%d.json'%pmax).read_text())
    authenticate_table(facets,pmax,inputs)
    saved = ctx.prec
    try:
        ctx.prec = 256
        for i in ff:
            cosines = tuple(sorted(inputs.sides(cycles[i]), key=str))
            require(prove_flat(cosines), 'false flat exclusion: '+str(i))
        for i in bb:
            rec = cycles[i]
            require(rec['status'] == 'ROOT' and len(rec['R']) == 1 and len(rec['facets']) == 3,
                    'degenerate exclusion requires one triangle root interval')
            # The interval is a coverage input, not an equality premise.
            from decimal import Decimal
            lo, hi = map(Decimal, rec['R'][0])
            require(lo.is_finite() and hi.is_finite() and 0 < lo <= hi, 'degenerate root interval')
            cosines = inputs.sides(rec)
            radii = tuple(inputs.cell_radius2(c) for c in rec['cells'])
            require(prove_degenerate(rec['p'], radii, cosines), 'false degenerate exclusion: '+str(i))
    finally:
        ctx.prec = saved
    return set(ff), set(bb)
