"""Second checker: twice-squared residual and exact algebraic field embedding.

Shares authoritative exact LIB constructions, but neither primary checker,
word guard, nor exclusion generator. Interval signs select positive roots;
a zero-containing interval is never an equality. This is independent checking
of the new arithmetic/link contract, not a third library classification.
"""
from collections import Counter
from functools import lru_cache
import argparse
import json
from pathlib import Path
import sympy as sp
from flint import ctx
from exact_source import constructions, expression, evaluate, require
from radii_b import cell_guard, facet_guard


@lru_cache(None)
def zero(e):
    e = sp.simplify(sp.expand(e))
    if e == 0:
        return True
    if e.is_Rational:
        return False
    roots = e.atoms(sp.CRootOf)
    if len(roots) == 1:
        # A rational function of one isolated algebraic root can be checked
        # directly in Q[t]/minimal_polynomial. Avoid an expensive primitive
        # element search for the snub radius equations.
        root = next(iter(roots)); t = sp.Dummy('t')
        num, den = sp.cancel(e.xreplace({root:t})).as_numer_denom()
        try:
            P = sp.Poly(root.poly.as_expr().subs(root.poly.gen,t),t,domain=sp.QQ)
            N, D = sp.Poly(num,t,domain=sp.QQ), sp.Poly(den,t,domain=sp.QQ)
        except (sp.PolynomialError, sp.polys.polyerrors.CoercionFailed):
            pass
        else:
            if P.is_irreducible:
                require(not D.rem(P).is_zero, 'zero algebraic denominator')
                return N.rem(P).is_zero
    return all(c == 0 for c in sp.polys.numberfields.to_number_field(e).coeffs())


@lru_cache(None)
def word_guard(R, p, ra, rb, c):
    rho = 1/(4*sp.sin(sp.pi/p)**2)
    D, A, B = (sp.factor(x-rho) for x in (R, ra, rb))
    require(all(evaluate(x) > 0 for x in (A, B, D-A, D-B)), 'word branch domain')
    # Eliminate the remaining radical independently of checker A. Recover
    # its sign explicitly, so squaring cannot accept the conjugate branch.
    h = sp.factor(D*c*c+A+B-D)
    require(zero(4*c*c*A*B-h*h), 'twice-squared exact word residual')
    if zero(c):
        require(zero(h), 'zero-cosine residual')
    else:
        require(evaluate(c)*evaluate(h) > 0, 'sign lost in second squaring')
    require(evaluate(sp.sqrt(sp.factor(A*B))-D*c) > 0, 'positive difference branch')
    require(-1 < evaluate(c) and evaluate(c) < 1, 'convex cosine branch')


def check(data):
    ctx.prec = 256
    require(data['schema'] == 'exact-word-inputs-v1', 'schema')
    originals, original_cells = constructions()
    cells = data['cell_radius_squared']
    require(cells.keys() == original_cells.keys(), 'radius names')
    cells = {k: expression(v) for k, v in cells.items()}
    for k in cells:
        cell_guard(k, cells[k], zero)
    records = data['records']
    require(len(records) == len(originals) and {r['name'] for r in records} == originals.keys(), 'facet names')
    result = {}
    for r in records:
        original = originals[r['name']]
        R = expression(r['radius_squared'])
        facet_guard(r['name'], R, cells, zero)
        inc = original['incidences']
        # Enumerate each local polygon's stored certified incident pair, and
        # independently check the intersection, rather than calling A's word
        # projection (which enumerates containing cells).
        words = Counter()
        for poly in inc['polygons']:
            i, j = poly['cells']
            require(i != j, 'distinct incident cells')
            C, E = inc['cells'][i], inc['cells'][j]
            require(set(C['neighbors']) & set(E['neighbors']) == set(poly['neighbors']), 'cell intersection')
            a, b = sorted((C['label'], E['label']))
            words[poly['p'], a, b] += 1
        actual = Counter((w['p'], w['A'], w['B']) for w in r['words'])
        require(actual == Counter(words.keys()), 'complete distinct words')
        parsed = {}
        for w in r['words']:
            p, a, b = w['p'], w['A'], w['B']
            require(type(p) is int and type(w['multiplicity']) is int and w['multiplicity'] == words[p,a,b], 'word occurrence')
            c = expression(w['cosine'])
            word_guard(R, p, cells[a], cells[b], c)
            parsed[p,a,b] = c
        result[r['name']] = R, parsed
    return result, cells


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('certificate', type=Path)
    a = p.parse_args()
    records, cells = check(json.loads(a.certificate.read_text()))
    print(json.dumps(dict(status='PASS', checker='B', facets=len(records), cells=len(cells),
                          words=sum(len(w) for _, w in records.values())), sort_keys=True))


if __name__ == '__main__':
    main()
