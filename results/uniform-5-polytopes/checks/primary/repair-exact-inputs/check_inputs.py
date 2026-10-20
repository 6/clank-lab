"""Primary exact-input checker. No exclusion search or float geometry import."""
from functools import lru_cache
import argparse
import json
from pathlib import Path
import sympy as sp
from flint import ctx
from exact_source import constructions, occurrence_words, expression, evaluate, require


@lru_cache(None)
def zero(e):
    e = sp.factor(sp.trigsimp(sp.cancel(e)))
    if e == 0:
        return True
    if e.is_Rational:
        return False
    x = sp.Dummy('x')
    return sp.minimal_polynomial(e, x) == x


@lru_cache(None)
def word_guard(R, p, ra, rb, c):
    """Authenticate c to the positive-branch word-radius formula exactly.

    Intervals only prove strict signs. Equality uses an algebraic residual.
    With D=R-rho², a=ra-rho², b=rb-rho², positive a,b,D-a,D-b,
    c=(sqrt(ab)-sqrt((D-a)(D-b)))/D iff
    (sqrt(ab)-D*c)^2=(D-a)(D-b) and sqrt(ab)-D*c>0.
    """
    rho = 1/(4*sp.sin(sp.pi/p)**2)
    D, a, b = (sp.factor(x-rho) for x in (R, ra, rb))
    require(all(evaluate(x) > 0 for x in (a, b, D-a, D-b)), 'positive word-radius branches')
    u = sp.sqrt(sp.factor(a*b))-D*c
    require(evaluate(u) > 0, 'wrong square-root branch')
    # Expanded form avoids a second, unnecessarily nested radical.
    residual = D*c*c - 2*c*sp.sqrt(sp.factor(a*b)) + a+b-D
    require(zero(residual), 'cosine differs from exact word-radius expression')
    require(evaluate(c) > -1 and evaluate(c) < 1, 'nonconvex angle')


def check(data):
    ctx.prec = 256
    require(data['schema'] == 'exact-word-inputs-v1', 'exact input schema')
    source, cells = constructions()
    require(set(data['cell_radius_squared']) == set(cells), 'exact cell radius inventory')
    parsed_cells = {c: expression(e) for c, e in data['cell_radius_squared'].items()}
    for c in cells:
        require(zero(parsed_cells[c]-cells[c]), 'cell radius construction: '+c)
    records = data['records']
    require(len(records) == len(source) and {r['name'] for r in records} == set(source), 'exact facet inventory')
    out = {}
    for r in records:
        name = r['name']; s = source[name]
        R = expression(r['radius_squared'])
        require(zero(R-s['radius_squared']), 'facet radius construction: '+name)
        expected = occurrence_words(s)
        words = {(w['p'], w['A'], w['B']): w for w in r['words']}
        require(len(words) == len(r['words']) and set(words) == set(expected), 'certified incident word inventory')
        cosines = {}
        for key, w in words.items():
            p, a, b = key
            require(type(p) is int and p >= 3 and a <= b, 'canonical incident word')
            require(type(w['multiplicity']) is int and w['multiplicity'] == expected[key], 'occurrence multiplicity')
            c = expression(w['cosine'])
            word_guard(R, p, parsed_cells[a], parsed_cells[b], c)
            cosines[key] = c
        out[name] = (R, cosines)
    return out, parsed_cells


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('certificate', type=Path)
    a = p.parse_args()
    records, cells = check(json.loads(a.certificate.read_text()))
    print(json.dumps(dict(status='PASS', facets=len(records), cells=len(cells),
                          words=sum(len(w) for _, w in records.values())), sort_keys=True))


if __name__ == '__main__':
    main()
