"""Authoritative exact constructions, not a numerical-to-exact index map.

The parabolic face theorem, exact exceptional supporting inequalities and
product face identities are implemented by the independent library. Replay
those constructions; never promote the frozen library JSON or its hash to a
geometric proof. Conventional labels/uniformity retain the LIB/R2 premises.
"""
from collections import Counter
from functools import lru_cache
from pathlib import Path
import sys
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
INDEPENDENT = ROOT.parent / 'independent-s1-b2'
sys.path.insert(0, str(INDEPENDENT))
from library import library_records, cell_radius_squared
from library_verify import check_incidences
from export import evaluate


def require(test, why):
    if not test:
        raise ValueError(why)


def expression(text):
    require(isinstance(text, str), 'exact expression must be a string')
    e = sp.sympify(text)
    require(not e.has(sp.Float) and not e.free_symbols, 'inexact or free algebraic operand')
    return e


@lru_cache(None)
def constructions():
    records = library_records()
    # Reconstruction checks exact parabolic incidence/radii, exceptional full
    # support inequalities/radii, and product incidences. Also check the entire
    # exported local face complex independently of word generation.
    check_incidences(dict(records=records, counts=dict(types=181, words=558, occurrences=1277)))
    labels = {w[k] for r in records for w in r['words'] for k in ('A', 'B')}
    return {r['name']: r for r in records}, {c: cell_radius_squared(c) for c in labels}


def occurrence_words(r):
    inc = r['incidences']
    cells = inc['cells']
    out = Counter()
    for p in inc['polygons']:
        edge = set(p['neighbors'])
        ids = [i for i, c in enumerate(cells) if edge <= set(c['neighbors'])]
        require(len(ids) == 2 and ids == sorted(p['cells']), 'incident cell pair')
        a, b = sorted(cells[i]['label'] for i in ids)
        out[p['p'], a, b] += 1
    return out


def certificate():
    records, cells = constructions()
    return dict(schema='exact-word-inputs-v1',
                cell_radius_squared={k: str(v) for k, v in sorted(cells.items())},
                records=[dict(name=r['name'], radius_squared=str(r['radius_squared']),
                              words=[dict(p=w['p'], A=w['A'], B=w['B'], multiplicity=w['multiplicity'],
                                          cosine=str(w['cos_alpha'])) for w in r['words']])
                         for r in records.values()])


def consumer_ball(pair):
    """Parse with the actual S1 consumer at its declared 160-bit precision."""
    from flint import ctx
    saved = ctx.prec
    try:
        if str(ROOT/'enum') not in sys.path:
            sys.path.insert(0, str(ROOT/'enum'))
        from cert_stage1_5d import ball
        ctx.prec = 160
        require(isinstance(pair, (list,tuple)) and len(pair) == 2, 'table ball format')
        require(all(isinstance(x,str) for x in pair), 'table ball strings')
        return ball(*pair)
    finally:
        ctx.prec = saved


def in_family(name, pmax):
    if name.startswith('antiprism-prism-'):
        return int(name.split('-')[-1]) <= pmax
    if name.startswith('duoprism-'):
        return max(map(int,name.split('-')[1:])) <= pmax
    return True
