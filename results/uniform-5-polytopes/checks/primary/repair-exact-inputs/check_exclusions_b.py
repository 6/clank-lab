"""Independent exact acceptance for listed S1 exclusions.

Does not import exact_angles/exact_inputs or the primary checker. Uses a
real/imaginary phase recurrence and explicit adjugate rows, instead of
minimal-polynomial complex products and symbolic replaced-column determinants.
"""
from collections import Counter
from functools import lru_cache
from decimal import Decimal
import argparse
import json
from pathlib import Path
import sympy as sp
from flint import arb, ctx
from check_inputs_b import check, zero
from exact_source import evaluate, require, constructions, consumer_ball


@lru_cache(None)
def flat(cosines):
    total = sum((evaluate(c).acos() for c in cosines), arb(0))
    require(arb.pi() < total and total < 3*arb.pi(), 'phase winding')
    re, im = sp.Integer(1), sp.Integer(0)
    for c in cosines:
        s = sp.sqrt(1-c*c)
        re, im = sp.expand(re*c-im*s), sp.expand(im*c+re*s)
    return zero(re-1) and zero(im)


@lru_cache(None)
def degenerate(p, radii, cosines):
    a, b, c = cosines[1], cosines[0], cosines[2]
    determinant = 1+2*a*b*c-a*a-b*b-c*c
    require(not zero(determinant), 'singular independent Gram')
    rho = 1/(4*sp.sin(sp.pi/p)**2)
    d = [sp.sqrt(sp.factor(r-rho)) for r in radii]
    rows = ((1-c*c, b*c-a, a*c-b), (b*c-a, 1-b*b, a*b-c), (a*c-b, a*b-c, 1-a*a))
    return any(zero(sum(x*y for x, y in zip(row, d))) for row in rows)


def authenticate_table(facets,pmax,records):
    originals,_ = constructions()
    expected = set()
    for name in originals:
        allowed = True
        if name.startswith('antiprism-prism-'):
            allowed = int(name.split('-')[-1]) <= pmax
        elif name.startswith('duoprism-'):
            allowed = all(int(t) <= pmax for t in name.split('-')[1:])
        if allowed:
            expected.add(name)
    require(isinstance(facets,list) and len(facets) == len(expected), 'live facet count')
    actual = {f['name']:f for f in facets}
    require(len(actual) == len(facets) and set(actual) == expected, 'live facet set')
    for name,f in actual.items():
        R,words = records[name]
        require(Counter(f['aliases']) == Counter(originals[name]['aliases']), 'live alias set')
        rb = consumer_ball(f['R'])
        require(rb.is_finite() and rb > 0 and rb.contains(evaluate(R).sqrt()), 'independent live radius containment')
        seen = set()
        for p,A,B,mid,rad in f['orbits']:
            key=p,A,B
            require(type(p) is int and A <= B and key in words and key not in seen, 'live incident word')
            seen.add(key)
            ab = consumer_ball([mid,rad])
            require(ab.is_finite() and ab > 0 and ab < arb.pi() and 9*ab > 2*arb.pi(), 'live depth bound')
            require(ab.contains(evaluate(words[key]).acos()), 'independent live word containment')
        require(seen == words.keys(), 'live word completeness')
    return len(actual)


def authenticate(cycles, ff, bb, pmax, certificate, facets=None):
    records, cells = check(certificate)
    if facets is None:
        facets=json.loads(Path('cert_facets4_p%d.json'%pmax).read_text())
    authenticate_table(facets,pmax,records)
    require(ff['pmax'] == bb['pmax'] == pmax, 'pmax')
    require(not ff['failed'] and not bb['unhandled'], 'unproved exclusion')
    f, b = ff['flat'], bb['degenerate']
    require(isinstance(f, list) and isinstance(b, list), 'list format')
    require(len(f) == len(set(f)) and len(b) == len(set(b)) and not set(f)&set(b), 'unique disjoint exclusions')
    require(all(type(i) is int and 0 <= i < len(cycles) for i in f+b), 'index')
    for i in f+b:
        r = cycles[i]; k = len(r['facets'])
        require(3 <= k <= 8 and len(r['cells']) == k and type(r['p']) is int and 3 <= r['p'] <= 16, 'cycle word')
        cosines = []
        for j, K in enumerate(r['facets']):
            require(K in records, 'unknown exact facet')
            R, words = records[K]
            if K.startswith('antiprism-prism-'):
                require(int(K.split('-')[-1]) <= pmax, 'antiprism parameter range')
            if K.startswith('duoprism-'):
                require(max(map(int, K.split('-')[1:])) <= pmax, 'duoprism parameter range')
            key = (r['p'], *sorted((r['cells'][j-1], r['cells'][j])))
            require(key in words, 'uncertified incident pair')
            cosines.append(words[key])
        if i in f:
            require(flat(tuple(sorted(cosines, key=str))), 'false independent flat exclusion')
        else:
            require(k == 3 and r['status'] == 'ROOT' and len(r['R']) == 1, 'one boundary root')
            lo, hi = map(Decimal, r['R'][0])
            require(lo.is_finite() and hi.is_finite() and 0 < lo <= hi, 'root interval')
            require(degenerate(r['p'], tuple(cells[c] for c in r['cells']), tuple(cosines)), 'false independent degenerate exclusion')
    return dict(checker='B', status='PASS', flat=len(f), degenerate=len(b))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('directory', type=Path)
    p.add_argument('pmax', type=int)
    a = p.parse_args(); ctx.prec = 256
    def read(name):
        return json.loads((a.directory/name).read_text())
    cert = json.loads((Path(__file__).resolve().parent/'inputs.json').read_text())
    print(json.dumps(authenticate(read('cert_stage1_5d_p%d.json'%a.pmax), read('exact_flat_p%d.json'%a.pmax),
                                  read('exact_boundary_p%d.json'%a.pmax), a.pmax, cert, read('cert_facets4_p%d.json'%a.pmax)), sort_keys=True))


if __name__ == '__main__':
    main()
