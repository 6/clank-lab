"""Radius classes from the certified stage-1 output and a combinatorial closure filter.

A radius class is a connected component of the overlap graph of the certified root
intervals (conservative: overlaps only merge).  Filter (necessary condition): if facet K
occurs in P, each polygon orbit (p, cell a, cell b, alpha) of K lies in a polygon of P whose
cycle is in the same class and contains K as a side between cells a and b.  Cycles failing
this are removed, to a fixpoint.  Exact exclusion operand authentication and LIB/LINK remain required upstream
premises. Structural validation and inventory reconstruction here do not prove
those premises. usage: class_filter.py PMAX -> classes_pPMAX.json"""
import json, sys
from decimal import Decimal, InvalidOperation
import os
from pathlib import Path
import subprocess
import tempfile

def validated_interval(pair, index, allow_infinite=False):
    if not isinstance(pair, list) or len(pair) != 2 or any((type(x) is not str for x in pair)):
        raise ValueError(f'cycle {index}: malformed ROOT interval')
    try:
        lo, hi = map(Decimal, pair)
    except InvalidOperation as exc:
        raise ValueError(f'cycle {index}: invalid decimal endpoint') from exc
    if not lo.is_finite() or lo <= 0 or hi.is_nan() or (hi < lo):
        raise ValueError(f'cycle {index}: invalid interval order or radius')
    if not hi.is_finite() and (not (allow_infinite and hi == Decimal('Infinity'))):
        raise ValueError(f'cycle {index}: surviving non-finite interval')
    return (lo, hi)

def validate_inputs(cycles, flat, boundary, pmax):
    """Fail closed before skipping any record, including an excluded record.

    Structural validation does not authenticate an exact exclusion's operands.
    The exact-provenance checker must separately establish that implication;
    a digest of the two lists alone cannot do so.
    """
    if type(cycles) is not list or not cycles:
        raise ValueError('empty or malformed cycle inventory')
    excluded = []
    for record, key, incomplete in ((flat, 'flat', 'failed'), (boundary, 'degenerate', 'unhandled')):
        if type(record) is not dict or type(record.get('pmax')) is not int or record['pmax'] != pmax:
            raise ValueError('wrong or missing exclusion pmax')
        if type(record.get(incomplete)) is not list or record[incomplete]:
            raise ValueError('incomplete exact exclusion proofs')
        ids = record.get(key)
        if type(ids) is not list or any((type(i) is not int or not 0 <= i < len(cycles) for i in ids)):
            raise ValueError('invalid exclusion index')
        if len(set(ids)) != len(ids):
            raise ValueError('duplicate exclusion index')
        excluded.append(set(ids))
    flat_ids, deg = excluded
    if flat_ids & deg:
        raise ValueError('flat and degenerate exclusions overlap')
    intervals = []
    for i, record in enumerate(cycles):
        if type(record) is not dict or record.get('status') not in ('ROOT', 'NOROOT'):
            raise ValueError(f'cycle {i}: unresolved or malformed status')
        roots = record.get('R')
        if type(roots) is not list:
            raise ValueError(f'cycle {i}: malformed root list')
        if record['status'] == 'NOROOT':
            if roots or i in flat_ids or i in deg:
                raise ValueError(f'cycle {i}: NOROOT with intervals or exclusion')
            continue
        if not roots:
            raise ValueError(f'cycle {i}: ROOT without intervals')
        if i in deg and len(roots) != 1:
            raise ValueError(f'cycle {i}: degenerate exclusion requires exactly one certified root interval')
        for pair in roots:
            lo, hi = validated_interval(pair, i, allow_infinite=i in flat_ids)
            if i not in flat_ids and i not in deg:
                intervals.append((lo, hi, i))
    return intervals

def canonical_cycle(p, facets, cells):
    sides = [(f, cells[i - 1], cells[i]) for i, f in enumerate(facets)]
    versions = []
    for i in range(len(sides)):
        rotated = sides[i:] + sides[:i]
        versions.append(tuple(rotated))
        versions.append(tuple(((f, b, a) for f, a, b in reversed(rotated))))
    return (p, min(versions))

def validate_inventory(cycles, facets):
    """Regenerate the complete directed-cycle inventory from the supplied library.

    This establishes completeness relative to that library, not its geometric
    provenance. LIB/LINK must certify precisely this table (all occurrences,
    angle containment and the nine-angle depth bound). No count or list hash
    substitutes for reconstructing the canonical cycles here.
    """
    from flint import arb, ctx
    old_prec = ctx.prec
    try:
        from cert_stage1_5d import ball
        ctx.prec = 160
        words, sides = ({}, {})
        if type(facets) is not list or not facets:
            raise ValueError('empty facet library')
        names = set()
        for facet in facets:
            name = facet['name']
            if name in names:
                raise ValueError('duplicate facet name')
            names.add(name)
            for p, a, b, mid, rad in facet['orbits']:
                key = (name, p, tuple(sorted((a, b))))
                if key in words:
                    raise ValueError('duplicate facet word')
                alpha = ball(mid, rad)
                if not alpha.is_finite() or not alpha > 0 or (not 9 * alpha > 2 * arb.pi()):
                    raise ValueError('uncertified angle/depth bound')
                words[key] = alpha
                sides.setdefault(p, []).append((name, a, b, alpha))
                if a != b:
                    sides[p].append((name, b, a, alpha))
        actual = set()
        for record in cycles:
            p, fs, cs = (record['p'], record['facets'], record['cells'])
            if type(p) is not int or type(fs) is not list or type(cs) is not list or (not 3 <= len(fs) <= 8) or (len(fs) != len(cs)):
                raise ValueError('malformed cycle word')
            if any(((f, p, tuple(sorted((cs[i - 1], cs[i])))) not in words for i, f in enumerate(fs))):
                raise ValueError('cycle word absent from library')
            key = canonical_cycle(p, fs, cs)
            if key in actual:
                raise ValueError('duplicate canonical cycle')
            actual.add(key)
        expected = set()
        two_pi = 2 * arb.pi()
        for p, options in sides.items():

            def dfs(seq, total):
                if len(seq) >= 3 and seq[-1][2] == seq[0][1]:
                    expected.add(canonical_cycle(p, [s[0] for s in seq], [s[2] for s in seq]))
                if len(seq) == 8:
                    return
                for side in options:
                    if seq and side[1] != seq[-1][2]:
                        continue
                    following = total + side[3]
                    if following >= two_pi:
                        continue
                    dfs(seq + [side], following)
            dfs([], arb(0))
        if actual != expected:
            raise ValueError(f'incomplete cycle inventory: missing {len(expected - actual)}, unexpected {len(actual - expected)}')
    finally:
        ctx.prec = old_prec

def decimal_endpoint(value):
    """Exact decimal spelling without redundant fractional trailing zeros.

    Do not use Decimal.normalize(): it rounds to the ambient context.
    """
    text = str(value)
    if '.' in text and 'E' not in text and ('e' not in text):
        return text.rstrip('0').rstrip('.')
    return text

def authenticate_library(facets, pmax):
    """Execute both LIB/LINK checks on this actual parsed table.

    A fresh process avoids module-name and precision collisions with exact
    proof modules. The temporary input is serialized from the consumed object,
    so no independent or changed table can stand in for the FILTER input.
    """
    root = Path(os.environ.get('U5_EXACT_INPUT_ROOT', Path(__file__).resolve().parents[1]))
    checker = root / 'input_link/compare_legacy.py'
    if not checker.is_file():
        raise ValueError('missing actual-table LIB/LINK checker; set U5_EXACT_INPUT_ROOT for copied scripts')
    with tempfile.TemporaryDirectory(prefix='filter-library-') as name:
        table = Path(name) / 'facets.json'
        table.write_text(json.dumps(facets))
        checked = subprocess.run([sys.executable, str(checker), str(table), str(pmax)], capture_output=True, text=True)
    if checked.returncode:
        raise ValueError('actual-table LIB/LINK rejection: ' + checked.stderr[-2000:])
    try:
        result = json.loads(checked.stdout)
    except (ValueError, TypeError) as exc:
        raise ValueError('malformed LIB/LINK result') from exc
    if result.get('status') != 'PASS' or result.get('pmax') != pmax or [row.get('mode') for row in result.get('checks', [])] != ['A', 'B'] or any((row.get('facets') != len(facets) for row in result['checks'])):
        raise ValueError('incomplete actual-table LIB/LINK checks')
    return result

def filter_classes(d, flat, boundary, facets, pmax):
    iv = validate_inputs(d, flat, boundary, pmax)
    validate_inventory(d, facets)
    orbits = {f['name']: [(o[0], o[1], o[2], o[3]) for o in f['orbits']] for f in facets}
    lib = {f['name']: f['orbits'] for f in facets}
    iv.sort()
    classes = []
    for lo, hi, i in iv:
        if classes and lo <= classes[-1][1]:
            classes[-1][1] = max(classes[-1][1], hi)
            classes[-1][2].append(i)
        else:
            classes.append([lo, hi, [i]])

    def sides(i):
        r = d[i]
        out = []
        for k, f in enumerate(r['facets']):
            a, b = (r['cells'][k - 1], r['cells'][k])
            o = [o for o in lib[f] if o[0] == r['p'] and sorted(o[1:3]) == sorted([a, b])]
            if not len(o) == 1:
                raise AssertionError()
            out.append((f, r['p'], tuple(sorted([a, b])), o[0][3]))
        return out
    out = []
    for lo, hi, cyc in classes:
        alive = set(cyc)
        S = {i: sides(i) for i in cyc}
        while True:
            have = set((s for i in alive for s in S[i]))
            bad = set()
            for i in alive:
                for f, p, ab, al in S[i]:
                    for p2, a2, b2, al2 in orbits[f]:
                        if (f, p2, tuple(sorted([a2, b2])), al2) not in have:
                            bad.add(i)
            if not bad:
                break
            alive -= bad
        out.append(dict(R=[decimal_endpoint(lo), decimal_endpoint(hi)], cycles=sorted(cyc), alive=sorted(alive)))
    return out

def main(pmax):

    def load(stem):
        with open(f'{stem}_p{pmax}.json') as stream:
            return json.load(stream)
    cycles, flat, boundary, facets = (load(stem) for stem in ('cert_stage1_5d', 'exact_flat', 'exact_boundary', 'cert_facets4'))
    result = filter_classes(cycles, flat, boundary, facets, pmax)
    authenticate_library(facets, pmax)
    from exact_inputs import authenticate_exclusions
    authenticated = authenticate_exclusions(cycles, flat, boundary, pmax, facets=facets)
    expected = (set(flat['flat']), set(boundary['degenerate']))
    if type(authenticated) is not tuple or len(authenticated) != 2 or any((type(ids) is not set for ids in authenticated)) or (authenticated != expected):
        raise ValueError('incomplete exact exclusion authentication')
    return result
if __name__ == '__main__':
    pmax = int(sys.argv[1])
    out = main(pmax)
    n_alive = sum((1 for c in out if c['alive']))
    print(len(out), 'radius classes;', n_alive, 'survive the closure filter;', sum((len(c['alive']) for c in out)), 'cycles in them', file=sys.stderr)
    json.dump(out, open('classes_p%d.json' % pmax, 'w'), indent=0)
