"""Explicit W acceptance scopes and combinatorial test obligations.

No geometry/search imports. Lists are reviewed inputs, never inferred from
rows being accepted. Full/supplementary type-(i) lists also match the P1
input files; the full list adds 14 type-(ii), 3 type-(iii), 36 integer
slices and four continuous families. Restricted runs require a singleton
partner filter and are appended only for the seven specified exceptions.
"""
import ast
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
LIMITS = {(3, 7): 41, (3, 8): 23, (3, 9): 17, (4, 5): 19}
EXCEPTIONS = {(m, 3, 7) for m in range(38, 42)} | {(23, 3, 8), (17, 3, 9), (19, 4, 5)}
FAMILIES = {'(m,4,4)': 3, '(m,3,3,3)': 4, '(m,3,6)': 3, '(ii)q=m': 4}
REAL = {'kind': 'real', 'min': 17, 'includes_infinity': True}


def config(name):
    c = ast.literal_eval(name[3:].split('@')[0])
    if not isinstance(c, tuple) or not 3 <= len(c) <= 5 or any(type(q) is not int or q < 3 for q in c):
        raise ValueError('integer polygon configuration required: ' + name)
    return c


def obligations(name):
    """Exact parameter domain, kind, vertex names and F diagonal flags."""
    base, *point = name.split('@n=')
    domain = {'n': dict(REAL)}
    partner = None
    diagonals = set()
    if base.startswith('(i)'):
        c = config(base)
        k = len(c)
        names = ['a', 'b'] + [f'x{i+1}' for i in range(k)]
        kind = 'unpaired'
        if c[0] >= 17:
            m, rest = c[0], c[1:]
            if rest not in LIMITS or not 17 <= m <= LIMITS[rest]:
                raise ValueError('bounded integer slice out of range')
            domain['m'] = {'kind': 'integer_slice', 'value': m, 'min': 17, 'max': LIMITS[rest]}
            partner, kind = frozenset(('x1', 'x2')), 'paired'
        for i in range(k):
            for j in range(i + 2, k):
                if (i, j) != (0, k - 1):
                    diagonals.add(frozenset((f'x{i+1}', f'x{j+1}')))
    elif base in FAMILIES:
        domain['m'] = dict(REAL)
        kind = 'paired'
        names = ['a', 'b'] + (['x', 'y', 'z1', 'z2'] if base == '(ii)q=m'
                                else [f'x{i+1}' for i in range(FAMILIES[base])])
        partner = frozenset(('z1', 'z2') if base == '(ii)q=m' else ('x1', 'x2'))
        if base == '(m,3,3,3)':
            diagonals = {frozenset(('x1', 'x3')), frozenset(('x2', 'x4'))}
    elif base.startswith('(ii)q=') and base[6:].isdigit() and 3 <= int(base[6:]) <= 16:
        names, kind = ['a', 'b', 'x', 'y', 'z1', 'z2'], 'unpaired'
    elif base in ('(iii)(3,3)', '(iii)(3,4)', '(iii)(3,5)'):
        names, kind = ['a', 'b', 'x', 'y', 'z1', 'z2', 'w'], 'unpaired'
    else:
        raise ValueError('unknown fan: ' + name)
    if point:
        if len(point) != 1 or not base.startswith('(i)'):
            raise ValueError('invalid restricted fan')
        c = config(base)
        if c not in EXCEPTIONS or point != [str(c[0])]:
            raise ValueError('restriction must be an exceptional integer n=m point')
        domain['n'] = {'kind': 'integer_point', 'value': c[0]}
    tests = {f'V:{v}:{s}' for v in names for s in ('+', '-')} | {'P:+1+1', 'P:+1-1', 'D:+'}
    pairs = {a+b: frozenset((a, b)) in diagonals for i, a in enumerate(names) for b in names[i+1:]
             if frozenset((a, b)) not in (frozenset(('a', 'b')), partner)}
    return domain, kind, tests, pairs


def profile(scope):
    data = json.loads((HERE / 'acceptance-inventories.json').read_text())
    if scope not in data:
        raise ValueError('explicit known acceptance inventory required')
    # Check the complete inventory against authoritative P1 lists and explicit
    # elementary families, independently of the W constructor.
    p1 = lambda filename: ['(i)(' + l.strip() + ')' for l in (HERE / filename).read_text().splitlines() if l.strip()]
    full = p1('p1_closable.txt') + [f'(ii)q={q}' for q in range(3, 17)] + \
        [f'(iii)(3,{q})' for q in (3, 4, 5)] + \
        [f'(i)({m},{r[0]},{r[1]})' for r, hi in LIMITS.items() for m in range(17, hi+1)] + list(FAMILIES)
    if len(full) != 127 or len(p1('p1_closable.txt')) != 70 or len(p1('p1_excluded.txt')) != 67:
        raise ValueError('P1 inventory counts changed')
    for label, expected in [('full', full), ('supplementary', p1('p1_excluded.txt'))]:
        if len(data[label]['fans']) != len(expected) or set(data[label]['fans']) != set(expected):
            raise ValueError(label + ': inventory differs from authoritative inputs')
    spec = data[scope]
    if len(set(spec['fans'])) != len(spec['fans']) or len(set(spec['failures'])) != len(spec['failures']):
        raise ValueError('duplicate declared inventory entry')
    if not set(spec['failures']) <= set(spec['fans']):
        raise ValueError('unexpected declared failure')
    names = list(spec['fans'])
    for name in spec['failures']:
        if name.startswith('(i)') and config(name) in EXCEPTIONS:
            names.append(name + '@n=' + str(config(name)[0]))
    return {name: obligations(name) for name in names}, set(spec['failures'])
