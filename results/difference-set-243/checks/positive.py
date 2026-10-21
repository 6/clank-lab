"""Same-group positive-prefix mathematical controls, invoked by check.py."""
import itertools
from pathlib import Path
DATA = Path(__file__).resolve().parent.parent / "data"
WIDTH = 3**12

def need(value, message):
    if not value:
        raise ValueError(message)

def dec(e):
    return e // 81, e // 9 % 9, e % 9

def enc(p):
    return 81 * (p[0] % 3) + 9 * (p[1] % 9) + p[2] % 9

def scalar(e, t=61):
    return enc(tuple(t * x for x in dec(e)))

def controls():
    cells = {}
    for e in range(243):
        orbit = sorted({e, scalar(e), scalar(scalar(e))})
        if len(orbit) == 3 and e == orbit[0]:
            x, y, z = dec(e)
            cells.setdefault(9 * x + 3 * (y % 3) + z % 3, []).append(orbit)
    need(len(cells) == 24 and all(len(v) == 3 for v in cells.values()), 'scalar cells')
    singletons = [enc((x, 3 * u, 3 * v)) for x, u, v in itertools.product(range(3), repeat=3)
                  if 24909666 >> (9 * x + 3 * u + v) & 1]
    cases = [list(map(int, line.split()))[1:] for line in
             (DATA / 'cases.txt').read_text().splitlines() if line.strip()]
    result = []
    for ci, row in enumerate(cases):
        # Same deterministic words as the original control, now tested at the
        # real depth-12 ID (including a neighbouring wrong ID), rather than depth 1.
        word = [(ci // 3 ** (d % 2) + d * d + d // 3) % 3 for d in range(24)]
        positions = sorted(cells, key=lambda q: (-row[q], q))
        def make_points(digits):
            chosen = list(singletons)
            for d, q in enumerate(positions):
                for j, orbit in enumerate(sorted(cells[q])):
                    if (row[q] == 3) == (digits[d] == j):
                        chosen.extend(orbit)
            return sorted(chosen)
        def differences(chosen):
            counts = [0] * 243
            for a in chosen:
                for b in chosen:
                    if a != b:
                        counts[enc(tuple(x - y for x, y in zip(dec(a), dec(b))))] += 1
            return counts
        points = make_points(word)
        need(len(points) == len(set(points)) == 121, 'planted cardinality')
        need({scalar(e) for e in points} == set(points), 'planted scalar fixedness')
        counts = differences(points)
        prefix = 0
        for digit in word[:12]:
            prefix = 3 * prefix + digit
        ident = ci * WIDTH + prefix
        need(prefix + 1 < WIDTH, 'neighbour must remain in same case')
        neighbour = list(word)
        v = prefix + 1
        for d in range(11, -1, -1):
            neighbour[d], v = v % 3, v // 3
        neighbour_points = make_points(neighbour)
        need(neighbour_points != points, 'distinct prefix must give a distinct set')
        result.append(dict(case=ci, word=''.join(map(str, word)), prefix_id=ident,
                           wrong_prefix_id=ident + 1, points=points,
                           maximum=max(counts[1:]), difference_counts=counts,
                           neighbour_points=neighbour_points,
                           neighbour_maximum=max(differences(neighbour_points)[1:])))
    need(len(result) == 8, 'eight controls')
    return result

def parse_rows(path, ids):
    rows = []
    for text, ident in zip(path.read_text().splitlines(), ids):
        f = text.split()
        need(len(f) >= 9 and int(f[0]) == ident and f[1:3] == ['1', '1'], 'wrong/incomplete prefix row')
        points = list(map(int, f[9:]))
        need(len(points) == int(f[8]), 'witness length')
        rows.append(dict(id=ident, valid=int(f[3]), nodes=int(f[4]),
                         solutions=int(f[5]), witness=sorted(points)))
    need(len(rows) == len(ids) == len(path.read_text().splitlines()), 'row count')
    return rows

def check_results(expected, modes):
    need(set(modes) == {'fast', 'direct'}, 'both kernels required')
    for mode in modes.values():
        good, low = mode['bound_M'], mode['bound_M_minus_1']
        need(len(good) == 16 and len(low) == 8, 'control rows')
        for ci, item in enumerate(expected):
            actual, wrong = good[2 * ci:2 * ci + 2]
            need(actual == dict(id=item['prefix_id'], valid=1, nodes=13,
                                solutions=1, witness=item['points']), 'positive leaf/prefix mismatch')
            neighbour_fits = item['neighbour_maximum'] <= item['maximum']
            need(wrong['id'] == item['wrong_prefix_id']
                 and wrong['solutions'] == int(neighbour_fits)
                 and wrong['witness'] == (item['neighbour_points'] if neighbour_fits else [])
                 and wrong['witness'] != item['points'], 'prefix/witness association wrong')
            need(low[ci]['id'] == item['prefix_id'] and low[ci]['solutions'] == 0
                 and not low[ci]['witness'], 'insufficient bound accepted')
