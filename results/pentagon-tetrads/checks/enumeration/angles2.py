"""Angle screen with sign-pattern pruning (replaces the brute-force loop of
angles.py; same conditions, see that file's docstring).

For each reflex pattern (which prototile corners are reflex), labelings are
chosen tile by tile; a constraint whose corner slots are all labelled is
checked with interval bounds (convex corners in (0,180), reflex in
(180,360)); partially labelled constraints are checked by their lower bound.
Leaves are decided by an LP with a strict margin (numerical screen).
"""
import itertools
import json
import sys
import time

THRESH = 1e-7  # margin threshold of the numerical screen; 0 in the exact screen

from angles import lp_feasible, sign_patterns
from placements import MapData, placements, corner_sequence, dihedral, label_of


def constraints(md, cs, bends, n):
    """Returns list of constraints (kind, slots, nstraight) where slots are
    (tile, k) corner slots, and the per-tile corner sequences."""
    seqs = [corner_sequence(md, cs, bends, t) for t in range(4)]
    where = {}
    for t in range(4):
        for k, pos in enumerate(seqs[t]):
            where[(t, pos)] = (t, k)
    cons = []
    for v, secs in enumerate(md.vertex_sectors):
        slots = []
        s = 0
        for d in secs:
            t = md.tail[d]
            if t >= 4:
                continue
            if cs[d] == 'C':
                slots.append(where[(t, ('V', d))])
            else:
                s += 1
        cons.append(('E' if md.vertex_interior[v] else 'L', tuple(slots), s))
    for e, (a, b) in enumerate(md.edges):
        if a < 4 and b < 4:
            for j in range(bends[e]):
                cons.append(('E', (where[(a, ('B', e, j))], where[(b, ('B', e, j))]), 0))
    return cons, seqs


def check_interval(kind, labels_types, s):
    """labels_types: list of booleans (reflex) for assigned slots; returns
    False if impossible.  full: whether every slot is assigned."""
    pass


def screen_placement(md, cs, bends, n, pats, labs_all, cache, emit):
    cons, seqs = constraints(md, cs, bends, n)
    # constraints become checkable when the max tile among their slots is labelled
    by_level = [[] for _ in range(4)]
    for c in cons:
        lvl = max([t for t, k in c[1]], default=0)
        by_level[lvl].append(c)
    # partial lower-bound checks at each level for constraints not yet complete
    for pat in pats:
        labs = [(True, 0), None, None, None]
        yield from _dfs(1, labs, pat, cons, by_level, n, labs_all, cache, emit, md, cs, bends)


def _ok(c, labs, pat, full, n):
    kind, slots, s = c
    lo = 180 * s
    hi = 180 * s
    for t, k in slots:
        if labs[t] is None:
            continue
        a = label_of(labs[t], k, n)
        if pat[a]:
            lo += 180
            hi += 360
        else:
            hi += 180
    # strict: convex in (0,180), reflex in (180,360); at least one corner is open
    if full:
        if kind == 'E':
            if not slots:
                return 180 * s == 360
            return lo < 360 < hi
        return lo < 360 if slots else 180 * s < 360
    return lo < 360


def _dfs(level, labs, pat, cons, by_level, n, labs_all, cache, emit, md, cs, bends):
    if level == 4:
        rows = []
        for kind, slots, s in cons:
            coef = [0] * n
            for t, k in slots:
                coef[label_of(labs[t], k, n)] += 1
            rows.append((kind, tuple(coef), 180 * s))
        rows = tuple(sorted(set(rows)))
        key = (rows, pat)
        r = cache.get(key)
        if r is None:
            tm, x = lp_feasible(rows, n, pat)
            r = (tm, None if x is None else [round(float(v), 6) for v in x])
            cache[key] = r
        if r[0] > THRESH:
            emit(labs, pat, r)
            yield 1
        return
    for lab in labs_all:
        labs[level] = lab
        good = True
        for c in cons:
            tiles = {t for t, k in c[1]}
            full = all(labs[t] is not None for t in tiles)
            if level not in tiles and not (level == 1 and tiles and tiles <= {0}):
                continue
            if not _ok(c, labs, pat, full, n):
                good = False
                break
        if good:
            yield from _dfs(level + 1, labs, pat, cons, by_level, n, labs_all, cache, emit, md, cs, bends)
        labs[level] = None


def main(maps_file, n, outf, only_map=None, chunk=None):
    lines = open(maps_file).read().splitlines()
    pats = sign_patterns(n)
    labs_all = dihedral(n)
    cache = {}
    t0 = time.time()
    with open(outf, 'w') as out:
        for mi, line in enumerate(lines):
            if only_map is not None and mi != only_map:
                continue
            md = MapData(json.loads(line))
            nsurv = 0
            npl = 0
            for pi, (cs, bends) in enumerate(placements(md, n)):
                if chunk is not None and pi % chunk[1] != chunk[0]:
                    continue
                npl += 1
                if len(cache) > 1500000:
                    cache.clear()
                # tile-0 checks that need no labels of others: constraints with only tile 0 slots
                def emit(labs, pat, r, pi=pi, cs=cs, bends=bends):
                    out.write(json.dumps({'map': mi, 'placement': pi,
                                          'cs': {str(k): v for k, v in cs.items()}, 'bends': bends,
                                          'labs': [list(l) for l in labs], 'pattern': list(pat),
                                          'margin': r[0], 'alpha': r[1]}) + '\n')
                # check tile-0-only constraints first
                cons, _ = constraints(md, cs, bends, n)
                for _ in screen_placement(md, cs, bends, n, pats, labs_all, cache, emit):
                    nsurv += 1
            print(f'map {mi}: placements {npl}, survivors {nsurv}, cache {len(cache)}, {time.time()-t0:.0f}s',
                  file=sys.stderr, flush=True)


if __name__ == '__main__':
    only = int(sys.argv[4]) if len(sys.argv) > 4 and sys.argv[4] != '-' else None
    chunk = tuple(int(x) for x in sys.argv[5].split('/')) if len(sys.argv) > 5 else None
    main(sys.argv[1], int(sys.argv[2]), sys.argv[3], only, chunk)
