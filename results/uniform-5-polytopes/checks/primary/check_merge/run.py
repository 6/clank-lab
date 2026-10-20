"""Prove all 33 merged names congruent to their canonical names, then run
the deliberate corruptions.  Usage: python3 run.py [--facets u1_facets_p16.json]"""
import json, sys, time
from fractions import Fraction as Fr
import merge
from aliases import ALIASES


def file_aliases(path):
    """Canonical -> aliases from the shared facet file (tolerant of a list of
    entries or a dict keyed by name)."""
    data = json.load(open(path))
    entries = data.values() if isinstance(data, dict) else data
    if isinstance(data, dict) and all(isinstance(v, dict) for v in data.values()):
        entries = [dict(v, name=v.get('name', k)) for k, v in data.items()]
    out = {}
    for ent in entries:
        if isinstance(ent, dict) and ent.get('aliases'):
            out[ent['name']] = sorted(ent['aliases'])
    return out


def main():
    t0 = time.process_time()
    if '--facets' in sys.argv:
        fa = file_aliases(sys.argv[sys.argv.index('--facets') + 1])
        mine = {k: sorted(v) for k, v in ALIASES.items()}
        print('alias list vs --facets file:', 'identical' if fa == mine else 'DIFFERENT')
        if fa != mine:
            for k in sorted(set(fa) | set(mine)):
                if fa.get(k) != mine.get(k):
                    print('  ', k, 'file', fa.get(k), 'here', mine.get(k))
            sys.exit(1)
    pairs = [(c, a) for c in ALIASES for a in ALIASES[c]]
    print('aliases:', len(pairs), 'in', len(ALIASES), 'groups')
    cache = {}

    def get(n):
        if n not in cache:
            cache[n] = merge.build(n)
            merge.edge_check(n, cache[n])
        return cache[n]

    proved = 0
    for c, a in pairs:
        t = time.process_time()
        ok, why = merge.prove(c, a, get(c), get(a))
        proved += ok
        print('%-6s %-18s ~ %-8s %s  (%.1fs)' % ('PROVED' if ok else 'FAILED', a, c, why,
                                                  time.process_time() - t))
    print('proved %d/%d' % (proved, len(pairs)))

    print('\ncorruptions (each must be rejected):')
    rejected = 0
    # (a) the task's example: rectified tesseract vs 24-cell
    ok, why = merge.prove('B40010', 'B40100')
    print('(a) B40010 ~ B40100:', 'ACCEPTED' if ok else 'rejected: ' + why)
    rejected += not ok
    # (b) equal vertex counts, not congruent: truncated vs runcinated tesseract
    ok, why = merge.prove('B40011', 'B41001')
    print('(b) B40011 ~ B41001:', 'ACCEPTED' if ok else 'rejected: ' + why)
    rejected += not ok
    # exact certificate of non-congruence: the multisets of pairwise squared
    # distances differ (an isometry invariant)
    def dists(P):
        return sorted(merge.sqdist(P[i], P[j]) for i in range(len(P)) for j in range(i + 1, len(P)))
    dP, dQ = dists(merge.build('B40011')), dists(merge.build('B41001'))
    print('    exact pairwise squared-distance multisets', 'equal' if dP == dQ else
          'differ: squared diameters %s vs %s, not congruent' % (
              merge.kstr(dP[-1]), merge.kstr(dQ[-1])))
    # (c) a true pair with one coordinate of one vertex moved by 10^-12
    #     (exactly): the float search still matches, the exact step must not
    Q = [list(p) for p in get('F41100')]
    x = Q[7][2]
    Q[7][2] = (x[0] + Fr(1, 10**12),) + x[1:]
    Q = [tuple(p) for p in Q]
    ok, why = merge.prove('B41110', 'F41100', get('B41110'), Q)
    print('(c) B41110 ~ F41100 with one vertex moved by 1e-12:',
          'ACCEPTED' if ok else 'rejected: ' + why)
    rejected += not ok
    # (d) a true pair with a wrong bijection (two images swapped)
    P, Q = get('B41010'), get('F40100')
    pi = merge.find_bijection(P, Q)
    pi[0], pi[1] = pi[1], pi[0]
    ok, _ = merge.exact_congruent(P, Q, pi)
    print('(d) B41010 ~ F40100 with two images of the bijection swapped:',
          'ACCEPTED' if ok else 'rejected: exact squared distances differ')
    rejected += not ok
    print('corruptions rejected %d/4' % rejected)
    print('CPU seconds: %.1f' % (time.process_time() - t0))
    sys.exit(0 if proved == len(pairs) and rejected == 4 else 1)


if __name__ == '__main__':
    main()
