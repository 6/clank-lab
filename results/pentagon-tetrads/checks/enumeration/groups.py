"""Group closure cases by relabeling of the prototile (rotations and
reflections of P's corner labels, with sides relabeled accordingly).
Two cases in one group have the same closure-and-simplicity problem up to
renaming, since relabeling or mirroring P preserves closure and simplicity.
Key: (reflex pattern, sorted angle rows, sorted ray set) after relabeling."""
import json
import sys


def relabelings(n):
    out = []
    for refl in (False, True):
        for r in range(n):
            if not refl:
                vm = [(i + r) % n for i in range(n)]
                em = [(i + r) % n for i in range(n)]
            else:
                vm = [(-i + r) % n for i in range(n)]
                em = [(-i - 1 + r) % n for i in range(n)]
            out.append((vm, em))
    return out


def transform(case, arows, vm, em, n=5):
    """The case's (pattern, angle rows, rays) after relabeling prototile
    corner i -> vm[i] and side i -> em[i]."""
    pat = [None] * n
    for i in range(n):
        pat[vm[i]] = case['pattern'][i]
    rows = []
    for kind, coef, const in arows:
        c = [0] * n
        for i in range(n):
            c[vm[i]] += coef[i]
        rows.append((kind, tuple(c), const))
    rays = []
    for r in case['rays']:
        rr = [0] * n
        for i in range(n):
            rr[em[i]] = r[i]
        rays.append(tuple(rr))
    return (tuple(pat), tuple(sorted(set(rows))), tuple(sorted(rays)))


def key(case, arows, n=5):
    best = None
    for vm, em in relabelings(n):
        # new label vm[i] carries old corner i
        pat = [None] * n
        for i in range(n):
            pat[vm[i]] = case['pattern'][i]
        rows = []
        for kind, coef, const in arows:
            c = [0] * n
            for i in range(n):
                c[vm[i]] += coef[i]
            rows.append((kind, tuple(c), const))
        rays = []
        for r in case['rays']:
            rr = [0] * n
            for i in range(n):
                rr[em[i]] = r[i]
            rays.append(tuple(rr))
        k = (tuple(pat), tuple(sorted(set(rows))), tuple(sorted(rays)))
        if best is None or k < best:
            best = k
    return best


if __name__ == '__main__':
    import os
    sys.path.insert(0, '.')
    from lengths import MapData, build_problem
    cases = json.load(open(sys.argv[1]))
    maps = [MapData(json.loads(l)) for l in open(sys.argv[2])]
    recs = {(r['map'], r['placement'], json.dumps(r['labs']), json.dumps(r['pattern'])): r
            for r in map(json.loads, open(sys.argv[3]))}
    groups = {}
    for k, c in enumerate(cases):
        r = recs[(c['map'], c['placement'], json.dumps(c['labs']), json.dumps(c['pattern']))]
        cs, bends, labs, segs, lrows, arows = build_problem(maps[c['map']], r, 5)
        groups.setdefault(json.dumps(key(c, arows)), []).append(k)
    out = sorted(groups.values())
    json.dump(out, open(sys.argv[4], 'w'))
    print(len(out), [len(g) for g in out])
