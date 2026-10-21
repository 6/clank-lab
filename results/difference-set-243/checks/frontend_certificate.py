#!/usr/bin/env python3
"""Recheck a frontend.json from frontend.py export.
Self-contained (shares no code with the exporter).  Checks the certificate's
internal claims; the completeness of the 144 images and of the singleton pattern
set comes from the enumeration stages, not from this file.
Invoked by check.py; checks mathematical structure, with no file-integrity checks."""
import json, sys, re
from pathlib import Path
from itertools import product

def fail(m):
    print('FAIL', m); sys.exit(1)
def need(c, m):
    if not c: fail(m)

E = [(x, y, z) for x in range(3) for y in range(9) for z in range(9)]
def I(g): return 81*g[0]+9*g[1]+g[2]
def U(n): return (n//81, n//9 % 9, n % 9)
def ad(g, h): return ((g[0]+h[0]) % 3, (g[1]+h[1]) % 9, (g[2]+h[2]) % 9)
def sc(n, g): return ((n*g[0]) % 3, (n*g[1]) % 9, (n*g[2]) % 9)
def inH(g): return sc(3, g) == (0, 0, 0)
def cellq(g): return 9*g[0]+3*(g[1] % 3)+g[2] % 3
def hbit(g): return 9*g[0]+3*(g[1]//3)+g[2]//3
def hel(b): return (b//9, 3*(b//3 % 3), 3*(b % 3))

def partition(path):
    words = Path(path).read_text(encoding='ascii').split()
    need(all(re.fullmatch(r'0|[1-9][0-9]*', w) for w in words), 'p243 integer grammar')
    data = list(map(int, words))
    need(data[:7] == [3, 3, 9, 9, 121, 60, 99], 'p243 header')
    rows, pos = [], 7
    for _ in range(99):
        need(pos < len(data) and data[pos] in (1, 3), 'p243 orbit length')
        size = data[pos]; pos += 1
        o = data[pos:pos+size]; pos += size
        need(len(o) == size and o == sorted(set(o)) and all(0 <= n < 243 for n in o), 'p243 orbit elements')
        rows.append(tuple(o))
    need(pos == len(data), 'p243 trailing tokens')
    need(sorted(n for o in rows for n in o) == list(range(243)), 'p243 exact point partition')
    expected = {tuple(sorted({I(sc(t, g)) for t in (1, 61, 61*61)})) for g in E}
    ordered = sorted(o for o in expected if len(o) == 3) + sorted(o for o in expected if len(o) == 1)
    need(len(expected) == 99 and rows == ordered, 'p243 multiplier orbit partition/order')
    return rows

def main():
    c = json.load(open(sys.argv[1]))
    S0 = c['S0']
    pf = sys.argv[2] if len(sys.argv) > 2 else None
    if pf:
        actual_orbits = partition(pf)
    need(c['group'] == [3, 9, 9] and S0 == 24909666, 'header')
    need([(S0 >> (9*x) & 511).bit_count() for x in range(3)] == [4, 3, 6], 'S0 layers')
    # --- 27 maps
    qp = []
    for mp in c['maps']:
        phi, q = mp['phi'], mp['qperm']
        need(sorted(phi) == list(range(243)), 'phi not bijective')
        t = U(phi[0]); need(inH(t), 'translation not in H')
        A = [None]*243
        for g in E:
            r = U(phi[I(g)]); A[I(g)] = ((r[0]-t[0]) % 3, (r[1]-t[1]) % 9, (r[2]-t[2]) % 9)
        for g in E:
            for h in E:
                need(A[I(ad(g, h))] == ad(A[I(g)], A[I(h)]), 'not additive')
        for g in E:
            need(U(phi[I(sc(61, g))]) == sc(61, U(phi[I(g)])), 'x61 does not commute')
        S = {hbit(hel(b)) for b in range(27) if S0 >> b & 1}
        need({hbit(U(phi[I(hel(b))])) for b in S} == S and all(inH(U(phi[I(hel(b))])) for b in S), 'S0 not preserved')
        pq = [None]*27
        for n in range(243):
            j, k = cellq(U(n)), cellq(U(phi[n]))
            need(pq[j] in (None, k), 'quotient not well defined'); pq[j] = k
        need(pq == q and sorted(q) == list(range(27)), 'quotient permutation mismatch')
        qp.append(tuple(q))
    need(len(set(qp)) == 27, '27 distinct quotient permutations')
    # --- images
    forms = [f for f in product(range(3), repeat=3) if any(f) and next(x for x in f if x) == 1]
    Q = list(product(range(3), repeat=3))
    imgs = [tuple(i) for i in c['images']]
    need(len(imgs) == 144 and len(set(imgs)) == 144, 'image count')
    for a in imgs:
        need([a[0], a[9], a[18]] == [4, 3, 6], 'special cells')
        need(all(a[j] in (3, 6) for j in range(27) if j not in (0, 9, 18)), 'nonspecial values')
        for f in forms:
            s = [0, 0, 0]
            for j, q in enumerate(Q):
                s[sum(x*y for x, y in zip(f, q)) % 3] += a[j]
            need(sorted(s) == [36, 40, 45], 'line sums')
        for h in Q:
            corr = sum(a[j]*a[Q.index(tuple((x+y) % 3 for x, y in zip(q, h)))] for j, q in enumerate(Q))
            need(corr == (601 if h == (0, 0, 0) else 540), 'autocorrelation')
    # --- representatives and cover
    reps = [tuple(r) for r in c['representatives']]
    need(len(reps) == 8, 'representative count')
    def app(p, a):
        y = [None]*27
        for j in range(27): y[p[j]] = a[j]
        return tuple(y)
    orbits = [{app(p, r) for p in qp} for r in reps]
    need(sum(map(len, orbits)) == 144 and set().union(*orbits) == set(imgs), 'orbit coverage')
    need(sorted(map(len, orbits)) == [9, 9, 9, 9, 27, 27, 27, 27], 'orbit sizes')
    if pf:
        cf = Path(sys.argv[3]) if len(sys.argv) > 3 else Path(pf).parent / 'cases.txt'
        lines = cf.read_text(encoding='ascii').splitlines()
        need(len(lines) == 8, 'cases row count')
        case_rows = []
        for line in lines:
            words = line.split()
            need(len(words) == 28 and all(re.fullmatch(r'0|[1-9][0-9]*', w) for w in words), 'cases row grammar')
            case_rows.append(list(map(int, words)))
        hits = []
        for weight, *a in case_rows:
            hit = [j for j, orbit in enumerate(orbits) if tuple(a) in orbit]
            need(len(hit) == 1, 'cases image not in exactly one certified orbit')
            need(weight == len(orbits[hit[0]]), 'cases orbit weight')
            hits.append(hit[0])
        need(sorted(hits) == list(range(8)), 'cases must hit all eight orbits exactly once')
    for a, (r, mi) in zip(imgs, c['image_cover']):
        need(app(qp[mi], reps[r]) == a, 'image_cover entry wrong')
    # --- singleton coverage
    cov = c['singleton_cover']
    masks = [e[0] for e in cov]
    need(len(masks) == len(set(masks)) == 7776, 'singleton cover size')
    for e in cov:
        m, al, d, g, ee, f, h, i, t0, t1, t2 = e
        need(al in (1, 2) and (ee*i-f*h) % 3 and all(0 <= v < 3 for v in e[2:]), 'bad parameters')
        # explicit full map (b=c=0), bijection, H-restriction equals the H-map
        full = []
        for (x, y, z) in E:
            full.append(I(((al*x+t0) % 3, (3*d*x+ee*y+f*z+3*t1) % 9, (3*g*x+h*y+i*z+3*t2) % 9)))
        need(len(set(full)) == 243, 'singleton map not bijective')
        im = 0
        for b in range(27):
            if S0 >> b & 1:
                im |= 1 << hbit(U(full[I(hel(b))]))
        need(im == m, 'singleton cover mask mismatch')
        need(all((m & _t(m, h2)).bit_count() % 3 == 0 for h2 in range(1, 27)), 'congruence fails')
    need(S0 in set(masks), 'S0 missing')
    # --- encoding
    sl = c['singleton_lines_by_bit']; need(len(set(sl)) == 27, 'singleton lines')
    cl = c['cell_orbit_lines']; need(len(cl) == 24 and all(len(v) == 3 for v in cl.values()), 'cell lines')
    if pf:
        need(sl == [actual_orbits.index((I(hel(b)),)) for b in range(27)], 'p243 singleton line encoding')
        cells = {str(q): [j for j, o in enumerate(actual_orbits) if len(o) == 3 and cellq(U(o[0])) == q]
                 for q in range(27) if q not in (0, 9, 18)}
        need(cl == cells, 'p243 cell orbit line encoding')
        print('INPUT STRUCTURE PASS p243=27 singletons+72 exact multiplier triples; cases=8 distinct complete orbits with exact weights')
    print('CERT PASS maps=27 images=144 reps=8 orbit_sizes=9x4,27x4 singleton_cover=7776')

def _t(m, h):
    r = 0
    hx, hu, hw = h//9, h//3 % 3, h % 3
    for b in range(27):
        if m >> b & 1:
            x, u, w = b//9, b//3 % 3, b % 3
            r |= 1 << (9*((x+hx) % 3)+3*((u+hu) % 3)+(w+hw) % 3)
    return r

try:
    main()
except (KeyError, IndexError, TypeError, ValueError, AttributeError) as e:
    # A malformed certificate (missing field, short row, wrong type) is an
    # explicit rejection, not a crash.  Missing input files still raise.
    fail('malformed %s: %s' % (type(e).__name__, e))
