#!/usr/bin/env python3
"""Independent checker of the finite reduction frontend for a (243,121,60)
difference set in C3 x C9 x C9.  Imports no existing frontend code.

Inputs are read from the sibling data/ directory.
Invoked by check.py; finite enumeration alone does not replay the lifting search.
"""
import argparse, itertools, os, sys, tempfile
from itertools import product, permutations
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(HERE, '..', 'data')
RECEIPTS = os.environ.get('DS243_RECEIPTS', SRC)
P243 = os.environ.get('DS243_P243', os.path.join(SRC, 'p243.txt'))

V, K, LAM = 243, 121, 60
S0 = 24909666                       # fixed singleton representative, bit 9x+3u+w

# ---- group C3 x C9 x C9, element (x,y,z), index 81x+9y+z -------------------
def add(g, h):
    return ((g[0]+h[0]) % 3, (g[1]+h[1]) % 9, (g[2]+h[2]) % 9)
def mul(n, g):
    return ((n*g[0]) % 3, (n*g[1]) % 9, (n*g[2]) % 9)
def idx(g):
    return 81*g[0]+9*g[1]+g[2]
ELEMS = [(x, y, z) for x in range(3) for y in range(9) for z in range(9)]
assert [idx(g) for g in ELEMS] == list(range(V))
def in_H(g):                        # H = G[3]: elements killed by 3
    return mul(3, g) == (0, 0, 0)
HELEMS = [g for g in ELEMS if in_H(g)]
assert len(HELEMS) == 27
def hbit(g):                        # bit index of an H element: 9x+3u+w
    return 9*g[0]+3*(g[1]//3)+g[2]//3
def hel(b):
    return (b//9, 3*(b//3 % 3), 3*(b % 3))
assert [hbit(hel(b)) for b in range(27)] == list(range(27))
def cell(g):                        # index of g mod 3G in C3^3: 9x+3y+z
    return 9*g[0]+3*(g[1] % 3)+(g[2] % 3)
QPTS = [(x, y, z) for x in range(3) for y in range(3) for z in range(3)]
SPECIAL = (0, 9, 18)               # cells of H: (x,0,0)
NONSPECIAL = [j for j in range(27) if j not in SPECIAL]
assert len(NONSPECIAL) == 24

# 13 projective forms on C3^3, first nonzero coordinate 1
FORMS = [q for q in QPTS if any(q) and next(c for c in q if c) == 1]
assert len(FORMS) == 13
def fval(f, j):
    q = QPTS[j]
    return sum(a*b for a, b in zip(f, q)) % 3
FCOSET = [[[j for j in range(27) if fval(f, j) == t] for t in range(3)] for f in FORMS]

LAST_GOOD = set()

class Fail(Exception):
    pass
def need(cond, msg):
    if not cond:
        raise Fail(msg)

# ---- 1. index-three moment solutions --------------------------------------
def moments():
    """All (n0,n1,n2): sum 121, sum squares 121+60*(81-1)."""
    target = K + LAM*(V//3 - 1)
    need(target == 4921, 'moment target')
    sols = [t for t in product(range(K+1), repeat=3)
            if sum(t) == K and sum(c*c for c in t) == target]
    base = {tuple(sorted(t)) for t in sols}
    need(base == {(36, 40, 45)}, 'moment base %r' % base)
    need(len(sols) == 6, 'moment arrangements')
    # equivalent forms: pairwise products sum, |chi|^2 = 61 for nontrivial chi
    for t in sols:
        need(sum(t[i]*t[j] for i in range(3) for j in range(i+1, 3)) == (K*K-target)//2, 'cross')
        need(target - (K*K-target)//2 == K-LAM, 'chi square')
    return sols

# ---- multiplier structure ---------------------------------------------------
def orbits61():
    seen, orbs = set(), []
    for g in ELEMS:
        if g in seen:
            continue
        o, h = [], g
        while h not in o:
            o.append(h); h = mul(61, h)
        orbs.append(o); seen.update(o)
    return orbs

def multiplier_facts():
    orbs = orbits61()
    sizes = sorted(len(o) for o in orbs)
    need(sizes.count(1) == 27 and sizes.count(3) == 72 and len(sizes) == 99, 'orbit sizes')
    need(all(in_H(o[0]) for o in orbs if len(o) == 1), 'fixed points are H')
    # every orbit lies inside one coset of 3G
    need(all(len({cell(g) for g in o}) == 1 for o in orbs), 'orbit within cell')
    # each nonspecial cell = 9 non-H elements = exactly three 3-orbits
    for j in NONSPECIAL:
        members = [g for g in ELEMS if cell(g) == j]
        need(len(members) == 9 and not any(in_H(g) for g in members), 'cell members')
        need(len({tuple(sorted(o)) for o in orbs if cell(o[0]) == j}) == 3, 'three orbits')
    # special cells are exactly H layers
    for j in SPECIAL:
        need(all(in_H(g) for g in ELEMS if cell(g) == j), 'special cell in H')
    return orbs

def read_p243(path=P243):
    data = parse_ints(open(path).read(), 'p243')
    need(data[:7] == [3, 3, 9, 9, 121, 60, 99], 'p243 header')
    pos, parts = 7, []
    for _ in range(99):
        need(pos < len(data), 'p243 truncated')
        n = data[pos]; need(n >= 1, 'p243 orbit size')
        o = data[pos+1:pos+1+n]; need(len(o) == n and all(0 <= v < V for v in o), 'p243 elements')
        parts.append(frozenset(o)); pos += n+1
    need(pos == len(data), 'p243 trailing data')
    return parts

def parse_ints(text, what):
    out = []
    for tok in text.split():
        need(tok.lstrip('-').isdigit() and (tok[0] != '0' or tok == '0'), '%s: bad token %r' % (what, tok))
        out.append(int(tok))
    return out

def check_partition():
    orbs = multiplier_facts()
    mine = {frozenset(idx(g) for g in o) for o in orbs}
    parts = read_p243()
    need(set(parts) == mine and len(parts) == len(mine), 'p243 partition != orbits of x61')
    need(sorted(len(p) for p in parts).count(1) == 27, 'p243 singletons')
    partition_encoding()
    return True

def partition_encoding():
    """Systematic comparison of the p243 input encoding with the frontend's cell
    and singleton-bit indexing.  Returns (singleton_lines, cell_lines): for each
    H bit b the p243 line holding the singleton orbit {idx(hel(b))}, and for each
    nonspecial cell the three p243 line numbers (input order) whose orbits lie in it."""
    data = parse_ints(open(P243).read(), 'p243')
    pos, lines = 7, []
    for _ in range(99):
        n = data[pos]; lines.append(tuple(data[pos+1:pos+1+n])); pos += n+1
    single = {}
    for ln, o in enumerate(lines):
        if len(o) == 1:
            single[o[0]] = ln
    need(set(single) == {idx(hel(b)) for b in range(27)}, 'singleton orbits != H elements')
    sing_lines = [single[idx(hel(b))] for b in range(27)]
    need(len(set(sing_lines)) == 27, 'singleton lines')
    cell_lines = {}
    for ln, o in enumerate(lines):
        if len(o) == 3:
            cs = {cell(from_idx(v)) for v in o}
            need(len(cs) == 1, 'orbit spans cells')
            cell_lines.setdefault(cs.pop(), []).append(ln)
    need(sorted(cell_lines) == NONSPECIAL, 'cells with 3-orbits')
    need(all(len(v) == 3 for v in cell_lines.values()), 'three orbits per cell')
    # S0 bit set -> chosen singleton elements (13 of them)
    chosen = [idx(hel(b)) for b in range(27) if S0 >> b & 1]
    need(len(chosen) == 13, 'S0 size')
    return sing_lines, {c: tuple(v) for c, v in cell_lines.items()}

# ---- 2. singleton layer possibilities and congruences ---------------------------
def layer_possibilities(sols):
    """Derive |D cap H| and admissible ordered layer counts from the moments."""
    # (a) four y,z-quotients: zero coset count forced to 40, giving |D cap H|=13.
    yz_forms = [f for f in FORMS if f[0] == 0]
    need(len(yz_forms) == 4, 'four forms')
    # every element outside H lies in the zero coset of exactly one yz form; H in all four
    for j in range(27):
        c = sum(1 for f in yz_forms if fval(f, j) == 0)
        need(c == (4 if j in SPECIAL else 1), 'yz zero-coset cover')
    # nonspecial cosets get multiples of 3; zero coset gets |S| mod 3; nonzero cosets have 0 mod 3.
    z_vals = set()
    for t in sols:
        if t[1] % 3 == 0 and t[2] % 3 == 0:
            z_vals.add(t[0])
    need(z_vals == {40}, 'zero coset not forced to 40')
    hmeet = (4*40 - K)//3
    need(4*40 - K == 3*hmeet and hmeet == 13, 'h meet')
    # (b) x-layer counts: x quotient (1,0,0): coset counts == layer counts mod 3
    xres = {tuple(c % 3 for c in t) for t in sols}
    need(all(sorted(r) == [0, 0, 1] for r in xres), 'x residues')
    # (c) quotient zero coefficient: sum a(q)^2 = 121+60*8 = 601, nonspecial squares 0 mod 9
    q0 = K + LAM*8
    need(q0 == 601, 'q0')
    trip = [t for t in product(range(10), repeat=3) if sum(t) == hmeet
            and sum(c*c for c in t) % 9 == q0 % 9
            and sorted(c % 3 for c in t) == [0, 0, 1]]
    base = {tuple(sorted(t)) for t in trip}
    need(base == {(0, 4, 9), (3, 4, 6)}, 'layer base %r' % base)
    need(len(trip) == 12, 'layer ordered count')
    return trip

def hmasks_for(layers):
    """All 27-bit masks with the given ordered x-layer popcounts."""
    out = []
    n = [list(itertools.combinations(range(9), c)) for c in layers]
    for p0 in n[0]:
        m0 = sum(1 << b for b in p0)
        for p1 in n[1]:
            m1 = sum(1 << b for b in p1) << 9
            for p2 in n[2]:
                out.append(m0 | m1 | (sum(1 << b for b in p2) << 18))
    return out

# translation of a 27-bit H mask by h in H, via per-layer 9-bit tables
def _layer_table():
    tab = {}
    for hu, hw in product(range(3), repeat=2):
        t = [0]*512
        for m in range(512):
            r = 0
            for b in range(9):
                if m >> b & 1:
                    u, w = b//3, b % 3
                    r |= 1 << (3*((u+hu) % 3)+(w+hw) % 3)
            t[m] = r
        tab[(hu, hw)] = t
    return tab
LT = _layer_table()
def translate(m, h):
    hx, rest = h//9, h % 9
    tab = LT[(rest//3, rest % 3)]
    layers = (m & 511, m >> 9 & 511, m >> 18 & 511)
    r = 0
    for x in range(3):
        r |= tab[layers[x]] << (9*((x+hx) % 3))
    return r
def congruent(m):
    for h in range(1, 27):
        if (m & translate(m, h)).bit_count() % 3:
            return False
    return True

# ---- worker for the all-patterns scan (module level for multiprocessing) ----
def _scan(job):
    layers, i0 = job
    c0 = list(itertools.combinations(range(9), layers[0]))[i0]
    m0 = sum(1 << b for b in c0)
    good = []
    for p1 in itertools.combinations(range(9), layers[1]):
        m1 = sum(1 << b for b in p1) << 9
        for p2 in itertools.combinations(range(9), layers[2]):
            m = m0 | m1 | (sum(1 << b for b in p2) << 18)
            if congruent(m):
                good.append(m)
    return good

def all_patterns_passing(trip, procs):
    jobs = []
    for lay in trip:
        n0 = len(list(itertools.combinations(range(9), lay[0])))
        jobs += [(lay, i) for i in range(n0)]
    total, good = 0, set()
    with Pool(procs) as pool:
        for r in pool.imap_unordered(_scan, jobs, chunksize=1):
            good.update(r)
    return good

def pattern_total(trip):
    from math import comb
    return sum(comb(9, a)*comb(9, b)*comb(9, c) for a, b, c in trip)

# ---- affine automorphisms of G = C3 x C9 x C9 ---------------------------------
def det3(e, f, h, i):
    return (e*i - f*h) % 3
GL2 = [(e, f, h, i) for e, f, h, i in product(range(3), repeat=4) if det3(e, f, h, i)]
assert len(GL2) == 48

def full_map(alpha, b, c, d, g, E, t):
    """Point map phi of G (list of 243 indices).  x'=alpha x+b y+c z+t0 mod 3;
    y'=3d x+e y+f z+3 t1, z'=3g x+h y+i z+3 t2 mod 9.  t=(t0,t1,t2) in 0..2."""
    e, f, h, i = E
    out = []
    for (x, y, z) in ELEMS:
        X = (alpha*x + b*(y % 3) + c*(z % 3) + t[0]) % 3
        Y = (3*d*x + e*y + f*z + 3*t[1]) % 9
        Z = (3*g*x + h*y + i*z + 3*t[2]) % 9
        out.append(idx((X, Y, Z)))
    return out

def from_idx(n):
    return (n//81, n//9 % 9, n % 9)

def validate_affine(phi):
    """phi = list of images.  Checks: bijection; A=phi-phi(0) is additive on the
    generators and has the right orders; A equals the generator formula on all
    of G; (optional) full pairwise additivity is done by validate_full_additive."""
    need(len(phi) == V and sorted(phi) == list(range(V)), 'not a bijection')
    t0 = from_idx(phi[0])
    def A(g):
        r = from_idx(phi[idx(g)])
        return ((r[0]-t0[0]) % 3, (r[1]-t0[1]) % 9, (r[2]-t0[2]) % 9)
    a1, a2, a3 = A((1, 0, 0)), A((0, 1, 0)), A((0, 0, 1))
    need(mul(3, a1) == (0, 0, 0), 'order of image of e1')
    need(mul(9, a2) == (0, 0, 0) and mul(9, a3) == (0, 0, 0), 'order of image of e2/e3')
    for g in ELEMS:
        want = add(add(mul(g[0], a1), mul(g[1], a2)), mul(g[2], a3))
        need(A(g) == want, 'generator formula differs at %r' % (g,))
    return a1, a2, a3

def validate_full_additive(phi):
    t0 = from_idx(phi[0])
    def A(g):
        r = from_idx(phi[idx(g)])
        return ((r[0]-t0[0]) % 3, (r[1]-t0[1]) % 9, (r[2]-t0[2]) % 9)
    img = [A(g) for g in ELEMS]
    for g in ELEMS:
        for h in ELEMS:
            need(img[idx(add(g, h))] == add(img[idx(g)], img[idx(h)]), 'not additive')
    # translation part lies in H (order 3), so phi commutes with x61 exactly
    need(in_H(t0), 'translation phi(0) not in H')
    for g in ELEMS:
        need(from_idx(phi[idx(mul(61, g))]) == mul(61, from_idx(phi[idx(g)])), 'x61 does not commute')

def hmap_mask(phi, m):
    """Image of the 27-bit H subset m under the full map phi."""
    r = 0
    for b in range(27):
        if m >> b & 1:
            n = phi[idx(hel(b))]
            g = from_idx(n)
            need(in_H(g), 'phi(H) not in H')
            r |= 1 << hbit(g)
    return r

def apply_quot(phi):
    """Induced permutation of C3^3 = G/3G, computed from phi; checks well-defined."""
    p = [None]*27
    for n in range(V):
        g = from_idx(n); j = cell(g); k = cell(from_idx(phi[n]))
        need(p[j] is None or p[j] == k, 'quotient map not well defined')
        p[j] = k
    need(sorted(p) == list(range(27)), 'quotient map not bijective')
    return tuple(p)

def hmaps():
    for alpha in (1, 2):
        for d, g in product(range(3), repeat=2):
            for E in GL2:
                for t in product(range(3), repeat=3):
                    yield alpha, d, g, E, t

# ---- 3. quotient enumeration by exact index-three line-sum propagation ----------
def s0_layers():
    return tuple((S0 >> (9*x) & 511).bit_count() for x in range(3))

def quotient_images(prefix=()):
    """All a: C3^3 -> Z with a(0,0,0..)=layer counts of S0 at the special cells,
    a(q) in {0,3,6,9} at the 24 nonspecial cells, such that for each of the 13
    index-three subgroups the three coset sums are a permutation of (36,40,45).
    By Fourier inversion on C3^3 (|chi(a)|^2 = 61 for each nonzero chi, total 121)
    this is equivalent to the full quotient difference equation (re-checked at
    every leaf by direct autocorrelation)."""
    lay = s0_layers()
    need(lay == (4, 3, 6), 'S0 layers %r' % (lay,))
    a = [None]*27
    for x in range(3):
        a[9*x] = lay[x]
    order = [9*x+3*y+z for (y, z) in product(range(3), repeat=2) if (y, z) != (0, 0)
             for x in range(3)]
    need(sorted(order) == sorted(NONSPECIAL), 'order')
    lo = [[0]*3 for _ in FORMS]
    un = [[0]*3 for _ in FORMS]
    for fi, f in enumerate(FORMS):
        for j in range(27):
            t = fval(f, j)
            if a[j] is None:
                un[fi][t] += 1
            else:
                lo[fi][t] += a[j]
    targets = (36, 40, 45)
    perms = list(permutations(targets))
    def feasible(fi):
        L, U = lo[fi], un[fi]
        for p in perms:
            if all(L[t] <= p[t] <= L[t] + 9*U[t] and (p[t]-L[t]) % 3 == 0 for t in range(3)):
                return True
        return False
    ts = [[fval(f, j) for j in range(27)] for f in FORMS]
    out = []
    nodes = [0]
    def rec(k):
        nodes[0] += 1
        if k == len(order):
            for fi in range(13):
                need(tuple(sorted(lo[fi])) == targets, 'leaf line sums')
            out.append(tuple(a))
            return
        j = order[k]
        for v in ((prefix[k],) if k < len(prefix) else (0, 3, 6, 9)):
            a[j] = v
            for fi in range(13):
                t = ts[fi][j]
                un[fi][t] -= 1; lo[fi][t] += v
            if all(feasible(fi) for fi in range(13)):
                rec(k+1)
            for fi in range(13):
                t = ts[fi][j]
                un[fi][t] += 1; lo[fi][t] -= v
        a[j] = None
    rec(0)
    quotient_images.order = order
    return out, nodes[0]

def _qjob(pre):
    return quotient_images(pre)

def check_autocorrelation(a):
    for h in QPTS:
        corr = 0
        for jq, q in enumerate(QPTS):
            r = tuple((u+w) % 3 for u, w in zip(q, h))
            corr += a[jq]*a[QPTS.index(r)]
        need(corr == (601 if h == (0, 0, 0) else 540), 'autocorrelation')
    return True

# ---- coverage of the images by representatives under the 27 quotient maps ----------
def apply_perm(p, a):
    y = [None]*27
    for j in range(27):
        y[p[j]] = a[j]
    return tuple(y)

def check_group(qperms):
    """The orbit {apply_perm(p, a) for p in qperms} is an orbit only if qperms is a
    group: contains the identity and is closed under composition (finite, so inverses follow)."""
    ps = set(qperms)
    need(tuple(range(27)) in ps, 'quotient permutations: no identity')
    for p in ps:
        for q in ps:
            need(tuple(p[q[j]] for j in range(27)) in ps, 'quotient permutations: not closed')

def stabilizer_quotient_maps():
    """Explicit full maps phi: affine automorphisms of G with phi(S0)=S0.
    Returns {quotient permutation: first full map (as list)} and the count of stabilizing
    full-map parameter tuples with b,c free (lift choice e,f,h,i taken in 0..2)."""
    stab = []
    for alpha, d, g, E, t in hmaps():
        phi = full_map(alpha, 0, 0, d, g, E, t)
        if hmap_mask(phi, S0) == S0:
            stab.append((alpha, d, g, E, t))
    qmaps = {}
    for alpha, d, g, E, t in stab:
        for b, c in product(range(3), repeat=2):
            phi = full_map(alpha, b, c, d, g, E, t)
            p = apply_quot(phi)
            if p not in qmaps:
                qmaps[p] = (phi, (alpha, b, c, d, g, E, t))
    return stab, qmaps

# ---- frozen-input checkers (text in, raise Fail on any discrepancy) -----------------
def parse_rows(text, ncols, nrows, what):
    lines = text.split('\n')
    if lines and lines[-1] == '':
        lines.pop()
    need(len(lines) == nrows, '%s: %d rows, expected %d' % (what, len(lines), nrows))
    rows = []
    for ln in lines:
        need(ln == ln.strip() and '  ' not in ln, '%s: whitespace' % what)
        toks = ln.split(' ')
        need(len(toks) == ncols, '%s: %d columns, expected %d' % (what, len(toks), ncols))
        rows.append(parse_ints(ln, what))
        need(all(v >= 0 for v in rows[-1]), '%s: negative' % what)
    return rows

def check_images_text(text, images):
    rows = [tuple(r) for r in parse_rows(text, 27, len(images), 'images')]
    need(len(set(rows)) == len(rows), 'images: duplicate row')
    need(set(rows) == set(images), 'images: set differs from independent enumeration')

def check_cases_text(text, images, qperms):
    check_group(qperms)
    rows = parse_rows(text, 28, 8, 'cases')
    univ = set(images); covered = set(); total = 0
    for r in rows:
        w, a = r[0], tuple(r[1:])
        need(a in univ, 'cases: representative not an image')
        need(a not in covered, 'cases: representative inside earlier orbit')
        orb = {apply_perm(p, a) for p in qperms}
        need(orb <= univ, 'cases: orbit leaves image set')
        need(len(orb) == w, 'cases: weight %d != orbit size %d' % (w, len(orb)))
        need(not (orb & covered), 'cases: overlapping orbits')
        covered |= orb; total += w
    need(covered == univ and total == len(univ), 'cases: union is not the image set')

SING_KEYS = ('maps', 'normalized', 'congruence_pass', 'representatives', 'covered', 'full_weight')

def check_singletons_text(text, exp):
    """Exactly two lines: '<mask> <full_weight>', then the six key=value fields of
    SING_KEYS in that order.  Every field is compared to exp, the recomputation."""
    lines = text.split('\n')
    need(len(lines) == 3 and lines[2] == '', 'singletons: %d lines, expected 2' % (len(lines)-1))
    head = parse_rows(lines[0] + '\n', 2, 1, 'singletons line 1')[0]
    need(head == [exp['mask'], exp['full_weight']], 'singletons line 1: %r' % lines[0])
    need(lines[1] == lines[1].strip() and '  ' not in lines[1], 'singletons line 2: whitespace')
    toks = lines[1].split(' ')
    need(len(toks) == len(SING_KEYS), 'singletons line 2: %d fields' % len(toks))
    for tok, key in zip(toks, SING_KEYS):
        k, sep, v = tok.partition('=')
        need(sep == '=' and k == key, 'singletons line 2: field %r, expected %s' % (tok, key))
        val = parse_ints(v, 'singletons ' + key)
        need(len(val) == 1 and val[0] == exp[key],
             'singletons %s=%s, recomputed %d' % (key, v, exp[key]))

def read(name):
    with open(os.path.join(RECEIPTS, name)) as f:
        return f.read()

def banner(msg):
    print(msg, flush=True)

# ---- subcommands -----------------------------------------------------------------
def cmd_moments(a):
    sols = moments(); trip = layer_possibilities(sols)
    check_partition()
    banner('PASS moments arrangements=%d base=(36,40,45) |D cap H|=13 layer_triples=%d multiplier_orbits=99'
           % (len(sols), len(trip)))
    return sols, trip

def cmd_singletons(a, trip=None):
    if trip is None:
        trip = layer_possibilities(moments())
    total = pattern_total(trip)
    good = all_patterns_passing(trip, a.threads)
    by = {}
    for m in good:
        k = tuple((m >> (9*x) & 511).bit_count() for x in range(3))
        by[k] = by.get(k, 0) + 1
    # affine orbit of S0 under maps of H that extend to full automorphisms; also
    # collect, as bit permutations of H, those that keep every x-layer in place
    orbit = set(); nmaps = 0; layer_fixing = set()
    for alpha, d, g, E, t in hmaps():
        phi = full_map(alpha, 0, 0, d, g, E, t)
        validate_affine(phi)
        nmaps += 1
        orbit.add(hmap_mask(phi, S0))
        p = tuple(hbit(from_idx(phi[idx(hel(b))])) for b in range(27))
        if all(p[b]//9 == b//9 for b in range(27)):
            layer_fixing.add(p)
    need(S0 in good, 'S0 not congruence-passing')
    need(orbit == good, 'affine orbit of S0 (%d) != passing set (%d)' % (len(orbit), len(good)))
    # normalized layer orders of the frozen file: layer 0 holds 4, one per base multiset
    norm = [t for t in trip if t[0] == 4 and t[1] < t[2]]
    need(sorted(norm) == [(4, 0, 9), (4, 3, 6)], 'normalized orders %r' % norm)
    ngood = {m for m in good if tuple((m >> (9*x) & 511).bit_count() for x in range(3)) in norm}
    # partition the normalized passing set into orbits under the layer-fixing maps
    seen = set(); reps = []; covered = 0
    for m in sorted(ngood):
        if m in seen:
            continue
        orb = set()
        for p in layer_fixing:
            orb.add(sum(1 << p[b] for b in range(27) if m >> b & 1))
        seen |= orb; covered += len(orb); reps.append(m)
    need(seen == ngood, 'layer-fixing orbits leave the normalized passing set')
    sing = {'mask': S0, 'full_weight': len(good), 'maps': len(layer_fixing),
            'normalized': pattern_total(norm), 'congruence_pass': len(ngood),
            'representatives': len(reps), 'covered': covered}
    banner('PASS patterns_total=%d congruence_pass=%d by_layers=%s affine_maps_validated=%d orbit=%d '
           'layer_fixing_maps=%d normalized=%d normalized_pass=%d representatives=%d covered=%d'
           % (total, len(good), sorted(by.items()), nmaps, len(orbit), sing['maps'],
              sing['normalized'], sing['congruence_pass'], sing['representatives'], covered))
    LAST_GOOD.update(good)
    return sing

def cmd_quotients(a):
    if a.threads > 1:
        with Pool(a.threads) as pool:
            res = pool.map(_qjob, list(product((0, 3, 6, 9), repeat=6)), chunksize=8)
        images = [im for r in res for im in r[0]]; nodes = sum(r[1] for r in res)
    else:
        images, nodes = quotient_images()
    need(len(set(images)) == len(images), 'duplicate images')
    for im in images:
        check_autocorrelation(im)
    vals = {v for im in images for j, v in enumerate(im) if j not in SPECIAL}
    sixes = {sum(1 for j, v in enumerate(im) if j not in SPECIAL and v == 6) for im in images}
    banner('PASS quotient_images=%d dfs_nodes=%d nonspecial_values=%s sixes_per_image=%s'
           % (len(images), nodes, sorted(vals), sorted(sixes)))
    return images

def cmd_maps(a, images=None):
    stab, qmaps = stabilizer_quotient_maps()
    nfull = 0
    for p, (phi, par) in qmaps.items():
        validate_affine(phi); validate_full_additive(phi)
        need(hmap_mask(phi, S0) == S0, 'map does not preserve S0')
        need(apply_quot(phi) == p, 'quotient permutation mismatch')
        nfull += 1
    check_group(qmaps)
    banner('PASS stabilizing_Hmaps=%d quotient_permutations=%d full_maps_fully_validated=%d'
           % (len(stab), len(qmaps), nfull))
    return list(qmaps)

def cmd_coverage(a):
    images = cmd_quotients(a)
    qperms = cmd_maps(a)
    orb_total = 0; seen = set(); reps = []
    for im in sorted(images):
        if im in seen:
            continue
        orb = {apply_perm(p, im) for p in qperms}
        need(orb <= set(images), 'orbit leaves image set')
        seen |= orb; orb_total += len(orb); reps.append((len(orb), im))
    need(seen == set(images), 'coverage')
    banner('PASS representatives=%d orbit_sizes=%s covered=%d' % (len(reps), sorted(r[0] for r in reps), orb_total))
    return images, qperms

def frozen_all(a, images, qperms, sing):
    check_images_text(read('images.txt'), images)
    check_cases_text(read('cases.txt'), images, qperms)
    check_singletons_text(read('singletons.txt'), sing)
    check_partition()
    banner('PASS frozen inputs match independent recomputation')

def singleton_mutations(s1, s2):
    """Mutations of the two singletons.txt lines; every one must be rejected."""
    mask, fw = s1.split(' ')
    return [
        ('singletons valid-format: line 2 congruence_pass=1295',
         s1+'\n'+s2.replace('congruence_pass=1296', 'congruence_pass=1295')+'\n'),
        ('singletons valid-format: line 2 dropped', s1+'\n'),
        ('singletons valid-format: line 1 wrong full weight', '%s %d\n%s\n' % (mask, int(fw)-1, s2)),
        ('singletons valid-format: line 1 wrong mask', '%d %s\n%s\n' % (int(mask)+1, fw, s2)),
        ('singletons valid-format: line 2 maps=3887', s1+'\n'+s2.replace('maps=3888', 'maps=3887')+'\n'),
        ('singletons valid-format: line 2 normalized=889181',
         s1+'\n'+s2.replace('normalized=889182', 'normalized=889181')+'\n'),
        ('singletons valid-format: line 2 representatives=2',
         s1+'\n'+s2.replace('representatives=1', 'representatives=2')+'\n'),
        ('singletons valid-format: line 2 covered=1295', s1+'\n'+s2.replace('covered=1296', 'covered=1295')+'\n'),
        ('singletons valid-format: line 2 full_weight=7775',
         s1+'\n'+s2.replace('full_weight=7776', 'full_weight=7775')+'\n'),
        ('singletons malformed: line 2 fields reordered', s1+'\n'+' '.join(reversed(s2.split(' ')))+'\n'),
        ('singletons malformed: line 2 extra field', s1+'\n'+s2+' extra=0\n'),
        ('singletons malformed: extra line', s1+'\n'+s2+'\n'+s2+'\n'),
        ('singletons malformed: line 1 only, old format', s1),
        ('singletons malformed: leading zero', s1+'\n'+s2.replace('maps=3888', 'maps=03888')+'\n'),
        ('singletons malformed: empty', ''), ('singletons malformed: junk', 'a b\nc d\n'),
    ]

def cmd_mutations(a, images, qperms, sing_exp):
    img = read('images.txt'); cas = read('cases.txt'); sing = read('singletons.txt')
    il = img.split('\n')[:-1]; cl = cas.split('\n')[:-1]
    def swap_two(line, first=1):
        t = line.split(' ')
        pos = [i for i in range(first, len(t)) if t[i] in ('3', '6')]
        i = next(i for i in pos if t[i] == '3'); j = next(i for i in pos if t[i] == '6')
        t[i], t[j] = t[j], t[i]
        return ' '.join(t)
    muts = [   # (name, function, text, must_reject)
        ('images valid-format: swap 3/6 in row', check_images_text, '\n'.join([swap_two(il[0])]+il[1:])+'\n', 1),
        ('images valid-format: duplicate a row', check_images_text, '\n'.join(il[:-1]+[il[0]])+'\n', 1),
        ('images valid-format: change 4 to 5', check_images_text, '\n'.join(['5'+il[0][1:]]+il[1:])+'\n', 1),
        ('images valid-format: row swapped for another valid-looking one', check_images_text,
         '\n'.join(il[:-1]+[swap_two(il[-1])])+'\n', 1),
        ('images valid-format: drop a row', check_images_text, '\n'.join(il[1:])+'\n', 1),
        ('images malformed: extra column', check_images_text, il[0]+' 3\n'+'\n'.join(il[1:])+'\n', 1),
        ('images malformed: non-integer', check_images_text, il[0].replace('6', 'x', 1)+'\n'+'\n'.join(il[1:])+'\n', 1),
        ('images malformed: negative', check_images_text, il[0].replace('6', '-6', 1)+'\n'+'\n'.join(il[1:])+'\n', 1),
        ('images malformed: leading zero', check_images_text, il[0].replace(' 6', ' 06', 1)+'\n'+'\n'.join(il[1:])+'\n', 1),
        ('images malformed: empty', check_images_text, '', 1),
        ('images malformed: double space', check_images_text, il[0].replace(' ', '  ', 1)+'\n'+'\n'.join(il[1:])+'\n', 1),
    ]
    results = []
    for name, fn, text, must in muts:
        try:
            fn(text, images); rej = False
        except Fail:
            rej = True
        need(rej == bool(must), 'mutation not handled as expected: ' + name)
        results.append(name)
    cmuts = [
        ('cases valid-format: weight 27->26', '\n'.join(['26'+cl[0][2:]]+cl[1:])+'\n'),
        ('cases valid-format: swap 3/6 in representative', '\n'.join([swap_two(cl[0])]+cl[1:])+'\n'),
        ('cases valid-format: two rows exchanged weights', '\n'.join([cl[0].replace('27', '9', 1)]+[cl[1]]+cl[2:])+'\n'),
        ('cases valid-format: duplicate representative', '\n'.join(cl[:-1]+[cl[0]])+'\n'),
        ('cases valid-format: drop a row', '\n'.join(cl[1:])+'\n'),
        ('cases malformed: missing weight', '\n'.join([cl[0][3:]]+cl[1:])+'\n'),
        ('cases malformed: junk token', '\n'.join(cl[:-1]+[cl[-1]+' z'])+'\n'),
        ('cases malformed: empty', ''),
    ]
    for name, text in cmuts:
        try:
            check_cases_text(text, images, qperms); rej = False
        except Fail:
            rej = True
        need(rej, 'mutation accepted: ' + name)
        results.append(name)
    # semantically equivalent alternative representative of the same orbit must be accepted
    first = tuple(map(int, cl[0].split(' ')[1:]))
    alt = sorted(apply_perm(p, first) for p in qperms)[-1]
    check_cases_text('\n'.join([cl[0].split(' ')[0]+' '+' '.join(map(str, alt))]+cl[1:])+'\n', images, qperms)
    s1, s2 = sing.split('\n')[:2]
    for name, text in singleton_mutations(s1, s2):
        try:
            check_singletons_text(text, sing_exp); rej = False
        except Fail:
            rej = True
        need(rej, 'mutation accepted: ' + name)
        results.append(name)
    # corrupted partition input
    p_orig = open(P243).read()
    tmpdir = tempfile.TemporaryDirectory()
    for name, text in [('p243 malformed: truncated', p_orig[:len(p_orig)//2]),
                       ('p243 valid-format: element changed', p_orig.replace('3 1 4 7', '3 1 4 8', 1)),
                       ('p243 valid-format: header changed', p_orig.replace('121 60 99', '121 61 99', 1))]:
        tmp = os.path.join(tmpdir.name, 'mut_p243.txt')
        open(tmp, 'w').write(text)
        try:
            ok = True
            try:
                parts = read_p243(tmp)
                need(set(parts) == {frozenset(idx(g) for g in o) for o in orbits61()}, 'partition')
            except Fail:
                ok = False
        finally:
            os.remove(tmp)
        need(not ok, 'mutation accepted: ' + name)
        results.append(name)
    tmpdir.cleanup()
    banner('PASS rejected_mutations=%d (plus one equivalent-representative accepted)' % len(results))

def singleton_cover():
    """mask -> parameters (alpha,d,g,e,f,h,i,t0,t1,t2) of one H-map taking S0 to it."""
    cover = {}
    for alpha, d, g, E, t in hmaps():
        phi = full_map(alpha, 0, 0, d, g, E, t)
        m = hmap_mask(phi, S0)
        if m not in cover:
            cover[m] = (alpha, d, g) + tuple(E) + tuple(t)
    return cover

def cmd_export(a, out, images, qperms, good):
    import json
    stab, qmaps = stabilizer_quotient_maps()
    maps = []
    for p, (phi, par) in sorted(qmaps.items()):
        alpha, b, c, d, g, E, t = par
        maps.append(dict(params=[alpha, b, c, d, g] + list(E) + list(t), phi=phi, qperm=list(p)))
    need(len(maps) == 27, 'map count')
    qlist = [m['qperm'] for m in maps]
    reps, assign = [], {}
    for im in sorted(images):
        if im in assign:
            continue
        r = len(reps)
        for mi, p in enumerate(qlist):
            assign.setdefault(apply_perm(p, im), (r, mi))
        reps.append(list(im))
    need(set(assign) == set(images), 'coverage')
    imgs = sorted(images)
    cover = singleton_cover()
    need(set(cover) == set(good), 'singleton cover != passing set')
    sing_lines, cell_lines = partition_encoding()
    cert = dict(
        group=[3, 9, 9], S0=S0, s0_layers=list(s0_layers()),
        maps=maps, images=[list(i) for i in imgs], representatives=reps,
        image_cover=[[r, mi] for r, mi in (assign[i] for i in imgs)],
        singleton_cover=[[m] + list(cover[m]) for m in sorted(cover)],
        singleton_lines_by_bit=sing_lines,
        cell_orbit_lines={str(k): list(v) for k, v in sorted(cell_lines.items())})
    with open(out, 'w') as f:
        json.dump(cert, f, separators=(',', ':'))
    banner('EXPORT maps=%d images=%d reps=%d singleton_cover=%d' % (
        len(maps), len(imgs), len(reps), len(cover)))

def cmd_qslice(a):
    """Fixed slice of the quotient DFS under a prefix, compared with frozen images."""
    pre = tuple(int(v) for v in a.prefix.split(',')) if a.prefix else ()
    imgs, nodes = quotient_images(pre)
    order = quotient_images.order
    frozen = {tuple(r) for r in parse_rows(read('images.txt'), 27, 144, 'images')}
    want = {i for i in frozen if all(i[order[k]] == pre[k] for k in range(len(pre)))}
    need(set(imgs) == want, 'slice solutions differ from frozen images with this prefix')
    banner('PASS qslice prefix=%s solutions=%d nodes=%d' % (a.prefix, len(imgs), nodes))

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('cmd', choices=['moments', 'singletons', 'quotients', 'maps', 'coverage',
                                    'frozen', 'mutations', 'all', 'export', 'qslice'])
    ap.add_argument('--out', default='frontend_certificate.json')
    ap.add_argument('--prefix', default='')
    ap.add_argument('--threads', type=int, default=os.cpu_count() or 1)
    a = ap.parse_args()
    try:
        if a.cmd == 'moments': cmd_moments(a)
        elif a.cmd == 'singletons': cmd_singletons(a)
        elif a.cmd == 'quotients': cmd_quotients(a)
        elif a.cmd == 'maps': cmd_maps(a)
        elif a.cmd == 'coverage': cmd_coverage(a)
        elif a.cmd == 'qslice': cmd_qslice(a)
        else:
            sols, trip = cmd_moments(a)
            sing = cmd_singletons(a, trip)
            images, qperms = cmd_coverage(a)
            if a.cmd in ('frozen', 'all'):
                frozen_all(a, images, qperms, sing)
            if a.cmd in ('mutations', 'all'):
                cmd_mutations(a, images, qperms, sing)
            if a.cmd in ('export', 'all'):
                cmd_export(a, a.out, images, qperms, LAST_GOOD)
    except Fail as e:
        print('FAIL', e); sys.exit(1)
    banner('DONE')

if __name__ == '__main__':
    main()
