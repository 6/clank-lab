#!/usr/bin/env python3
"""Independent checker of the N=10 near-sharp three-point certificate.

Standard library only (fractions, json, gzip, re, itertools, math, time).  Imports nothing from the
producer or the frozen recovery code.  Operators are rebuilt from the mathematical definitions
(see SEMANTICS.md); the full residual of
    sym(h) - U'/45 - sum_blocks <F F^T, op_block>
over all orbit rows is recomputed in exact rational arithmetic.

Usage: python3 -I check_certificate.py CERT.json.gz DATA.lean
"""
import gzip, json, re, sys, time, itertools, math, collections
from fractions import Fraction as Fr

CAP = Fr(13, 20)           # replaced by the value parsed from Data.lean in check()
DEG = 18

# ---------------------------------------------------------------- polynomials in (u,v,t): dict exp-tuple -> Fraction
def padd(*ps):
    r = collections.defaultdict(Fr)
    for p in ps:
        for e, c in p.items():
            r[e] += c
    return {e: c for e, c in r.items() if c}
def pscale(p, x):
    return {e: c * x for e, c in p.items() if c * x}
def pmul(p, q):
    r = collections.defaultdict(Fr)
    for e, c in p.items():
        for f, d in q.items():
            r[(e[0]+f[0], e[1]+f[1], e[2]+f[2])] += c * d
    return {e: c for e, c in r.items() if c}
def orbit(p):
    """orbit compression: sum of coefficients over each S3-orbit of exponent triples (keyed by sorted-descending triple)"""
    r = collections.defaultdict(Fr)
    for e, c in p.items():
        r[tuple(sorted(e, reverse=True))] += c
    return {e: c for e, c in r.items() if c}
ONE = {(0, 0, 0): Fr(1)}
U_ = {(1, 0, 0): Fr(1)}
V_ = {(0, 1, 0): Fr(1)}
T_ = {(0, 0, 1): Fr(1)}

def row_list():
    """rows = sorted-descending exponent triples of total degree <= 18, in lexicographic order"""
    s = set()
    for a in range(DEG + 1):
        for b in range(a + 1):
            for c in range(b + 1):
                if a + b + c <= DEG:
                    s.add((a, b, c))
    return sorted(s)

# ---------------------------------------------------------------- moment (Cohn-Woo / Bachoc-Vallentin) blocks, S^2
def qk_polys(K):
    """q_k = (1-u^2)^{k/2}(1-v^2)^{k/2} T_k(z/sqrt(w)),  z = t-uv, w=(1-u^2)(1-v^2); q_0=1,q_1=z,q_k=2z q_{k-1}-w q_{k-2}"""
    z = padd(T_, pscale(pmul(U_, V_), -1))
    w = pmul(padd(ONE, pscale(pmul(U_, U_), -1)), padd(ONE, pscale(pmul(V_, V_), -1)))
    q = [ONE, z]
    for k in range(2, K):
        q.append(padd(pscale(pmul(z, q[-1]), 2), pscale(pmul(w, q[-2]), -1)))
    return q

def moment_op_entry(i, j, qk):
    """Entry (i,j) of the k-th moment-block operator, as an orbit-row vector.
    S_ij(a,x,y) = u^i v^j q_k, u=<a,x>, v=<a,y>, t=<x,y>.  The Gram form sum over ALL ordered triples (a,x,y) of X^3 is PSD
    (vectors V_i(a)=sum_x u^i (1-u^2)^{k/2} e^{ik phi_x}).  Divide by 90.
      distinct ordered triples: 720 * Lambda(p)  ->  8 * orbit(p)
      two equal (a!=b, s=<a,b>): the three patterns (u,v,t) = (1,s,s),(s,1,s),(s,s,1), each over 90 ordered pairs
           = 2*sum_{unordered pairs}; and  sum_pairs s^m = 45 * Lambda(s^m)   ->  rows (m,0,0) with weight 1 per pattern
      all equal (10 triples): p(1,1,1)*10/90 = p(1,1,1)/9   -> row (0,0,0)
    """
    p = pmul({(i, j, 0): Fr(1)}, qk)
    c = pscale(orbit(p), 8)
    boundary = collections.defaultdict(Fr)
    for e, v in p.items():
        boundary[(e[1] + e[2], 0, 0)] += v      # pattern u=1 : (1,s,s)
        boundary[(e[0] + e[2], 0, 0)] += v      # pattern v=1 : (s,1,s)
        boundary[(e[0] + e[1], 0, 0)] += v      # pattern t=1 : (s,s,1)
    # orbit rows are keyed by sorted exponents: (m,0,0) already sorted-descending
    out = padd(c, dict(boundary), {(0, 0, 0): sum(p.values()) / 9})
    return out

# ---------------------------------------------------------------- SOS localizers
def exps(d):
    return [(i, j, k) for i in range(d + 1) for j in range(d - i + 1) for k in range(d - i - j + 1)]

def sos_bases(d, full):
    es = exps(d)
    if full:   # fully S3-symmetric monomial sums
        orbs = sorted(set(tuple(sorted(e, reverse=True)) for e in es))
        even = [{e: Fr(1) for e in set(itertools.permutations(r))} for r in orbs]
    else:      # symmetric under v<->t
        even = []
        for e in es:
            f = (e[0], e[2], e[1])
            if e == f: even.append({e: Fr(1)})
            elif e < f: even.append({e: Fr(1), f: Fr(1)})
    odd = [{e: Fr(1), (e[0], e[2], e[1]): Fr(-1)} for e in es if e < (e[0], e[2], e[1])]   # antisymmetric under v<->t
    return even, odd

def sos_specs(cap):
    gram = padd(ONE, {(1, 1, 1): Fr(2), (2, 0, 0): Fr(-1), (0, 2, 0): Fr(-1), (0, 0, 2): Fr(-1)})   # Gram determinant >= 0
    lower = padd(U_, ONE)                     # 1+u >= 0
    upper = padd(pscale(ONE, cap), pscale(U_, -1))   # cap-u >= 0
    b = pmul(lower, upper)
    specs = []
    for g, d, full in [(ONE, 9, True), (lower, 8, False), (upper, 8, False), (gram, 7, True), (b, 8, False), (pmul(gram, b), 6, False)]:
        for basis in sos_bases(d, full):
            specs.append((g, basis))
    return specs

def build_operators(cap, log=print):
    """returns {face_index: (size, [(i,j,mult,orbit_poly)])}.  faces 0..9 moment k=face; faces 10..21 SOS."""
    t0 = time.time()
    ops = {}
    q = qk_polys(10)
    for k in range(10):
        n = 10 - k
        ops[k] = (n, [(i, j, 1 if i == j else 2, moment_op_entry(i, j, q[k])) for i in range(n) for j in range(i, n)])
    for idx, (g, basis) in enumerate(sos_specs(cap)):
        m = len(basis)
        ent = []
        for i in range(m):
            gb = pmul(g, basis[i])
            for j in range(i, m):
                ent.append((i, j, 1 if i == j else 2, orbit(pmul(gb, basis[j]))))
        ops[10 + idx] = (m, ent)
    log('operators built in %.1fs' % (time.time() - t0))
    return ops

# ---------------------------------------------------------------- rigorous interval arithmetic on Fractions (candidate energy)
PBITS = 420
def isqrt_lo(x):   # lower bound of sqrt(x) at 2^-PBITS, x>=0 Fraction
    n = (x.numerator << (2 * PBITS)) // x.denominator
    return Fr(math.isqrt(n), 1 << PBITS)
def isqrt_hi(x):
    n = -((-x.numerator << (2 * PBITS)) // x.denominator)
    return Fr(math.isqrt(n) + 1, 1 << PBITS)
class Iv:
    def __init__(s, lo, hi=None):
        s.lo = Fr(lo); s.hi = Fr(lo if hi is None else hi); assert s.lo <= s.hi
    def __add__(s, o): o = o if isinstance(o, Iv) else Iv(o); return Iv(s.lo + o.lo, s.hi + o.hi)
    __radd__ = __add__
    def __neg__(s): return Iv(-s.hi, -s.lo)
    def __sub__(s, o): o = o if isinstance(o, Iv) else Iv(o); return s + (-o)
    def __mul__(s, o):
        o = o if isinstance(o, Iv) else Iv(o)
        c = [s.lo*o.lo, s.lo*o.hi, s.hi*o.lo, s.hi*o.hi]; return Iv(min(c), max(c))
    __rmul__ = __mul__
    def sqrt(s):
        assert s.lo >= 0; return Iv(isqrt_lo(s.lo), isqrt_hi(s.hi))
    def inv(s):
        assert s.lo > 0; return Iv(1 / s.hi, 1 / s.lo)

def candidate_energy_upper(hlo, hhi):
    """upper bound of the Coulomb energy of the candidate (Candidate.lean coordinates) for h in [hlo,hhi]"""
    h = Iv(hlo, hhi)
    rho = (Iv(1) - h * h).sqrt()
    q = rho * Iv(2).sqrt() * Iv(Fr(1, 2))
    z = Iv(0)
    P = [(z, z, Iv(1)), (z, z, Iv(-1)),
         (rho, z, h), (z, rho, h), (-rho, z, h), (z, -rho, h),
         (q, q, -h), (-q, q, -h), (-q, -q, -h), (q, -q, -h)]
    tot = Iv(0)
    for a in range(10):
        for b in range(a + 1, 10):
            d2 = Iv(0)
            for c in range(3):
                dd = P[a][c] - P[b][c]; d2 = d2 + dd * dd
            tot = tot + d2.sqrt().inv()
    return tot.hi

# ---------------------------------------------------------------- Data.lean parsing
def parse_data_lean(path):
    s = open(path).read()
    out = {}
    m = re.search(r'def hCoeff[^=]*:=\s*!\[(.*?)\]', s, re.S)
    out['hCoeff'] = [(int(a), int(b)) for a, b in re.findall(r'\((\d+)\s*:\s*ℚ\)\s*/\s*2\s*\^\s*(\d+)', m.group(1))]
    def rat(name):
        m = re.search(r'^def %s\s*:\s*ℚ\s*:=\s*(.*)$' % name, s, re.M)
        expr = m.group(1)
        expr = re.sub(r':\s*ℚ', '', expr).replace('^', '**').replace('(', ' ( ').replace(')', ' ) ')
        # evaluate integer arithmetic only: tokens digits, / ** * parentheses
        if not re.fullmatch(r'[\d\s/\*\(\)]*', expr): raise ValueError(name + ': ' + expr)
        return eval_rat(expr)
    for nm in ['minorantEps', 'certU', 'certLoss', 'pairCap', 'energyCap', 'windowRadius', 'gapBound']:
        out[nm] = rat(nm)
    return out

def eval_rat(expr):
    """tiny exact evaluator for + - * / ** parentheses over integers (no eval())"""
    toks = re.findall(r'\*\*|[()/*]|\d+', expr)
    pos = [0]
    def peek(): return toks[pos[0]] if pos[0] < len(toks) else None
    def nxt(): t = toks[pos[0]]; pos[0] += 1; return t
    def atom():
        t = nxt()
        if t == '(':
            v = expr_(); assert nxt() == ')'; return v
        return Fr(int(t))
    def power():
        b = atom()
        if peek() == '**':
            nxt(); e = power(); assert e.denominator == 1; return b ** int(e)
        return b
    def term():
        v = power()
        while peek() in ('*', '/'):
            o = nxt(); r = power(); v = v * r if o == '*' else v / r
        return v
    def expr_(): return term()
    v = expr_(); assert pos[0] == len(toks); return v

def parse_lean_height(path):
    s = open(path).read()
    r = {}
    for nm in ['heightLower', 'heightUpper']:
        m = re.search(r'def %s : ℚ := (\d+) / (\d+)' % nm, s)
        r[nm] = Fr(int(m.group(1)), int(m.group(2)))
    return r

def frac(s):
    if s.startswith('-'): return -frac(s[1:])
    return eval_rat(s.replace('^', '**')) if '^' in s else Fr(s)

# ---------------------------------------------------------------- the check
def residual_of(cert, ops, rows, cap, report=None):
    """recompute the residual of  sym(h) - U'/45 - sum <F F^T, op>  from cert fields (all exact)"""
    k = cert['k']; eps = frac(cert['eps'])
    RI = {e: i for i, e in enumerate(rows)}
    U = frac(cert['U']); Up = U - 45 * eps
    res = [Fr(0)] * len(rows)
    for j, v in enumerate(cert['h_numerators']):
        res[RI[(j, 0, 0)]] += Fr(int(v), 1 << k)
    res[RI[(0, 0, 0)]] += -eps - Up / 45
    seen = set()
    for b in cert['blocks']:
        idx = b['face_index']
        assert idx not in seen and idx in ops; seen.add(idx)
        n, ent = ops[idx]
        F = [[int(x) for x in row] for row in b['F_numerators']]
        assert len(F) == n == b['rows'] and all(len(r) == b['cols'] for r in F), ('shape', idx)
        # W = F F^T (integers, scale 2^(2k))
        W = [[sum(a * c for a, c in zip(F[i], F[j])) for j in range(n)] for i in range(n)]
        acc = collections.defaultdict(Fr)
        for i, j, mult, p in ent:
            w = W[i][j] * mult
            if w:
                for e, c in p.items():
                    acc[e] += w * c
        for e, c in acc.items():
            res[RI[e]] -= c / (1 << (2 * k))
    return res

def check(cert, data, ops, rows, log=print):
    """returns list of failure strings (empty = PASS)"""
    bad = []
    def ok(cond, msg):
        if not cond: bad.append(msg)
        return cond
    cap = data['pairCap']
    k = cert['k']; eps = frac(cert['eps']); U = frac(cert['U'])
    # row structure
    ok([tuple(e) for e in cert['row_exponents']] == rows, 'row_exponents differ from independently enumerated orbit rows')
    ok(len(rows) == 274, 'row count')
    # h, U, eps against Data.lean
    ok(k == 200, 'k != 200')
    ok(len(cert['h_numerators']) == 17 and all(b == 200 for _, b in data['hCoeff']), 'h degree/denominators')
    ok([int(x) for x in cert['h_numerators']] == [a for a, _ in data['hCoeff']], 'h_numerators != Data.lean hCoeff')
    ok(eps == data['minorantEps'] == Fr(1, 2 ** 130), 'eps != minorantEps')
    ok(U == data['certU'], 'U != certU')
    Up = U - 45 * eps
    ok(frac(cert['Uprime']) == Up, 'Uprime != U - 45 eps')
    ok(cap == Fr(13, 20), 'pairCap != 13/20')
    # residual
    t0 = time.time()
    res = residual_of(cert, ops, rows, cap)
    log('residual recomputed in %.1fs' % (time.time() - t0))
    given = [frac(x) for x in cert['residual']]
    ok(len(given) == len(res), 'residual length')
    nbad = sum(1 for a, b in zip(res, given) if a != b)
    ok(nbad == 0, 'recomputed residual differs from JSON residual in %d rows' % nbad)
    L = sum((abs(x) for x in res), Fr(0))
    ok(L == frac(cert['L']), 'L (recomputed l1 norm) != JSON L')
    loss = 45 * (L + eps)
    ok(loss == frac(cert['loss']), 'loss != 45(L+eps) of JSON')
    ok(loss == data['certLoss'], 'recomputed loss != Data.lean certLoss')
    ok(loss < Fr(1, 10 ** 30), 'certLoss >= 1e-30')
    # candidate energy and U
    hb = [frac(x) for x in cert['h_box']]
    lean_h = parse_lean_height.cache
    ok(hb[0] == lean_h['heightLower'] and hb[1] == lean_h['heightUpper'], 'h_box != Data/Candidate height box')
    ok(hb[1] - hb[0] < Fr(1, 2 ** 300), 'h box too wide')
    Eup = candidate_energy_upper(lean_h['heightLower'], lean_h['heightUpper'])
    log('E(candidate) upper bound over the box = %.60f' % (Eup.numerator * 10**70 // Eup.denominator / 10**70) if False else
        'E(candidate) <= %s...' % str(float(Eup)))
    ok(U >= Eup, 'certU < rigorous upper bound of E(candidate)')
    ok(U - Eup < Fr(1, 2 ** 190), 'certU not tight to E (sanity)')
    ok(U <= Fr(32717, 1000), 'certU > 32717/1000')
    ok(U <= data['energyCap'] == Fr(32717, 1000), 'certU > energyCap')
    return bad, dict(L=L, loss=loss, Eup=Eup, U=U, nres=len(res))

def main():
    cert_path, lean_path = sys.argv[1], sys.argv[2]
    t0 = time.time(); c0 = time.process_time()
    cert = json.load(gzip.open(cert_path, 'rt'))
    data = parse_data_lean(lean_path)
    parse_lean_height.cache = parse_lean_height(lean_path.replace('Data.lean', 'Candidate.lean'))
    rows = row_list()
    ops = build_operators(data['pairCap'])
    bad, info = check(cert, data, ops, rows)
    print('L = %.6e   certLoss = %.6e   (L_float json %.6e)' % (float(info['L']), float(info['loss']), cert['L_float']))
    print('E(candidate) upper bound %.45f  certU %.45f' % (float(info['Eup']), float(info['U'])), '; U - Eup = %.3e' % float(info['U'] - info['Eup']))
    print('wall %.1fs cpu %.1fs' % (time.time() - t0, time.process_time() - c0))
    if bad:
        print('FAIL'); [print(' -', b) for b in bad]; sys.exit(1)
    print('PASS')

if __name__ == '__main__':
    main()
