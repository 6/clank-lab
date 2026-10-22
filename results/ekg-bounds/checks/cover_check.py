"""Independent checker for EKG3.P3.CertifiedCover, written from the Lean
statements (Statement/TheoremTP3.lean, Statement/PiBoundsP3.lean) only.
Every inequality is proved with Arb balls: upper(left) <= / < lower(right).
Usage: check.py CERT.csv.xz [--controls]"""
import sys, csv, lzma, math
from fractions import Fraction as Fr
from flint import arb, ctx

ctx.prec = 256
E0, E1, KFIN = 13328000000, 10**205, 329
PRIMES256 = [p for p in range(2, 256) if all(p % d for d in range(2, int(p**.5) + 1))]
assert len(PRIMES256) == 54 and PRIMES256[-1] == 251  # matches primesBelow256

def A(fr):  # exact rational -> ball
    fr = Fr(fr)
    return arb(fr.numerator) / arb(fr.denominator)

C = A(Fr(103883, 100000)); AA = A(Fr(92129, 100000))
def F(x):
    l = x.log()
    return x / l * (1 + 1 / l + 2 / l**2 + 24 / l**3)
THETA256 = sum((arb(p).log() for p in PRIMES256), arb(0))
J = arb(len(PRIMES256)) - THETA256 / arb(256).log() + C * (arb(256) / arb(256).log() - F(arb(256)))

class X:
    """real number r (Fraction) or sqrt(r), kept exact for case splits."""
    def __init__(s, r, sq=False): s.r = Fr(r); s.sq = sq
    def small(s): return s.r < (65536 if s.sq else 256)
    def val(s):
        v = A(s.r); return v.sqrt() if s.sq else v
    def floor(s):
        n = s.r.numerator // s.r.denominator
        return math.isqrt(n) if s.sq else n

def count(x):
    f = x.floor(); return sum(1 for p in PRIMES256 if p <= f)
def piU(x):
    if x.small(): return arb(count(x))
    v = x.val(); return C * F(v) + J
def piL(x):
    if x.small(): return arb(count(x))
    v = x.val(); l = v.log()
    R = C * v.sqrt() + (C / arb(2).log()) * (l / 3).exp() * l
    t = (AA * v - 5 * l + 5 - R) / l
    if t.lower() < 0:  # max 0 t, as an enclosure
        u = max(t.upper(), arb(0)); return arb(u.mid() / 2, u.mid() / 2 + u.rad())  # encloses [0, upper]
    return t

def bt(y, q):  # y, q naturals
    return (arb(y) + arb(q)**2) / ((arb(q) + 1).log() + A(Fr(107, 100))) + piU(X(q))

class Fail(Exception): pass
tight = {}
def le(name, a, b, strict=False):
    """prove a<b (or a<=b) from enclosures; a,b arb or int/Fraction"""
    a = A(a) if not isinstance(a, arb) else a
    b = A(b) if not isinstance(b, arb) else b
    hi, lo = a.upper(), b.lower()
    ok = hi < lo if strict else hi <= lo
    if not ok: raise Fail(f"{name}: {hi} !< {lo}")
    r = float(a.mid() / b.mid()) if b.mid() != 0 else float('inf')
    if r > tight.get(name, (-1,))[0]: tight[name] = (r,)

def exact_le(name, a, b, strict=False):
    if not (a < b if strict else a <= b): raise Fail(name)
    r = float(Fr(a) / Fr(b)); 
    if r > tight.get(name, (-1,))[0]: tight[name] = (r,)

def check_row(row):
    ea, eb, M, Y, Q, hc, bq = row
    exact_le("ea<eb", ea, eb, True)
    exact_le("6M+7<=Y", 6*M+7, Y)
    M1 = M + 1
    s = 2*arb(M1)**2 + 2*arb(M1)*(arb(M1)**2 + eb).sqrt()
    le("Y<S", arb(Y), s, True)
    S = s
    if not Q >= 3: raise Fail("3<=Q")
    exact_le("Q<=(Y+1/2)/(2(M+1))", Fr(Q), (Fr(Y) + Fr(1, 2)) / (2*M1))
    if not hc >= 15: raise Fail("15<=hc")
    if not bq >= 6: raise Fail("6<=bq")
    pU = piU(X(eb, True))
    le("pU+2+bt<=M", pU + 2 + bt(3*M + 2, bq), arb(M))
    le("hc+2sqrt(hc)(pi+M+4)<ea", arb(hc) + 2*arb(hc).sqrt()*(piU(X(hc, True)) + M + 4), arb(ea), True)
    Ostar = arb((Y + 1)//2) + piU(X(Fr(eb) + Y + 1, True)) + (S - Y + arb(Q)**2) / arb(Q).log()
    Hstar = pU * (pU + M + 5)
    Amin = piL(X(ea)) - 2*piU(X(Fr(eb, 2))) + piL(X(Fr(ea, 3)))
    Amax = piU(X(eb)) - 2*piL(X(Fr(ea, 2))) + piU(X(Fr(eb, 3)))
    le("M+O+1-Amin<ea/13", M + Ostar + 1 - Amin, A(Fr(ea, 13)), True)
    le("Amax+H+2<ea/8", Amax + Hstar + 2, A(Fr(ea, 8)), True)
    le("7S+12(Amax+H+4)<5ea", 7*S + 12*(Amax + Hstar + 4), arb(5*ea), True)
    le("13(eb-Amin+M+O)<28hc", 13*(arb(eb) - Amin + M + Ostar), arb(28*hc), True)

def check_chain(rows, memo):
    a, b = E0, KFIN
    for i, r in enumerate(rows):
        if r[0] != a: raise Fail(f"row {i}: ea != previous eb")
        if r[2] < b: raise Fail(f"row {i}: M decreased / below Kfin")
        if r not in memo:
            check_row(r); memo.add(r)
        a, b = r[1], r[2]
    if not E1 <= a: raise Fail("final eb < 1e205")
    exact_le("final eb vs 1e205 (inverse)", E1, a)

def load(path):
    with lzma.open(path, "rt") as f:
        rd = csv.DictReader(f)
        rows = [tuple(int(d[k]) for k in ("ea", "eb", "M", "Y", "Q", "hc", "bq")) for d in rd]
    return rows

def main():
    rows = load(sys.argv[1]); memo = set()
    check_chain(rows, memo)
    print(f"ACCEPT: {len(rows)} rows; first ea={rows[0][0]}, last eb={rows[-1][1]:.6e}, "
          f"first M={rows[0][2]}, last M={rows[-1][2]}")
    for k, v in tight.items(): print(f"  tightest ratio left/right  {k}: {v[0]:.9f}")
    print("  (ratio<1 means slack; for 'final eb' it is 1e205/eb)")
    if "--controls" in sys.argv:
        def Q_over(r): 
            ea, eb, M, Y, Q, hc, bq = r
            return r[:4] + ((2*Y + 1) // (4*(M + 1)) + 1,) + r[5:]
        k = len(rows) // 2
        def rep(i, f): rr = list(rows); rr[i] = f(rr[i]); return rr
        ctl = {
          "planted gap (one eb changed)": rep(k, lambda r: (r[0], r[1] - 1) + r[2:]),
          "M decreased on one row": rep(k, lambda r: r[:2] + (rows[k-1][2] - 1,) + r[3:]),
          "Q above bound": rep(k, Q_over),
          "bq = 5": rep(k, lambda r: r[:6] + (5,)),
          "hc = 14": rep(k, lambda r: r[:5] + (14,) + r[6:]),
          "first ea moved": rep(0, lambda r: (r[0] + 1,) + r[1:]),
          "final eb < 1e205": rep(len(rows) - 1, lambda r: (r[0], E1 - 1) + r[2:]),
        }
        bad = 0
        for name, rr in ctl.items():
            try: check_chain(rr, memo); print(f"CONTROL NOT REJECTED: {name}"); bad += 1
            except Fail as e: print(f"control rejected: {name}  [{str(e)[:90]}]")
        if bad: sys.exit(1)
if __name__ == "__main__":
    try: main()
    except Fail as e: print("REJECT:", e); sys.exit(1)
