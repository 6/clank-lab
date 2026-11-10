"""Exact check of the six explicit billiard paths, in coordinates over Q(zeta), written
independently of paths_sqrt5.py.

Points and vectors are complex numbers in Q(zeta), zeta = exp(2 pi i / 5), stored as rational
coordinates on 1, zeta, zeta^2, zeta^3; the pentagon's vertices are zeta^k, wall k joins zeta^k
to zeta^(k+1). Reflection in wall k sends a vector d to -zeta^(2k+1) * conj(d); rotation by
72 degrees is multiplication by zeta. Real quantities are reduced to Q(sqrt5) to decide signs.
usage: python3 paths_zeta.py small-paths.json
"""
import json, sys
from fractions import Fraction as F

def mul(x, y):
    r = [F(0)] * 8
    for i in range(4):
        for j in range(4):
            r[i + j] += x[i] * y[j]
    for k in range(7, 3, -1):            # zeta^k = zeta^(k-5) * zeta^5, zeta^4 = -(1 + zeta + zeta^2 + zeta^3)
        c = r[k]; r[k] = F(0)
        if k >= 5: r[k - 5] += c
        else:
            for m in range(4): r[m] -= c
    return tuple(r[:4])
def add(x, y): return tuple(a + b for a, b in zip(x, y))
def sub(x, y): return tuple(a - b for a, b in zip(x, y))
ONE = (F(1), F(0), F(0), F(0))
def zpow(k):
    k %= 5
    if k == 4: return (F(-1),) * 4
    return tuple(F(int(i == k)) for i in range(4))
def conj(x):                              # zeta^k -> zeta^(5-k)
    r = (F(0),) * 4
    for k in range(4): r = add(r, tuple(x[k] * c for c in zpow(-k)))
    return r
ETA = add(zpow(1), zpow(4))               # 2 cos 72 = (sqrt5 - 1)/2
SQ5 = add(add(ETA, ETA), ONE)             # sqrt5 in Q(zeta)
ISIN = tuple(c / 2 for c in sub(zpow(1), zpow(4)))    # i sin 72
def from_q5(a, b): return add(tuple(F(a) * c for c in ONE), tuple(F(b) * c for c in SQ5))
def to_q5(r):                             # real element p + q eta  ->  (p - q/2) + (q/2) sqrt5
    assert r[1] == 0 and r[2] == r[3], "not real"
    q = -r[2]; p = r[0] + q
    return (p - q / 2, q / 2)
def sgn(r):
    a, b = to_q5(r)
    if a == 0 and b == 0: return 0
    if a >= 0 and b >= 0: return 1
    if a <= 0 and b <= 0: return -1
    return (1 if a * a > 5 * b * b else -1) * (1 if a > 0 else -1)
def qdiv(x, y):                           # x / y for real x, y, result in Q(zeta)
    a, b = to_q5(x); c, d = to_q5(y); n = c * c - 5 * d * d
    return from_q5((a * c - 5 * b * d) / n, (b * c - a * d) / n)
ZD = sub(zpow(1), zpow(4))                # 2 i sin 72, positive imaginary
def inv_zd():                             # 1/(zeta - zeta^4) = -i/(2 sin72): find by solving zd * w = 1
    # w = conj(zd)/|zd|^2, |zd|^2 = zd*conj(zd) real
    n = mul(ZD, conj(ZD)); a, b = to_q5(n); m = a * a - 5 * b * b
    return mul(conj(ZD), from_q5(a / m, -b / m))
IZD = inv_zd()
def cr(x, y):                             # Im(conj(x) y) / sin72, a real element
    return mul(sub(mul(conj(x), y), mul(x, conj(y))), IZD)

def run(wall, p, d, cap):
    states = [(wall, p, d)]; w, q = wall, p
    for _ in range(cap):
        hit = None
        for i in range(5):
            if i == w: continue
            e = sub(zpow(i + 1), zpow(i)); den = cr(d, e)
            if sgn(den) == 0: continue
            z = sub(zpow(i), q); t = qdiv(cr(z, e), den); u = qdiv(cr(z, d), den)
            if sgn(t) <= 0 or sgn(u) < 0 or sgn(sub(u, ONE)) > 0: continue
            if sgn(u) == 0 or sgn(sub(u, ONE)) == 0: return None, "vertex"
            if hit is None or sgn(sub(t, hit[0])) < 0: hit = (t, i)
        if hit is None: return None, "escape"
        t, w = hit; q = add(q, mul(t, d)); d = mul(tuple(-c for c in zpow(2 * w + 1)), conj(d))
        if (w, q, d) == states[0]: return states, "closed"
        states.append((w, q, d))
    return None, "open"

def main(path):
    fails = []; got = set()
    for c in json.load(open(path)):
        l = c["l"]; (xa, xb), (ya, yb) = c["dir"]
        d = add(from_q5(F(xa), F(xb)), mul(from_q5(F(ya), F(yb)), ISIN))   # x + i sin72 * Y
        w = c["wall"]; u0 = F(c["u0"])
        if not (0 < u0 < 1): fails.append((l, "u0")); continue
        p = add(zpow(w), tuple(u0 * k for k in sub(zpow(w + 1), zpow(w))))
        st, why = run(w, p, d, 2 * l + 5)
        if st is None or len(st) != 2 * l: fails.append((l, why, None if st is None else len(st))); continue
        rp, rd = mul(zpow(1), p), mul(zpow(1), d)
        if any(q == rp and dd == rd for _, q, dd in st): fails.append((l, "5-fold symmetric")); continue
        got.add(l)
    if got != {4, 5, 15, 21, 29, 51}: fails.append(("set", sorted(got)))
    print("paths (Q(zeta) checker): period-2l asymmetric paths for l in", sorted(got))
    if fails: print("FAIL", fails); sys.exit(1)
    print("PASS (paths)")

if __name__ == "__main__":
    main(sys.argv[1])
