#!/usr/bin/env python3
"""Exact check of the six explicit billiard paths, in coordinates over Q(sqrt5).

A point (x, y) of the plane is stored as (X, Y) with x = X and y = s*Y, s = sin 72 degrees, and
X, Y in Q(sqrt5). The pentagon's vertex k is at angle 72k degrees and wall k joins vertex k to
vertex k+1. For each path in the certificate the checker follows the billiard flow exactly: the
next wall is the nearest positive collision, a hit at a vertex rejects the path, and the run stops
at the first return of the full state (wall, point, direction). It requires that return after
exactly 2l bounces, and that rotation by 72 degrees does not map the oriented path to itself.
usage: python3 paths_sqrt5.py small-paths.json ; exit status 0 only if all six paths check."""
import sys, json
from fractions import Fraction as Fr

fail = []

class R5:
    __slots__ = ("a", "b")
    def __init__(s, a, b=0): s.a, s.b = Fr(a), Fr(b)
    def __add__(s, o): return R5(s.a + o.a, s.b + o.b)
    def __sub__(s, o): return R5(s.a - o.a, s.b - o.b)
    def __mul__(s, o): return R5(s.a * o.a + 5 * s.b * o.b, s.a * o.b + s.b * o.a)
    def __truediv__(s, o):
        n = o.a * o.a - 5 * o.b * o.b
        return s * R5(o.a / n, -o.b / n)
    def __eq__(s, o): return s.a == o.a and s.b == o.b
    def sgn(s):
        a, b = s.a, s.b
        if a == 0 and b == 0: return 0
        if a >= 0 and b >= 0: return 1
        if a <= 0 and b <= 0: return -1
        return (1 if a * a > 5 * b * b else -1) * (1 if a > 0 else -1)
SS = R5(Fr(5, 8), Fr(1, 8))           # sin^2 72 = (10 + 2 sqrt5)/16
CO = R5(Fr(-1, 4), Fr(1, 4))          # cos 72
CO2 = R5(Fr(-1, 4), Fr(-1, 4))        # cos 144 ; sin 144 = s * 2 cos 72
P5 = [(R5(1), R5(0)), (CO, R5(1)), (CO2, CO * R5(2)), (CO2, CO * R5(-2)), (CO, R5(-1))]
def vsub(p, q): return (p[0] - q[0], p[1] - q[1])
def vadd(p, q): return (p[0] + q[0], p[1] + q[1])
def vmul(k, p): return (k * p[0], k * p[1])
def dotp(p, q): return p[0] * q[0] + SS * p[1] * q[1]
def crs(p, q): return p[0] * q[1] - p[1] * q[0]
def simulate(wall, u0, dvec, maxn):
    p = vadd(P5[wall], vmul(u0, vsub(P5[(wall + 1) % 5], P5[wall])))
    start = (wall, p, dvec); states = [start]; w, q, d = start
    for _ in range(maxn):
        best = None
        for i in range(5):
            if i == w: continue
            e = vsub(P5[(i + 1) % 5], P5[i]); den = crs(d, e)
            if den.sgn() == 0: continue
            z = vsub(P5[i], q); t = crs(z, e) / den; u = crs(z, d) / den
            if t.sgn() <= 0 or u.sgn() < 0 or (u - R5(1)).sgn() > 0: continue
            if u.sgn() == 0 or (u - R5(1)).sgn() == 0: return None          # vertex hit
            if best is None or (t - best[0]).sgn() < 0: best = (t, i)
        t, i = best
        q = vadd(q, vmul(t, d)); e = vsub(P5[(i + 1) % 5], P5[i])
        d = vsub(vmul(R5(2) * dotp(d, e) / dotp(e, e), e), d); w = i
        same = lambda d1, d2: crs(d1, d2).sgn() == 0 and dotp(d1, d2).sgn() > 0
        if w == start[0] and q == start[1] and same(d, start[2]): return states
        states.append((w, q, d))
    return None
def rot72(p): return (p[0] * CO - SS * p[1], p[0] + p[1] * CO)
def check_paths(path):
    want = {4, 5, 15, 21, 29, 51}; got = set()
    for c in json.load(open(path)):
        l = c["l"]; dv = tuple(R5(Fr(x), Fr(y)) for x, y in c["dir"])
        st = simulate(c["wall"], R5(Fr(c["u0"])), dv, 2 * l + 5)
        if st is None or len(st) != 2 * l: fail.append(("path-period", l)); continue
        # 5-fold symmetry test: is the rotated initial state on the trajectory?
        w0, p0, d0 = st[0]; rp, rd = rot72(p0), rot72(d0)
        sym = any(q == rp and crs(d, rd).sgn() == 0 and dotp(d, rd).sgn() > 0 for _, q, d in st)
        if sym: fail.append(("path-symmetric", l)); continue
        got.add(l)
    if got != want: fail.append(("paths", sorted(want - got)))
    print(f"paths: asymmetric periodic paths of period 2l verified for l in {sorted(got)}")

if __name__ == "__main__":
    check_paths(sys.argv[1])
    if fail:
        print("FAIL", fail[:10]); sys.exit(1)
    print("PASS (paths, Q(sqrt5) checker)")
