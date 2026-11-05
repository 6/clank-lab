#!/usr/bin/env python3
"""Filipi checker F1 (pure Python, group level; imports nothing from
the other checkers).

Filipi, arXiv 2503.22377, Conjecture 4.1: let G be a group and C a finite
conjugacy class of G with <C> = G.  Then for any c in C there is z in C such
that for all integers k, c^k is central in G iff c^k commutes with z.

This checker takes the certificate's affine maps of B (one block per prime:
w -> T w + v), the map c0 = P o (w -> w + g0) and the group G0 of affine maps
with linear part in <a1, a2> and any translation.  It verifies:
  1. c0 normalises G0, so the G0-class C of c0 is closed under conjugation by
     every element of <G0, c0>, hence by every element of <C>;
  2. <C> is transitive on C (the orbit of c0 under conjugation by a few
     evenly spaced elements of C is all of C), so C is one conjugacy class of G := <C>;
  3. c = c0 violates the conclusion: for every z in C there is k in
     [1, ord(c0)] with c0^k commuting with z but c0^k not central in G.
     Central in G = <C> is tested as commuting with every element of C.
Exit 0 (ACCEPT) only if all three hold: Conjecture 4.1 fails for (G, C).

usage: check_filipi_group.py CERT.json
"""
import json, resource, sys, time

t0 = time.process_time()
cert = json.load(open(sys.argv[1]))
PR = tuple(cert["primes"]); DIM = tuple(cert["dims"])


def reject(why):
    print("REJECT:", why); sys.exit(1)


def matmul(A, B, p):
    n = len(A)
    return tuple(tuple(sum(A[i][k] * B[k][j] for k in range(n)) % p for j in range(n)) for i in range(n))


def matvec(A, x, p):
    return tuple(sum(a * b for a, b in zip(row, x)) % p for row in A)


def mul(f, g):
    """f after g, both tuples of per-block (T, v)."""
    return tuple((matmul(Tf, Tg, p), tuple((a + b) % p for a, b in zip(matvec(Tf, vg, p), vf)))
                 for (Tf, vf), (Tg, vg), p in zip(f, g, PR))


def inv(f):
    out = []
    for (T, v), p in zip(f, PR):
        n = len(T)  # inverse by the adjugate-free route: T^(m-1) where T^m = I
        M = T; Tinv = tuple(tuple(int(i == j) for j in range(n)) for i in range(n))
        I = Tinv
        while M != I:
            Tinv = M; M = matmul(M, T, p)
        # now Tinv * T = I (Tinv = T^(m-1)); for m = 1, T = I and Tinv = I
        out.append((Tinv, tuple((-x) % p for x in matvec(Tinv, v, p))))
    return tuple(out)


def affine(Ts, vs):
    return tuple((tuple(tuple(x % p for x in r) for r in T), tuple(x % p for x in v))
                 for T, v, p in zip(Ts, vs, PR))


eye = [[[int(i == j) for j in range(d)] for i in range(d)] for d in DIM]
zero = [[0] * d for d in DIM]
ONE = affine(eye, zero)
a1 = affine(cert["a1"], zero); a2 = affine(cert["a2"], zero)
P = affine(cert["P"], zero); g0 = affine(eye, cert["g0"])
c0 = mul(P, g0); c0i = inv(c0)
assert mul(c0, c0i) == ONE and mul(c0i, c0) == ONE
transl = []
for j, d in enumerate(DIM):
    for b in range(d):
        vs = [list(z) for z in zero]; vs[j][b] = 1
        transl.append(affine(eye, vs))
gens = [a1, a2] + transl
gens += [inv(s) for s in gens]


def lin(f):
    return tuple(T for T, v in f)


# 1. linear parts of G0 and normalisation by c0
L = {lin(ONE)}; front = [lin(ONE)]
while front:
    new = []
    for x in front:
        for s in (a1, a2):
            y = tuple(matmul(A, B, p) for A, B, p in zip(x, lin(s), PR))
            if y not in L:
                L.add(y); new.append(y)
    front = new
for s in gens:
    if lin(mul(mul(c0, s), c0i)) not in L:
        reject("c0 does not normalise G0")
print("1. linear parts of G0: %d; c0 normalises G0" % len(L))


def conj(y, x):
    return mul(mul(y, x), inv(y))


C = {c0}; front = [c0]
while front:
    new = []
    for x in front:
        for s in gens:
            z = conj(s, x)
            if z not in C:
                C.add(z); new.append(z)
    front = new
    if len(C) > 10 ** 5:
        reject("class too large")
Cl = sorted(C)
print("   |C| = %d (the G0-class of c0)" % len(Cl))

# 3 first (so that a corruption is reported for this reason): powers of c0
pw = [ONE]
while True:
    nxt = mul(pw[-1], c0)
    if nxt == ONE:
        break
    pw.append(nxt)
    if len(pw) > 10 ** 4:
        reject("c0 has order above 10^4")
order = len(pw)
pwi = [inv(x) for x in pw]
print("3. ord(c0) = %d" % order)


def commutes(f, g):
    return mul(f, g) == mul(g, f)


central = [all(commutes(pw[k], x) for x in Cl) for k in range(order)]
ck = [k for k in range(order) if central[k]]
print("   k in [0, ord) with c0^k central in <C>:", ck)
worst = 0
for z in Cl:
    k = next(k for k in range(1, order + 1) if commutes(pw[k % order], z))
    # k = order always commutes, so k exists; it violates the conclusion
    # exactly when c0^k is not central
    if central[k % order]:
        reject("Filipi's condition holds for c = c0 with z = %r (k = %d)" % (z, k))
    worst = max(worst, k)
print("   every z in C: c0^k commutes with z, c0^k not central, for some k <= %d" % worst)

# 2. transitivity of <C> on C
used = 0; orbit = {c0}
while len(orbit) < len(Cl):
    used += 4
    if used > 64:
        reject("<C> not shown transitive on C")
    Y = Cl[::len(Cl) // used][:used]
    orbit = {c0}; front = [c0]
    while front:
        new = []
        for x in front:
            for y in Y:
                z = conj(y, x)
                if z not in orbit:
                    orbit.add(z); new.append(z)
        front = new
    if not orbit <= C:
        reject("C not closed under conjugation by its elements")
print("2. orbit of c0 under conjugation by %d evenly spaced elements of sorted C: %d of %d"
      % (used, len(orbit), len(Cl)))
print("ACCEPT: C is a finite conjugacy class of G = <C> and Filipi's Conjecture 4.1 fails for c0")
print("CPU %.1f s, peak %d MB" % (time.process_time() - t0,
      resource.getrusage(resource.RUSAGE_SELF).ru_maxrss // 1024))
