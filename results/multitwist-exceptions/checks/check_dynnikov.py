#!/usr/bin/env python3
"""Checker B -- independent exact checker for the finite facts F0-F4 of the paper.

Model: integral laminations (multicurves) on the 4-punctured disc D_4, encoded by
their *Dynnikov coordinates* (a_1, a_2; b_1, b_2) in Z^4 \\ {0}, with the braid
group B_4 acting by Dynnikov's piecewise-linear update rules.  The boundary
circle of D_4 is the fifth puncture p5 of the 5-punctured sphere S, so curves on
S are curves on D_4 and B_4 / Z(B_4) is the stabiliser of p5 in Mod(S); every
mapping class the claim uses (twists about a, d, c, C', C and their products)
lies in it.  Nothing here uses the free group, words in pi_1 or the Artin
automorphisms.

Pure Python 3 standard library, integers only (no floating point anywhere).

References for the formulas (all re-validated below, see VALIDATION):
  [D]   I. Dynnikov, On a Yang-Baxter mapping and the Dehornoy ordering,
        Uspekhi Mat. Nauk 57 (2002).
  [HY]  T. Hall, S. O. Yurttas, On the topological entropy of families of
        braids, Topology Appl. 156 (2009), arXiv:0808.3053:
        Lemma 1 (inversion), Lemma 4 / Lemma 5 (update rules for sigma_i^{+-1}).
  [YH]  S. O. Yurttas, T. Hall, Intersections of multicurves from Dynnikov
        coordinates, Bull. Aust. Math. Soc. 98 (2018), arXiv:1711.00895:
        extended coordinates, Theorem 5 (uniform update rule for sigma_i),
        Lemma 9 (intersection number with an elementary = round curve).
  [FM]  Farb-Margalit, A primer on mapping class groups: Prop 3.2
        (i(T_u^k(v), v) = |k| i(u,v)^2, so i(u,v) = 0 iff T_u(v) = v),
        Fact 3.9 (T_u T_v = T_v T_u iff i(u,v) = 0).

Conventions.  Punctures 1..4 on the horizontal diameter.  Arcs (as in [HY] Fig 1):
alpha_{2j-3} (resp. alpha_{2j-2}) joins puncture j (j = 2, 3) vertically to the
top (resp. bottom) of the boundary; beta_i (i = 1, 2, 3) is a vertical arc from
boundary to boundary passing between punctures i and i+1.  For a multicurve L in
minimal position, writing alpha_i, beta_i for its intersection numbers,
    a_i = (alpha_{2i} - alpha_{2i-1}) / 2,   b_i = (beta_i - beta_{i+1}) / 2,
i = 1, 2.  This is a bijection {multicurves} <-> Z^4 \\ {0}  ([D], [HY] Rem 2),
so two curves are isotopic iff their coordinate vectors are equal.

A mapping class is stored as a *word*: a list of (i, e), i in {1,2,3}, e = +-1,
meaning "apply sigma_i^e", applied left to right (first entry acts first).  The
claim composes right to left (f g = g first); the helpers below translate.
sigma_i is the half twist exchanging punctures i, i+1 (counter-clockwise in
[HY]'s convention); the global handedness is irrelevant to the claim.
"""

import argparse
import json
import sys
import time

N = 4  # punctures of the disc; the boundary is the 5th puncture of S


def pos(x):
    return x if x > 0 else 0


# ---------------------------------------------------------------------------
# Update rules ([HY] Lemmas 4 and 5, written out from max-plus notation:
# [x+y] = max(x,y), [xy] = x+y, [x/y] = x-y, [1] = 0).  Coordinates are a tuple
# (a_1, ..., a_{n-2}, b_1, ..., b_{n-2}).
# ---------------------------------------------------------------------------

def _split(L):
    m = N - 2
    return list(L[:m]), list(L[m:])


def sigma(L, i, e):
    """Dynnikov coordinates of sigma_i^e (L)."""
    a, b = _split(L)
    m = N - 2
    if e == 1:
        if i == 1:
            a1, b1 = a[0], b[0]
            a[0] = a1 + b1 - max(a1, 0, b1)
            b[0] = pos(b1) - a1
        elif i == N - 1:
            an, bn = a[m - 1], b[m - 1]
            a[m - 1] = max(an + pos(bn), bn)
            b[m - 1] = bn - an - pos(bn)
        else:
            p, q = i - 2, i - 1          # 0-based indices of a_{i-1}, a_i
            ap, bp, aq, bq = a[p], b[p], a[q], b[q]
            big = max(ap + pos(bp) + pos(bq), aq + bp)
            a[p] = max(ap + pos(bp), aq + bp)
            b[p] = aq + bp + bq - big
            a[q] = ap + aq + bq - max(ap + pos(bq), aq)
            b[q] = big - aq
    elif e == -1:
        if i == 1:
            a1, b1 = a[0], b[0]
            a[0] = max(0, a1 + pos(b1)) - b1
            b[0] = a1 + pos(b1)
        elif i == N - 1:
            an, bn = a[m - 1], b[m - 1]
            a[m - 1] = an - max(an + bn, 0, bn)
            b[m - 1] = an + bn - pos(bn)
        else:
            p, q = i - 2, i - 1
            ap, bp, aq, bq = a[p], b[p], a[q], b[q]
            big = max(ap + bp, aq + pos(bp) + pos(bq))
            a[p] = ap + aq - max(ap + bp, aq + pos(bp))
            b[p] = ap + bp + bq - big
            a[q] = max(ap, aq + pos(bq)) - bq
            b[q] = big - ap
    else:
        raise ValueError(e)
    return tuple(a + b)


def act(word, L):
    for (i, e) in word:
        L = sigma(L, i, e)
    return L


def inv(word):
    return [(i, -e) for (i, e) in reversed(word)]


def power(word, k):
    if k >= 0:
        return list(word) * k
    return inv(word) * (-k)


def compose(*maps):
    """compose(f, g, h) = f g h in the claim's right-to-left convention
    (h acts first), returned as a left-to-right application word."""
    out = []
    for w in reversed(maps):
        out += w
    return out


# ---------------------------------------------------------------------------
# Extended coordinates and arc intersection numbers.
# [HY] Lemma 1 / [YH] (2)-(4): beta_0 = beta_n = 0, b_0 = -max_k(|a_k| + b_k^+ +
# sum_{j<k} b_j), b_{n-1} = -(b_0 + ... + b_{n-2}), a_0 = a_{n-1} = 0,
# beta_i = -2 sum_{k<i} b_k, alpha_{2i} + alpha_{2i-1} = max(beta_i, beta_{i+1}).
# ---------------------------------------------------------------------------

def extended(L):
    a, b = _split(L)
    m = N - 2
    best = None
    run = 0
    for k in range(m):
        v = abs(a[k]) + pos(b[k]) + run
        best = v if best is None else max(best, v)
        run += b[k]
    b0 = -best
    A = [0] + a + [0]                    # A[i] = a_i, 0 <= i <= n-1
    B = [b0] + b + [-(b0 + sum(b))]      # B[i] = b_i
    beta = [0] * (N + 1)                 # beta[i], 0 <= i <= n
    for i in range(1, N + 1):
        beta[i] = beta[i - 1] - 2 * B[i - 1]
    alpha = {}                           # alpha[i], -1 <= i <= 2n-2
    for j in range(0, N):
        s = max(beta[j], beta[j + 1])
        assert (s + 2 * A[j]) % 2 == 0
        alpha[2 * j] = (s + 2 * A[j]) // 2
        alpha[2 * j - 1] = (s - 2 * A[j]) // 2
    return A, B, alpha, beta


def round_curve_coords(i, j):
    """Dynnikov coordinates of round{i..j} (1 <= i < j <= n, (i,j) != (1,n)):
    b_{i-1} = -1, b_{j-1} = +1 in extended indexing, everything else 0.
    Derivation by direct count (see README): round{i..j} meets beta_k twice
    for i <= k < j and not otherwise, and meets each of the two alpha arcs at
    every enclosed puncture p (2 <= p <= n-1) once, so all a_k = 0 and
    b_k = (beta_k - beta_{k+1})/2 is -1 at k = i-1, +1 at k = j-1, else 0."""
    b = [0] * N
    b[i - 1] -= 1
    b[j - 1] += 1
    return tuple([0] * (N - 2) + b[1:N - 1])


def round_curve_arcs(i, j):
    """Intersection numbers of round{i..j} with the arcs, counted by hand from
    the picture (used to validate round_curve_coords against [HY] Lemma 1):
    it crosses beta_k twice for i <= k < j, and the vertical arcs above and
    below each enclosed puncture once (extended arcs alpha_{-1}, alpha_0,
    alpha_{2n-3}, alpha_{2n-2} at punctures 1 and n included)."""
    beta = [0] * (N + 1)
    for k in range(i, j):
        beta[k] = 2
    alpha = {}
    for p in range(1, N + 1):
        x = 1 if i <= p <= j else 0
        alpha[2 * p - 3] = x
        alpha[2 * p - 2] = x
    return alpha, beta


def i_round(i, j, L):
    """Geometric intersection number of the multicurve L with round{i..j},
    [YH] Lemma 9:  beta_{i-1} + beta_j - 2(R + L + A_{i,j} + B_{i,j})."""
    A_, B_, alpha, beta = extended(L)

    def Ak(k):
        return alpha[2 * k - 3] - abs(B_[k - 1])

    def Bk(k):
        return alpha[2 * k - 2] - abs(B_[k - 1])

    def Amin(l, m):
        return min(Ak(k) for k in range(l, m + 1))

    def Bmin(l, m):
        return min(Bk(k) for k in range(l, m + 1))

    Aij, Bij = Amin(i, j), Bmin(i, j)
    R = min(Amin(i, j - 1) - Aij, Bmin(i, j - 1) - Bij, pos(B_[j - 1]))
    Lc = min(Amin(i + 1, j) - Aij, Bmin(i + 1, j) - Bij, pos(-B_[i - 1]))
    return beta[i - 1] + beta[j] - 2 * (R + Lc + Aij + Bij)


# ---------------------------------------------------------------------------
# The five round curves and their twists.
# A Dehn twist about round{i..j} is the full twist Delta^2 of strands i..j
# (sigma_i^2 for two strands, (sigma_i sigma_{i+1})^3 for three); both are
# positive braids, so all five twists have the same handedness.
# ---------------------------------------------------------------------------

ROUND = {"a": (1, 2), "d": (2, 3), "c": (3, 4), "C'": (1, 3), "C": (2, 4)}
TWIST = {
    "a": [(1, 1)] * 2,
    "d": [(2, 1)] * 2,
    "c": [(3, 1)] * 2,
    "C'": [(1, 1), (2, 1)] * 3,
    "C": [(2, 1), (3, 1)] * 3,
}
EXPECTED_COORDS = {   # hand-derived, (a1, a2; b1, b2); see README
    "a": (0, 0, 1, 0),
    "d": (0, 0, -1, 1),
    "c": (0, 0, 0, -1),
    "C'": (0, 0, 0, 1),
    "C": (0, 0, -1, 0),
}
PENTAGON = ["a", "d", "c", "C'", "C"]


class Curve:
    """The curve g(R) for a round curve R and a mapping class g (a word)."""

    def __init__(self, base, g=()):
        self.base = base
        self.g = list(g)
        self.coords = act(self.g, round_curve_coords(*ROUND[base]))

    def twist(self):
        # T_{g(R)} = g T_R g^{-1}
        return compose(self.g, TWIST[self.base], inv(self.g))

    def i_with(self, L):
        # i(g(R), L) = i(R, g^{-1}(L))
        return i_round(*ROUND[self.base], act(inv(self.g), L))


def curves_for(corrupt):
    cs = {x: Curve(x) for x in PENTAGON}
    if corrupt == "K1":      # C replaced by T_a(C)
        cs["C"] = Curve("C", TWIST["a"])
    elif corrupt == "K2":    # C' replaced by T_c(C')
        cs["C'"] = Curve("C'", TWIST["c"])
    elif corrupt == "K3":    # C and C' exchanged
        cs["C"], cs["C'"] = Curve("C'"), Curve("C")
    elif corrupt == "K4":    # c replaced by T_{C'}^{-1}(c)
        cs["c"] = Curve("c", inv(TWIST["C'"]))
    return cs


# ---------------------------------------------------------------------------
# Bookkeeping
# ---------------------------------------------------------------------------

class Tally:
    def __init__(self, verbose):
        self.checks = 0
        self.failures = 0
        self.fail_by_group = {}
        self.count_by_group = {}
        self.verbose = verbose

    def check(self, group, ok, msg):
        self.checks += 1
        self.count_by_group[group] = self.count_by_group.get(group, 0) + 1
        if not ok:
            self.failures += 1
            self.fail_by_group[group] = self.fail_by_group.get(group, 0) + 1
            if self.verbose or self.fail_by_group[group] <= 3:
                print("FAIL [%s] %s" % (group, msg))


class Rng:
    """xorshift64*, integers only, deterministic."""

    def __init__(self, seed):
        self.s = seed & ((1 << 64) - 1) or 1

    def next(self):
        s = self.s
        s ^= (s >> 12)
        s ^= (s << 25) & ((1 << 64) - 1)
        s ^= (s >> 27)
        self.s = s
        return (s * 0x2545F4914F6CDD1D) & ((1 << 64) - 1)

    def below(self, n):
        return (self.next() >> 11) % n


def random_word(rng, length):
    return [(1 + rng.below(N - 1), 1 if rng.below(2) else -1)
            for _ in range(length)]


def test_laminations(rng):
    """All nonzero integer vectors in [-2,2]^4 (each is a multicurve), random
    larger vectors, and random braid images of the five round curves."""
    out = []
    rngs = range(-2, 3)
    for a1 in rngs:
        for a2 in rngs:
            for b1 in rngs:
                for b2 in rngs:
                    if (a1, a2, b1, b2) != (0, 0, 0, 0):
                        out.append((a1, a2, b1, b2))
    for _ in range(300):
        v = tuple(rng.below(201) - 100 for _ in range(4))
        if v != (0, 0, 0, 0):
            out.append(v)
    for _ in range(300):
        base = PENTAGON[rng.below(5)]
        out.append(act(random_word(rng, 1 + rng.below(12)),
                       round_curve_coords(*ROUND[base])))
    return out


# ---------------------------------------------------------------------------
# VALIDATION of the model on known facts (independent of the claim)
# ---------------------------------------------------------------------------

def sigma_uniform(L, i):
    """[YH] Theorem 5: uniform rule for sigma_i in *extended* coordinates;
    a second published form of the positive update rule, used only to
    cross-check sigma() (in particular the end generators sigma_1, sigma_3)."""
    A, B, _, _ = extended(L)
    a, b = A[:], B[:]
    ap, bp, aq, bq = A[i - 1], B[i - 1], A[i], B[i]
    big = max(ap + pos(bp) + pos(bq), aq + bp)
    a[i - 1] = max(ap + pos(bp), aq + bp)
    a[i] = bq - max(-ap, pos(bq) - aq)
    b[i - 1] = aq + bp + bq - big
    b[i] = big - aq
    return tuple(a[1:N - 1] + b[1:N - 1])


def validate(T, rng):
    Ls = test_laminations(rng)
    G = "V"
    s = {i: [(i, 1)] for i in range(1, N)}
    si = {i: [(i, -1)] for i in range(1, N)}
    full_twist = [(1, 1), (2, 1), (3, 1)] * 4
    for L in Ls:
        for i in range(1, N):
            T.check(G, act(s[i] + si[i], L) == L, "s%d s%d^-1 on %s" % (i, i, L))
            T.check(G, act(si[i] + s[i], L) == L, "s%d^-1 s%d on %s" % (i, i, L))
            T.check(G, sigma(L, i, 1) == sigma_uniform(L, i),
                    "Lemma 4 vs uniform Thm 5 for s%d on %s" % (i, L))
        T.check(G, act([(1, 1), (2, 1), (1, 1)], L) == act([(2, 1), (1, 1), (2, 1)], L),
                "s1s2s1 = s2s1s2 on %s" % (L,))
        T.check(G, act([(2, 1), (3, 1), (2, 1)], L) == act([(3, 1), (2, 1), (3, 1)], L),
                "s2s3s2 = s3s2s3 on %s" % (L,))
        T.check(G, act([(1, 1), (3, 1)], L) == act([(3, 1), (1, 1)], L),
                "s1s3 = s3s1 on %s" % (L,))
        T.check(G, act([(1, -1), (3, 1)], L) == act([(3, 1), (1, -1)], L),
                "s1^-1 s3 = s3 s1^-1 on %s" % (L,))
        T.check(G, act(full_twist, L) == L, "(s1s2s3)^4 trivial on %s" % (L,))
        # arc numbers are nonnegative integers and satisfy the strip identities
        A, B, alpha, beta = extended(L)
        ok = all(v >= 0 for v in beta) and all(v >= 0 for v in alpha.values())
        for j in range(1, N + 1):
            ok = ok and alpha[2 * j - 3] >= abs(B[j - 1]) and alpha[2 * j - 2] >= abs(B[j - 1])
        T.check(G, ok, "arc numbers of %s nonnegative / loop bounds" % (L,))
    # generators act nontrivially, and squares are not trivial either
    T.check(G, any(sigma(L, i, 1) != L for L in Ls for i in range(1, N)),
            "generators nontrivial")
    for i in range(1, N):
        T.check(G, any(act(s[i] * 2, L) != L for L in Ls), "s%d^2 nontrivial" % i)
        T.check(G, any(act(s[i] * 4, L) != act(s[i] * 2, L) for L in Ls),
                "s%d^2 has infinite order on the test set" % i)
    # (s1 s2 s3)^4 is the smallest power of s1s2s3 acting trivially
    T.check(G, any(act([(1, 1), (2, 1), (3, 1)] * 2, L) != L for L in Ls),
            "(s1s2s3)^2 nontrivial")
    # round curves: hand-derived coordinates agree with [HY] Lemma 1 inversion,
    # are primitive, pairwise distinct, and each is fixed by its own twist and
    # by the half twists sigma_p (i <= p < j) inside it.
    for x in PENTAGON:
        i, j = ROUND[x]
        L = round_curve_coords(i, j)
        T.check(G, L == EXPECTED_COORDS[x], "coords of round{%d..%d}" % (i, j))
        _, _, alpha, beta = extended(L)
        ha, hb = round_curve_arcs(i, j)
        T.check(G, beta == hb and all(alpha[k] == ha[k] for k in ha),
                "Lemma 1 arc numbers of round{%d..%d}" % (i, j))
        T.check(G, act(TWIST[x], L) == L, "twist fixes round{%d..%d}" % (i, j))
        for p in range(i, j):
            T.check(G, sigma(L, p, 1) == L and sigma(L, p, -1) == L,
                    "sigma_%d fixes round{%d..%d}" % (p, i, j))
        T.check(G, i_round(i, j, L) == 0, "i(R,R)=0 for round{%d..%d}" % (i, j))
    # the twist about round{i,i+1} is sigma_i^2 and the twist about a
    # 3-puncture round curve is (s_i s_{i+1})^3: check the defining property of
    # a single Dehn twist, [FM] Prop 3.2  i(T_R^k(v), v) = |k| i(R, v)^2,
    # with v = g(R') ranging over random braid images of round curves and
    # i(T_R^k v, v) = i(R', g^-1 T_R^k g R') computed by [YH] Lemma 9.
    # This simultaneously validates the update rules and Lemma 9.
    nprop = 0
    for _ in range(400):
        R = PENTAGON[rng.below(5)]
        Rp = PENTAGON[rng.below(5)]
        g = random_word(rng, rng.below(10))
        k = [1, 2, 3, -1, -2][rng.below(5)]
        v = act(g, round_curve_coords(*ROUND[Rp]))
        iRv = i_round(*ROUND[R], v)
        moved = act(inv(g), act(power(TWIST[R], k), v))
        lhs = i_round(*ROUND[Rp], moved)
        T.check(G, lhs == abs(k) * iRv * iRv,
                "FM 3.2: i(T_%s^%d v, v)=%d vs %d*%d^2 (g=%s, R'=%s)"
                % (R, k, lhs, abs(k), iRv, g, Rp))
        # i(u,v) = 0 iff T_u(v) = v
        T.check(G, (iRv == 0) == (act(TWIST[R], v) == v),
                "Lemma 9 zero vs twist test for %s, g=%s" % (R, g))
        # symmetry: i(R, g R') = i(R', g^-1 R)
        other = i_round(*ROUND[Rp], act(inv(g), round_curve_coords(*ROUND[R])))
        T.check(G, iRv == other, "symmetry of i for %s,%s,g=%s" % (R, Rp, g))
        nprop += iRv > 0
    T.check(G, nprop > 100, "FM 3.2 test exercised nonzero cases (%d)" % nprop)
    # [FM] Fact 3.9 sanity: s1^2 and s2^2 do not commute; s1^2 and s3^2 do
    T.check(G, any(act(TWIST["a"] + TWIST["d"], L) != act(TWIST["d"] + TWIST["a"], L)
                   for L in Ls), "T_a, T_d do not commute")
    return Ls


# ---------------------------------------------------------------------------
# The facts F0 - F4
# ---------------------------------------------------------------------------

def check_facts(T, cs, kmax, Ls, report):
    # F0: each twist fixes its own curve
    for x in PENTAGON:
        T.check("F0", act(cs[x].twist(), cs[x].coords) == cs[x].coords,
                "T_%s does not fix %s" % (x, x))
    # F1: pentagon, by two independent tests
    inter = {}
    for p in range(5):
        for q in range(p + 1, 5):
            u, v = PENTAGON[p], PENTAGON[q]
            consecutive = (q - p) in (1, 4)
            val = cs[u].i_with(cs[v].coords)
            val2 = cs[v].i_with(cs[u].coords)
            tw = act(cs[u].twist(), cs[v].coords) != cs[v].coords
            tw2 = act(cs[v].twist(), cs[u].coords) != cs[u].coords
            inter["i(%s,%s)" % (u, v)] = val
            T.check("F1", (val != 0) == consecutive,
                    "Lemma 9: i(%s,%s)=%d, consecutive=%s" % (u, v, val, consecutive))
            T.check("F1", tw == consecutive and tw2 == consecutive,
                    "twist test: T_%s(%s)!=%s is %s, consecutive=%s" % (u, v, v, tw, consecutive))
            T.check("F1", val == val2, "i(%s,%s) asymmetric %d/%d" % (u, v, val, val2))
            T.check("F1", cs[u].coords != cs[v].coords, "%s isotopic to %s" % (u, v))
    for x in PENTAGON:
        L = cs[x].coords
        # nonzero Dynnikov vector = essential multicurve on D_4 (no component
        # bounds a disc with <= 1 puncture or is parallel to the boundary, i.e.
        # essential on S); it is a homeomorphic image of a round curve, so
        # connected; primitivity double-checks it is not a multiple.
        g = 0
        for t in L:
            g = abs(t) if g == 0 else _gcd(g, abs(t))
        T.check("F1", L != (0, 0, 0, 0) and g == 1, "%s not an essential curve: %s" % (x, L))
    report["intersections"] = inter
    # F2: T_a T_c = T_c T_a
    Ta, Tc, Td = cs["a"].twist(), cs["c"].twist(), cs["d"].twist()
    TaTc, TcTa = compose(Ta, Tc), compose(Tc, Ta)
    T.check("F2", all(act(TaTc, L) == act(TcTa, L) for L in Ls),
            "T_a T_c != T_c T_a on the test set")
    T.check("F2", cs["a"].i_with(cs["c"].coords) == 0, "i(a,c) != 0 (FM Fact 3.9)")
    # F3 and F4 for k = 1..kmax, eps = +-1
    f4vals = set()
    for k in range(1, kmax + 1):
        fk = compose(power(Ta, k), Td)                       # T_a^k T_d
        fa = act(fk, cs["a"].coords)
        for eps in (1, -1):
            t = compose(Ta, power(Tc, eps))                  # t = T_a T_c^eps
            # F3, simplified forms as stated
            T.check("F3", act(fk, cs["C'"].coords) == cs["C'"].coords,
                    "k=%d eps=%d: T_a^k T_d does not fix C'" % (k, eps))
            g2 = compose(power(Tc, -eps * k), Td)            # T_c^{-eps k} T_d
            T.check("F3", act(g2, cs["C"].coords) == cs["C"].coords,
                    "k=%d eps=%d: T_c^(-eps k) T_d does not fix C" % (k, eps))
            # F3, literal forms t^0 f_k and t^{-k} f_k (no use of F2)
            T.check("F3", act(compose(power(t, 0), fk), cs["C'"].coords) == cs["C'"].coords,
                    "k=%d eps=%d: t^0 f_k does not fix C'" % (k, eps))
            lit = compose(power(t, -k), fk)
            T.check("F3", act(lit, cs["C"].coords) == cs["C"].coords,
                    "k=%d eps=%d: t^-k f_k does not fix C" % (k, eps))
        # F4 (independent of eps): i(a, f_k a) != 0, i(c, f_k a) != 0
        for x in ("a", "c"):
            val = cs[x].i_with(fa)
            moved = act(cs[x].twist(), fa) != fa
            f4vals.add((x, val))
            T.check("F4", val != 0, "k=%d: i(%s, f_k(a)) = 0 (Lemma 9)" % (k, x))
            T.check("F4", moved, "k=%d: T_%s fixes f_k(a) (twist test)" % (k, x))
            T.check("F4x", val == 4, "k=%d: i(%s, f_k(a)) = %d, claim says 4" % (k, x, val))
    report["F4_values"] = sorted("i(%s,f_k(a))=%d" % p for p in f4vals)


def _gcd(x, y):
    while y:
        x, y = y, x % y
    return x


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--kmax", type=int, default=30)
    ap.add_argument("--corrupt", choices=["K1", "K2", "K3", "K4"], default=None)
    ap.add_argument("--mirror", action="store_true",
                    help="reverse every twist (all twists of the other handedness)")
    ap.add_argument("--verbose", action="store_true")
    args = ap.parse_args()
    t0 = time.perf_counter_ns()
    if args.mirror:
        for x in TWIST:
            TWIST[x] = inv(TWIST[x])
    T = Tally(args.verbose)
    rng = Rng(0x1A2B3C4D5E6F)
    Ls = validate(T, rng)
    nval = T.checks
    cs = curves_for(args.corrupt)
    report = {}
    check_facts(T, cs, args.kmax, Ls, report)
    ms = (time.perf_counter_ns() - t0) // 1000000
    print("model: Dynnikov coordinates on D_4 (boundary = p5); validation checks %d"
          % nval)
    print("curves: " + ", ".join("%s=%s" % (x, cs[x].coords) for x in PENTAGON)
          + ("  [corruption %s]" % args.corrupt if args.corrupt else ""))
    print("intersections: " + ", ".join("%s=%d" % kv for kv in report["intersections"].items()))
    print("F4 values: " + ", ".join(report.get("F4_values", [])))
    for g in sorted(T.count_by_group):
        print("group %-3s checks %6d failures %d"
              % (g, T.count_by_group[g], T.fail_by_group.get(g, 0)))
    print("time: %d ms" % ms)
    verdict = "ACCEPT" if T.failures == 0 else "REJECT"
    if args.mirror:
        print("mirror: every twist reversed")
    print(json.dumps({"checker": "B-dynnikov", "kmax": args.kmax, "checks": T.checks,
                      "failures": T.failures, "verdict": verdict}))
    return 0 if verdict == "ACCEPT" else 1


if __name__ == "__main__":
    sys.exit(main())
