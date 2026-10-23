#!/usr/bin/env python3
"""Independently check the Lemma F certificates using exact integer arithmetic.
See the finite bracket problem and weak-duality lemma in the paper.

For every case (n, B, t) of the finite bracket problem (all 127,488 of them) the checker
  1. builds, for each coset u = 0..7, the full list of brackets allowed by
     conditions 1-4 with their exact costs (integers, in units 1/SC);
  2. looks up a weight vector w >= 0 (keyed by the case's sorted coset data,
     only to find it), and computes exactly
         L(w) = sum_u min_j (c_{u,j} + w(alpha_j) + [beta_j != alpha_j] w(beta_j))
                - sum_v w_v ;
  3. accepts the case iff L(w) > budget (128 n, times P/Q for a control), or
     the certificate says EMPTY and some coset's list is indeed empty.
By weak duality (the weak-duality lemma in the paper), L(w) is a lower bound on the total cost of
every admissible assignment, so an accepted case has none within budget.
Identical sub-computations are cached (pure functions of their arguments).

usage: check_cert.py CERTFILE [P Q]
exit 0 and "ALL 127488 CASES CERTIFIED" only if every case is accepted.
"""
import sys
from functools import lru_cache

def bit(x): return bin(x).count("1") % 2

def read(path):
    sc, cert = None, {}
    for line in open(path):
        if line.startswith("#"):
            sc = int(line.split("units 1/")[1].split()[0]); continue
        left, right = line.split(";")
        f = list(map(int, left.split()[1:]))
        key = (f[0], f[1], tuple((f[i], f[i + 1]) for i in range(2, 16, 2)))
        right = right.strip()
        if key in cert: raise SystemExit("duplicate certificate for %r" % (key,))
        if right == "EMPTY": cert[key] = "EMPTY"
        else:
            w = {}
            for item in right.split():
                v, x = map(int, item.split(":"))
                if x < 0: raise SystemExit("negative weight")
                if v in w: raise SystemExit("repeated value")
                w[v] = x
            cert[key] = w
    if sc is None: raise SystemExit("missing header")
    return sc, cert

@lru_cache(maxsize=None)
def brackets(n, num, den, r, zero, sc):
    """Brackets of one coset: mean num/den, residue r mod 4, coset 0 iff zero.
    Returns tuple of (cost in units 1/sc, alpha, beta)."""
    out = []
    for a in range(-n, n + 1):
        if (a - r) % 4: continue
        if a * den > num: continue
        for b in range(a, n + 1):
            if (b - r) % 4 or b * den < num: continue
            if a == b and a * den != num: continue          # condition 2
            if not zero and (a == n or b == n): continue    # condition 4
            # cost = N (mu^2 + (mu - a)(b - mu)) (+ n^2 for coset 0), mu = num/den,
            # N = 15 for coset 0, 16 otherwise; times sc, kept exact:
            N = 15 if zero else 16
            top = N * (num * num + (num - a * den) * (b * den - num))   # = cost' * den^2
            extra = n * n if zero else 0
            assert (top * sc) % (den * den) == 0
            out.append((top * sc // (den * den) + extra * sc, a, b))
    return tuple(out)

@lru_cache(maxsize=None)
def coset_min(n, num, den, r, zero, sc, wkey):
    w = dict(wkey)
    L = brackets(n, num, den, r, zero, sc)
    if not L: return None
    return min(c + w.get(a, 0) + (w.get(b, 0) if b != a else 0) for c, a, b in L)

def main():
    path = sys.argv[1]
    P, Q = (int(sys.argv[2]), int(sys.argv[3])) if len(sys.argv) > 3 else (1, 1)
    sc, cert = read(path)
    used, ok, bad = set(), 0, []
    for n in range(128):
        for B in range(128):
            m = bin(B).count("1")
            if m > n: continue
            for t in range(8):
                cos = []
                for u in range(8):
                    if u == 0:
                        cos.append((16 * m - n, 15, n % 4, True))
                    else:
                        mu = sum(1 - 2 * bit(u & h) for h in range(1, 8) if (B >> (h - 1)) & 1)
                        cos.append((mu, 1, (n - 2 * bit(u & t)) % 4, False))
                key = (n, m, tuple(sorted((c[0], c[2]) for c in cos[1:])))
                if key not in cert: bad.append(("missing", n, B, t)); continue
                used.add(key)
                w = cert[key]
                if w == "EMPTY":
                    if any(not brackets(n, *c, sc) for c in cos): ok += 1
                    else: bad.append(("not empty", n, B, t))
                    continue
                wkey = tuple(sorted(w.items()))
                mins = [coset_min(n, *c, sc, wkey) for c in cos]
                if any(x is None for x in mins): ok += 1; continue   # an empty list: no assignment at all
                bound = sum(mins) - sum(w.values())
                # accept iff bound > budget = 128 n P/Q, in units 1/sc
                if bound * Q > 128 * n * P * sc: ok += 1
                else: bad.append(("bound", n, B, t))
    print("cases accepted: %d, rejected: %d, certificates used: %d of %d" % (ok, len(bad), len(used), len(cert)))
    if bad:
        print("first rejections:", bad[:5]); sys.exit(1)
    assert ok == 127488
    print("ALL 127488 CASES CERTIFIED" + ("" if (P, Q) == (1, 1) else " (budget x %d/%d)" % (P, Q)))

if __name__ == "__main__":
    main()
