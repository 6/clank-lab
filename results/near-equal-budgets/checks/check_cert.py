#!/usr/bin/env python3
"""Checker 1: verify Farkas certificates that no competitive equilibrium exists near equal budgets.

Model (Segal-Halevi 2020, Def. 1; Babaioff-Nisan-Talgam-Cohen 2021, Def. 2.1): a CE at budgets t is a
partition X of all goods among the agents and prices p > 0 with p(X_i) <= t_i and p(Y) > t_i for every
bundle Y that agent i strictly prefers to X_i (additive values).  Relaxing to p >= 0 and p(Y) >= t_i gives
a closed linear system; if it is infeasible, so is the CE system.

For each of the n^m allocations the certificate gives alpha_i >= 0 and lambda_{i,Y} >= 0 on bundles Y
strictly preferred by i to X_i.  The checker verifies, in exact rationals:
  (1) for every good g: sum_i alpha_i [g in X_i] - sum lambda_{i,Y} [g in Y] >= 0,
  (2) with w_i = alpha_i - sum_Y lambda_{i,Y}:  w.e < 0, or w.e = 0 and w.d < 0.
Multiplying the closed system by these multipliers gives 0 <= (multiplied prices) <= sum_i w_i t_i, so
sum_i w_i t_i < 0 makes it infeasible.  For t = e + delta*d this holds for 0 < delta < r_X, where
r_X = -w.e / w.d if w.d > 0 (type A), and r_X = infinity otherwise.  Every allocation must be covered.
Output: r = min_X r_X.  Conclusion: for every 0 < delta < r no CE exists at e + delta*d, and (closed
system infeasibility being an open condition in t) none in a neighbourhood of each such budget vector.
Usage: check_cert.py certificate.json   (exit status 0 iff every check passes)
"""
import json, sys, itertools
from fractions import Fraction


def main(path):
    data = json.load(open(path))
    V = data["instance"]["values"]; d = [Fraction(x) for x in data["instance"]["direction"]]
    n, m = len(V), len(V[0])
    if any(len(r) != m for r in V) or any(not isinstance(x, int) or x <= 0 for r in V for x in r):
        return fail("values must be positive integers, one row per agent")
    def value(i, S):
        return sum(V[i][g] for g in range(m) if S >> g & 1)
    certs = {}
    for c in data["certificates"]:
        key = tuple(c["owner"])
        if key in certs:
            return fail(f"duplicate certificate for {key}")
        certs[key] = c
    r = None
    for own in itertools.product(range(n), repeat=m):
        if own not in certs:
            return fail(f"allocation {own} has no certificate")
        c = certs[own]
        X = [sum(1 << g for g in range(m) if own[g] == i) for i in range(n)]
        alpha = [Fraction(a) for a in c["alpha"]]
        if len(alpha) != n or any(a < 0 for a in alpha):
            return fail(f"{own}: bad alpha")
        load = [sum(alpha[i] for i in range(n) if X[i] >> g & 1) for g in range(m)]
        w = alpha[:]
        for i, Y, lam in c["lambda"]:
            lam = Fraction(lam)
            if not (0 <= i < n and 0 < Y < (1 << m)) or lam < 0:
                return fail(f"{own}: bad lambda entry")
            if not value(i, Y) > value(i, X[i]):
                return fail(f"{own}: agent {i} does not strictly prefer bundle {Y:0{m}b} to {X[i]:0{m}b}")
            for g in range(m):
                if Y >> g & 1:
                    load[g] -= lam
            w[i] -= lam
        if any(x < 0 for x in load):
            return fail(f"{own}: componentwise condition fails")
        we, wd = sum(w), sum(wi * di for wi, di in zip(w, d))
        if we < 0:
            rx = -we / wd if wd > 0 else None
        elif we == 0 and wd < 0:
            rx = None
        else:
            return fail(f"{own}: weight condition fails (w.e={we}, w.d={wd})")
        if rx is not None and (r is None or rx < r):
            r = rx
    print(f"OK: {n} agents, {m} goods, {n ** m} allocations certified; direction d={[str(x) for x in d]}; "
          f"radius r={'infinity' if r is None else r}")
    return 0


def fail(msg):
    print("FAIL:", msg)
    return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
