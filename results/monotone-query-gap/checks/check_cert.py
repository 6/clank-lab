"""Exact checker for certificate.json, independent of the search program.

Usage: python3 -I check_cert.py certificate.json   (exit 0 iff accepted)

Checks, with exact rationals, at p = 1/2 on n = 5 bits:
 1. the truth table is the stated f1 and is monotone;
 2. lower bound a(f1) >= 13/4: the table L covers all 3^5 restrictions,
    L(r) <= 0 when f1 is constant on r, and for EVERY free bit i of r,
    L(r) <= 1 + L(r, x_i=1)/2 + L(r, x_i=0)/2, and L(*****) >= 13/4.
    By induction over any adaptive query algorithm's decision tree (an
    algorithm that has not determined f1 at r must query some bit; a repeated
    query costs 1 and leaves r unchanged), its expected number of queries
    until f1 is determined, conditional on reaching r, is >= L(r);
 3. upper bound a(f1) <= 13/4: the tree only stops where f1 is determined,
    its leaf labels are correct, and its expected query count is 13/4;
 4. sc(f1) <= 51/16: the cubes partition {0,1}^5, f1 is constant on each, and
    the expected codimension is 51/16;
 5. sc(f1) >= 51/16: the LP dual y satisfies sum_{x in C} y_x <= codim(C)|C|
    for every f1-monochromatic subcube C, and sum_x y_x = 32 * 51/16.
"""
import itertools, json, sys
from fractions import Fraction as F

N = 5
HALF = F(1, 2)


def bits(x):
    return [(x >> i) & 1 for i in range(N)]


def formula(x):
    b = bits(x)
    return int((b[1] & b[2] & b[3]) | (b[0] & b[4] & (b[1] | b[2] | b[3])))


def members(cube):
    if len(cube) != N or any(c not in "01*" for c in cube):
        raise ValueError(f"bad cube {cube!r}")
    return [x for x in range(1 << N)
            if all(c == "*" or int(c) == b for c, b in zip(cube, bits(x)))]


def check(cert):
    errors = []
    tt = [int(c) for c in cert["truth_table"]]
    if len(tt) != 32 or tt != [formula(x) for x in range(32)]:
        errors.append("truth table is not f1")
    for x in range(32):
        for y in range(32):
            if x & y == x and tt[x] > tt[y]:
                errors.append(f"not monotone at {x},{y}")
    const = lambda r: len({tt[x] for x in members(r)}) == 1

    # 2. lower bound table
    L = {r: F(v) for r, v in cert["lower_bound_table"].items()}
    allr = {"".join(t) for t in itertools.product("01*", repeat=N)}
    if set(L) != allr:
        errors.append("lower-bound table does not cover exactly the 243 restrictions")
    else:
        for r in sorted(allr):
            if const(r):
                if L[r] > 0:
                    errors.append(f"L({r}) > 0 on a determined restriction")
                continue
            for i, c in enumerate(r):
                if c == "*":
                    r0, r1 = r[:i] + "0" + r[i + 1:], r[:i] + "1" + r[i + 1:]
                    if L[r] > 1 + HALF * L[r1] + HALF * L[r0]:
                        errors.append(f"DP inequality fails at {r}, bit {i}")
        if L["*****"] < F(13, 4):
            errors.append("root lower bound below 13/4")

    # 3. tree
    def walk(t, x, r, depth):
        if "leaf" in t:
            if not const(r):
                raise ValueError(f"tree stops at undetermined {r}")
            if t["leaf"] != tt[x]:
                raise ValueError("wrong leaf label")
            return depth
        i = t["q"]
        b = bits(x)[i]
        return walk(t[str(b)], x, r[:i] + str(b) + r[i + 1:], depth + 1)
    try:
        cost = F(sum(walk(cert["optimal_tree"], x, "*****", 0) for x in range(32)), 32)
        if cost != F(13, 4):
            errors.append(f"tree cost {cost} != 13/4")
    except (ValueError, KeyError) as e:
        errors.append(f"tree invalid: {e}")

    # 4. partition
    cover = [0] * 32
    codim = [None] * 32
    for cube in cert["partition"]:
        ms = members(cube)
        if len({tt[x] for x in ms}) != 1:
            errors.append(f"f1 not constant on {cube}")
        for x in ms:
            cover[x] += 1
            codim[x] = sum(c != "*" for c in cube)
    if cover != [1] * 32:
        errors.append("cubes are not a partition")
    elif F(sum(codim), 32) != F(51, 16):
        errors.append(f"partition cost {F(sum(codim), 32)} != 51/16")

    # 5. dual
    y = [F(v) for v in cert["sc_dual"]]
    if len(y) != 32:
        errors.append("dual has wrong length")
    else:
        for r in sorted(allr):
            if const(r):
                cd = sum(c != "*" for c in r)
                if sum(y[x] for x in members(r)) > cd * 2 ** (N - cd):
                    errors.append(f"dual infeasible at {r}")
        if sum(y) != 32 * F(51, 16):
            errors.append("dual objective != 51/16")
    return errors


def main():
    cert = json.load(open(sys.argv[1]))
    errors = check(cert)
    if errors:
        print("REJECT")
        for e in errors[:10]:
            print(" ", e)
        sys.exit(1)
    print("ACCEPT: f1 monotone; a(f1,pi_1/2) = 13/4 > 51/16 = sc(f1,pi_1/2)")


if __name__ == "__main__":
    main()
