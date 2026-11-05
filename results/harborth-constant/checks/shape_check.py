"""Independent check of the shape step for p = 11 and p = 13.

A profile is a list v of p class sizes with 0 <= v_g <= p - 1 and sum 2p - 1; it is
concentrated if sum C(v_g, 2) >= 2p - 4. For each concentrated profile, sorted in
decreasing order, the program confirms that it is one of the three exceptional shapes
(p-1, p-1, 1), (p-1, p-2, 2), (p-1, p-3, 3), or that it has a layer witness r:
r_g <= v_g, r_g = v_g mod 2, sum r_g^2 <= sum (v_g - 2)^2 and
sum_{i>=1} floor(x_i^2 / 4) >= p - 1, where x_i = #{g : r_g >= i}.
It tries rule B, the rules H(rho) and the three depth lists of the paper's Table 1, and
then searches all r.
Both conditions depend only on the multiset of sizes, so sorted profiles suffice.

Usage: python3 shape_check.py [p ...]   (default: 11 13). Exit status 0 means every
concentrated shape of every p given is covered.
"""
import sys
from itertools import product
from math import comb


def shapes(p):
    """Concentrated profiles of length p, in decreasing order."""
    def rec(n, hi, s):
        if n == 0:
            if s == 0:
                yield ()
            return
        for x in range(min(hi, s), -1, -1):
            if x * n < s:
                break
            for rest in rec(n - 1, x, s - x):
                yield (x,) + rest
    for v in rec(p, p - 1, 2 * p - 1):
        if sum(comb(x, 2) for x in v) >= 2 * p - 4:
            yield v


def exceptional(p, v):
    return v[0] == p - 1 and v[1] + v[2] == p and 1 <= v[2] <= 3 and not any(v[3:])


def is_witness(p, v, r):
    if any(a > b or (a - b) % 2 for a, b in zip(r, v)):
        return False
    if sum(a * a for a in r) > sum((b - 2) ** 2 for b in v):
        return False
    layers = (sum(1 for a in r if a >= i) for i in range(1, max(r) + 1))
    return sum(x * x // 4 for x in layers) >= p - 1


def rule_b(v):
    def base(x):
        return 0 if x == 0 else 1 if x % 2 else 2
    k = min(v.count(2), sum((x - 2) ** 2 - base(x) ** 2 for x in v if x != 2) // 4)
    r = []
    for x in v:
        if x == 2:
            r.append(2 if k > 0 else 0)
            k -= 1
        else:
            r.append(base(x))
    return r


def rule_h(rho, v):
    return [x if x <= rho + 1 else rho + (x - rho) % 2 for x in v]


# Table 1 of the paper: the shapes at p = 11 that rules B and H miss, with their r.
LISTED = {
    (6, 3, 3, 3, 3, 3): (2, 3, 1, 1, 1, 1),
    (5, 5, 3, 3, 3, 2): (3, 3, 3, 1, 1, 0),
    (5, 4, 3, 3, 3, 3): (3, 2, 1, 1, 1, 1),
}


def listed(p, v):
    nz = sum(1 for x in v if x)
    r = LISTED.get(v[:nz])
    return r is not None and is_witness(p, v, r + (0,) * (p - nz))


def search(p, v):
    for r in product(*(range(x % 2, x + 1, 2) for x in v)):
        if is_witness(p, v, r):
            return r
    return None


def check(p):
    count = {"exceptional": 0, "rule B": 0, "rule H": 0, "Table 1": 0, "other witness": 0}
    others, failures = [], []
    for v in shapes(p):
        if exceptional(p, v):
            count["exceptional"] += 1
        elif is_witness(p, v, rule_b(v)):
            count["rule B"] += 1
        elif any(is_witness(p, v, rule_h(rho, v)) for rho in range(2, p)):
            count["rule H"] += 1
        elif listed(p, v):
            count["Table 1"] += 1
        else:
            r = search(p, v)
            if r is None:
                failures.append(v)
            else:
                count["other witness"] += 1
                others.append((v, r))
    total = sum(count.values()) + len(failures)
    print(f"p = {p}: {total} concentrated shapes; "
          + ", ".join(f"{k} {n}" for k, n in count.items()) + f", uncovered {len(failures)}")
    for v, r in others:
        nz = sum(1 for x in v if x)
        print(f"  shape {v[:nz]} has witness r = {tuple(r[:nz])}")
    for v in failures:
        nz = sum(1 for x in v if x)
        print(f"  UNCOVERED shape {v[:nz]}")
    return not failures


def main():
    ps = [int(a) for a in sys.argv[1:]] or [11, 13]
    ok = all([check(p) for p in ps])
    print("PASS" if ok else "FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
