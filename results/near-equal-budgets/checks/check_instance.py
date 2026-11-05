#!/usr/bin/env python3
"""Check the hypotheses on the market: positive integer additive values, strict preferences.

Verifies that instance.json and the instance inside certificate.json are the same market (values
and direction), that every value is a positive integer (so each valuation is strictly monotone),
that each agent's 2^m bundle values are pairwise distinct (strict preferences), and that the
direction d sums to zero (so the budgets e + delta*d all have the same total).
Usage: check_instance.py instance.json certificate.json   (exit status 0 iff every check passes)
"""
import json, sys


def main(instance_path, certificate_path):
    inst = json.load(open(instance_path))
    cert = json.load(open(certificate_path))["instance"]
    if inst["values"] != cert["values"] or inst["direction"] != cert["direction"]:
        return fail("the certificate's market differs from instance.json")
    V, d = inst["values"], inst["direction"]
    n, m = len(V), len(V[0])
    if len(d) != n or sum(d) != 0:
        return fail("the direction must have one entry per agent and sum to zero")
    for i, row in enumerate(V):
        if len(row) != m or any(not isinstance(x, int) or x <= 0 for x in row):
            return fail(f"agent {i}: values must be {m} positive integers")
        sums = [sum(row[g] for g in range(m) if S >> g & 1) for S in range(1 << m)]
        if len(set(sums)) != 1 << m:
            return fail(f"agent {i}: two bundles have the same value")
    print(f"OK: {n} agents, {m} goods; values positive integers; all {1 << m} bundle values distinct "
          f"for each agent; direction d={d} sums to 0")
    return 0


def fail(msg):
    print("FAIL:", msg)
    return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1], sys.argv[2]))
