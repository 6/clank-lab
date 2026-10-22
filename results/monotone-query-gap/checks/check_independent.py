#!/usr/bin/env python3
"""Independent exact checker, derived solely from the mathematical claim.

Usage: python3 check_independent.py certificate.json
Subcubes are (fixed_mask, one_bits), not strings, after input decoding.
The adaptive minimum is recomputed without any certificate data.
Only Python's standard library is used; no floating point is accepted.
"""

import json
import re
import sys
from fractions import Fraction
from functools import lru_cache

N = 5
FULL = (1 << N) - 1
POINTS = tuple(range(1 << N))
MIN_TRUE = tuple(sum(1 << i for i in s)
                 for s in ((1, 2, 3), (0, 3, 4), (0, 2, 4), (0, 1, 4)))
A_TARGET = Fraction(13, 4)
SC_TARGET = Fraction(51, 16)


def f1(x):
    return int(any(x & t == t for t in MIN_TRUE))


def submasks(mask):
    value = mask
    while True:
        yield value
        if value == 0:
            return
        value = (value - 1) & mask


CUBES = tuple((mask, value) for mask in POINTS for value in submasks(mask))
MEMBERS = {(mask, value): tuple(value | s for s in submasks(FULL ^ mask))
           for mask, value in CUBES}
COLORS = {cube: frozenset(f1(x) for x in members)
          for cube, members in MEMBERS.items()}


def decode_cube(encoded):
    if not isinstance(encoded, str) or len(encoded) != N:
        raise ValueError("subcube must have exactly five characters")
    if any(c not in "01*" for c in encoded):
        raise ValueError("subcube contains a character outside 0, 1, *")
    mask = sum(1 << i for i, c in enumerate(encoded) if c != "*")
    value = sum(1 << i for i, c in enumerate(encoded) if c == "1")
    return mask, value


def rational(raw):
    if type(raw) is int:
        return Fraction(raw)
    if isinstance(raw, str) and re.fullmatch(r"[+-]?[0-9]+(?:/[0-9]+)?", raw):
        if "/" in raw:
            num, den = raw.split("/")
            return Fraction(int(num), int(den))
        return Fraction(int(raw))
    raise ValueError("expected an integer or exact rational string")


def unique_object(pairs):
    obj = {}
    for key, value in pairs:
        if key in obj:
            raise ValueError("duplicate JSON key: " + repr(key))
        obj[key] = value
    return obj


def forbidden_number(token):
    raise ValueError("non-integer JSON number is forbidden: " + token)


def recompute_adaptive():
    """Bellman minimisation over every possible next free query.

    No certificate values, truth table, lower bounds, or trees are inputs.
    A monotone function is constant on a cube exactly when its values at
    the least and greatest vertices agree. Repeated queries give no new
    information, so an optimal strategy can always use only free bits.
    """
    @lru_cache(maxsize=None)
    def optimum(mask, value):
        if f1(value) == f1(value | (FULL ^ mask)):
            return Fraction(0)
        alternatives = []
        for i in range(N):
            bit = 1 << i
            if not mask & bit:
                next_mask = mask | bit
                alternatives.append(Fraction(1) +
                                    (optimum(next_mask, value) +
                                     optimum(next_mask, value | bit)) / 2)
        return min(alternatives)

    result = optimum(0, 0)
    return result


def verify(cert):
    failures = []

    def require(condition, message):
        if not condition:
            failures.append(message)

    def section(name, action):
        try:
            action()
        except (KeyError, TypeError, ValueError, ZeroDivisionError,
                RecursionError, IndexError) as exc:
            failures.append(name + ": " + str(exc))

    if not isinstance(cert, dict):
        return ["top-level JSON value must be an object"], None

    def metadata():
        if "n" in cert:
            require(type(cert["n"]) is int and cert["n"] == N, "n must be 5")
        for field, expected in (("p", Fraction(1, 2)), ("a_value", A_TARGET),
                                ("sc_value", SC_TARGET)):
            if field in cert:
                require(rational(cert[field]) == expected, field + " is incorrect")

    def truth_table():
        table = cert["truth_table"]
        if not isinstance(table, str) or len(table) != len(POINTS):
            raise ValueError("truth_table must be a 32-character string")
        if any(c not in "01" for c in table):
            raise ValueError("truth_table must contain only 0 and 1")
        values = tuple(int(c) for c in table)
        for x in POINTS:
            require(values[x] == f1(x), "truth_table differs from f1 at x=" + str(x))
            for i in range(N):
                bit = 1 << i
                if not x & bit:
                    require(values[x] <= values[x | bit],
                            "truth_table is not monotone on edge " + str((x, x | bit)))

    def lower_bound():
        raw = cert["lower_bound_table"]
        if not isinstance(raw, dict):
            raise ValueError("lower_bound_table must be an object")
        bounds = {decode_cube(key): rational(value) for key, value in raw.items()}
        if set(bounds) != set(CUBES):
            raise ValueError("lower_bound_table must contain exactly all 243 restrictions")
        require(bounds[0, 0] == A_TARGET, "lower_bound_table root is not 13/4")
        for mask, value in CUBES:
            lhs = bounds[mask, value]
            if len(COLORS[mask, value]) == 1:
                require(lhs <= 0, "lower_bound_table positive on constant cube " +
                        str((mask, value)))
            else:
                for i in range(N):
                    bit = 1 << i
                    if not mask & bit:
                        rhs = Fraction(1) + (bounds[mask | bit, value] +
                                             bounds[mask | bit, value | bit]) / 2
                        require(lhs <= rhs, "lower_bound_table inequality fails at " +
                                str((mask, value)) + ", query=" + str(i))

    def tree():
        root = cert["optimal_tree"]
        pending = [root]
        while pending:
            node = pending.pop()
            if not isinstance(node, dict):
                raise ValueError("every tree node must be an object")
            if set(node) == {"leaf"}:
                if type(node["leaf"]) is not int or node["leaf"] not in (0, 1):
                    raise ValueError("leaf label must be integer 0 or 1")
            elif set(node) == {"q", "0", "1"}:
                if type(node["q"]) is not int or not 0 <= node["q"] < N:
                    raise ValueError("tree query must be an integer in 0..4")
                pending.extend((node["0"], node["1"]))
            else:
                raise ValueError("tree node must have exactly leaf, or q/0/1")

        # Run the entire tree separately on every point. This also handles
        # repeated queries correctly, without assigning half-probability to
        # impossible branches of an already fixed bit.
        total_depth = 0
        for x in POINTS:
            node, mask, value, depth = root, 0, 0, 0
            while "q" in node:
                bit = 1 << node["q"]
                answer = int(bool(x & bit))
                mask |= bit
                if answer:
                    value |= bit
                depth += 1
                node = node[str(answer)]
            require(len(COLORS[mask, value]) == 1,
                    "tree stops with f1 undetermined at x=" + str(x))
            require(node["leaf"] == f1(x), "tree has wrong label at x=" + str(x))
            total_depth += depth
        require(Fraction(total_depth, len(POINTS)) == A_TARGET,
                "tree expected depth is " + str(Fraction(total_depth, len(POINTS))) +
                ", expected 13/4")

    def partition():
        raw = cert["partition"]
        if not isinstance(raw, list):
            raise ValueError("partition must be a list")
        coverage = [0] * len(POINTS)
        total_codimension = 0
        for index, encoded in enumerate(raw):
            cube = decode_cube(encoded)
            require(len(COLORS[cube]) == 1,
                    "partition cell " + str(index) + " is not monochromatic")
            members = MEMBERS[cube]
            total_codimension += cube[0].bit_count() * len(members)
            for x in members:
                coverage[x] += 1
        for x, count in enumerate(coverage):
            require(count == 1, "partition covers x=" + str(x) + " " + str(count) + " times")
        require(Fraction(total_codimension, len(POINTS)) == SC_TARGET,
                "partition expected codimension is " +
                str(Fraction(total_codimension, len(POINTS))) + ", expected 51/16")

    def dual():
        raw = cert["sc_dual"]
        if not isinstance(raw, list) or len(raw) != len(POINTS):
            raise ValueError("sc_dual must be a list of 32 rationals")
        y = tuple(rational(entry) for entry in raw)
        for cube in CUBES:
            if len(COLORS[cube]) == 1:
                members = MEMBERS[cube]
                lhs = sum((y[x] for x in members), Fraction(0))
                rhs = cube[0].bit_count() * len(members)
                require(lhs <= rhs, "sc_dual infeasible on cube " + str(cube) +
                        ": " + str(lhs) + " > " + str(rhs))
        objective = sum(y, Fraction(0)) / len(POINTS)
        require(objective == SC_TARGET,
                "sc_dual objective is " + str(objective) + ", expected 51/16")

    for name, action in (("metadata", metadata), ("truth_table", truth_table),
                         ("lower_bound_table", lower_bound), ("optimal_tree", tree),
                         ("partition", partition), ("sc_dual", dual)):
        section(name, action)
    recomputed = recompute_adaptive()
    require(recomputed == A_TARGET,
            "independent adaptive minimisation gives " + str(recomputed) + ", expected 13/4")
    return failures, recomputed


def main(argv):
    if len(argv) != 2:
        print("REJECT usage: check_independent.py certificate.json")
        return 1
    try:
        with open(argv[1], "r", encoding="utf-8") as source:
            cert = json.load(source, object_pairs_hook=unique_object,
                             parse_float=forbidden_number, parse_constant=forbidden_number)
        failures, recomputed = verify(cert)
    except (OSError, ValueError, TypeError, RecursionError) as exc:
        print("REJECT " + str(exc))
        return 1
    if failures:
        print("REJECT " + "; ".join(failures))
        return 1
    print("ACCEPT truth_table=32 monotone_edges=80 restrictions=243 "
          "lower_bound=13/4 tree=13/4 partition=51/16 dual=51/16 "
          "adaptive_recomputed=" + str(recomputed))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
