#!/usr/bin/env python3
"""Independent standalone checker A; no producer or other checker imports."""
import argparse
import json
import sys


class Rejection(Exception):
    def __init__(self, reason, detail):
        super().__init__(detail)
        self.reason = reason


def require(condition, reason, detail):
    if not condition:
        raise Rejection(reason, detail)


def exact_int(value):
    return type(value) is int


def pairs_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "SCHEMA", "duplicate JSON key")
        result[key] = value
    return result


def keys(value, expected):
    require(type(value) is dict and set(value) == set(expected),
            "SCHEMA", "unexpected object fields")


def check(certificate, small=False, generic=False):
    keys(certificate, ("format", "graph", "modules", "coefficients", "patterns"))
    require(certificate["format"] == "zf-unimodality-v1", "SCHEMA", "format")
    graph = certificate["graph"]
    keys(graph, ("n", "edges"))
    weights = (2, 3, 2, 2, 2, 2) if small else (32, 33, 2, 2, 2, 2)
    n = sum(weights)
    require(exact_int(graph["n"]) and graph["n"] == n, "GRAPH", "vertex count")
    modules = certificate["modules"]
    require(type(modules) is list and len(modules) == 6, "PARTITION", "module count")
    cursor = 0
    owner = [-1] * n
    for i, (block, weight) in enumerate(zip(modules, weights)):
        require(type(block) is list and all(exact_int(v) for v in block),
                "PARTITION", "module vertex types")
        require(block == list(range(cursor, cursor + weight)),
                "PARTITION", "canonical contiguous partition")
        for vertex in block:
            owner[vertex] = i
        cursor += weight
    edges = graph["edges"]
    require(type(edges) is list, "GRAPH", "edge array")
    adjacency = [set() for _ in range(n)]
    previous = (-1, -1)
    for edge in edges:
        require(type(edge) is list and len(edge) == 2 and
                all(exact_int(v) for v in edge), "GRAPH", "edge schema")
        u, v = edge
        require(0 <= u < v < n and (u, v) > previous, "GRAPH", "edge order/range/uniqueness")
        previous = (u, v)
        adjacency[u].add(v)
        adjacency[v].add(u)
    for block in modules:
        for u in block:
            for v in block:
                require(u == v or v in adjacency[u], "CLIQUE", "missing within-module edge")
    quotient = [[False] * 6 for _ in range(6)]
    for i in range(6):
        for j in range(i + 1, 6):
            linked = modules[j][0] in adjacency[modules[i][0]]
            quotient[i][j] = quotient[j][i] = linked
            for u in modules[i]:
                for v in modules[j]:
                    require((v in adjacency[u]) == linked, "QUOTIENT", "nonuniform module adjacency")
    if not generic:
        for i in range(6):
            for j in range(i + 1, 6):
                require(quotient[i][j] == ((i < 2) != (j < 2)),
                        "CANONICAL_GRAPH", "wrong canonical quotient")
    transpositions = 0
    forts = 0
    for block in modules:
        for position, u in enumerate(block):
            for v in block[position + 1:]:
                # Check the actual permutation on every vertex neighborhood.
                def swap(x):
                    return v if x == u else u if x == v else x
                for vertex in range(n):
                    require({swap(x) for x in adjacency[vertex]} == adjacency[swap(vertex)],
                            "TRANSPOSITION", "within-module permutation is not an automorphism")
                transpositions += 1
                # A fort has no outside vertex with exactly one neighbor in it.
                for vertex in range(n):
                    if vertex != u and vertex != v:
                        count = int(u in adjacency[vertex]) + int(v in adjacency[vertex])
                        require(count != 1, "PAIR_FORT", "within-module pair is not a fort")
                forts += 1
    coefficients = certificate["coefficients"]
    require(type(coefficients) is list and len(coefficients) == n + 1 and
            all(exact_int(c) and c >= 0 for c in coefficients), "SCHEMA", "coefficient vector")
    patterns = certificate["patterns"]
    require(type(patterns) is list and len(patterns) == 64, "PATTERNS", "must contain 64 patterns")
    total = [0] * (n + 1)
    for mask, record in enumerate(patterns):
        keys(record, ("mask", "forcing", "multiplicity"))
        require(exact_int(record["mask"]) and record["mask"] == mask,
                "PATTERNS", "mask order/coverage")
        require(type(record["forcing"]) is bool and exact_int(record["multiplicity"]),
                "SCHEMA", "pattern field types")
        white = set()
        multiplicity = 1
        for i, block in enumerate(modules):
            if mask & (1 << i):
                white.add(block[0])
                multiplicity *= len(block)
        require(record["multiplicity"] == multiplicity,
                "PATTERN_MULTIPLICITY", "wrong orbit size")
        # Simultaneous rounds differ from the producer's sequential updates.
        while white:
            forced = set()
            for vertex in range(n):
                if vertex not in white:
                    unseen = adjacency[vertex].intersection(white)
                    if len(unseen) == 1:
                        forced.update(unseen)
            if not forced:
                break
            white.difference_update(forced)
        forcing = not white
        require(record["forcing"] == forcing,
                "PATTERN_FORCING", "ordinary forcing mismatch at mask " + str(mask))
        if record["forcing"]:
            total[n - mask.bit_count()] += record["multiplicity"]
    require(coefficients == total, "COEFFICIENTS", "serialized polynomial differs from pattern sum")
    if not small and not generic:
        # Supplied candidate prediction is checked only after independent closure
        # and coefficient reconstruction, and only when this leaf is released.
        prediction = [0] * 69 + [2096, 1592, 1600, 73, 1]
        require(coefficients == prediction, "TARGET_PREDICTION", "candidate prediction failed")
        require(coefficients[69] > coefficients[70] < coefficients[71],
                "TARGET_DIP", "candidate strict dip failed")
    return {"status": "ok", "reason": "VERIFIED", "patterns": 64,
            "transpositions": transpositions, "pair_forts": forts,
            "mode": "generic-audit" if generic else "canonical"}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("certificate")
    parser.add_argument("--small", action="store_true")
    parser.add_argument("--generic-audit", action="store_true")
    args = parser.parse_args()
    with open(args.certificate, "rb") as handle:
        raw = handle.read(2_000_000)
        require(len(raw) < 2_000_000 and not handle.read(1), "SCHEMA", "file size")
    try:
        certificate = json.loads(raw, object_pairs_hook=pairs_object,
                                 parse_constant=lambda x: (_ for _ in ()).throw(ValueError(x)))
    except Rejection:
        raise
    except (ValueError, UnicodeError) as error:
        raise Rejection("SCHEMA", str(error)) from error
    print(json.dumps(check(certificate, args.small, args.generic_audit), sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except Rejection as error:
        print(json.dumps({"status": "reject", "reason": error.reason, "detail": str(error)}))
        sys.exit(1)
    except Exception as error:
        print(json.dumps({"status": "reject", "reason": "CHECKER_ERROR", "detail": str(error)}))
        sys.exit(2)
