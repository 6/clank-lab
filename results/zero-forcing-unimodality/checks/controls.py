#!/usr/bin/env python3
"""Standalone future controls; never import producer or checkers."""
import argparse
import json
import math
import sys


def polynomial(n, edges):
    neighbors = [set() for _ in range(n)]
    for u, v in edges:
        neighbors[u].add(v)
        neighbors[v].add(u)
    counts = [0] * (n + 1)
    for seed in range(1 << n):
        blue = {v for v in range(n) if seed & (1 << v)}
        initial = len(blue)
        while True:
            additions = set()
            for v in blue:
                white_neighbors = neighbors[v] - blue
                if len(white_neighbors) == 1:
                    additions.update(white_neighbors)
            if not additions:
                break
            blue.update(additions)
        if len(blue) == n:
            counts[initial] += 1
    return counts


def symbolic(u, v):
    n = u + v + 8
    result = [0] * (n + 1)
    for s in range(5):
        result[n - s] += math.comb(4, s) * 2 ** s
    for s in range(4):
        result[n - 1 - s] += (u + v) * math.comb(4, s) * 2 ** s
    result[n - 2] += u * v
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("case", choices=("K6", "P4", "C4", "small"))
    parser.add_argument("--certificate")
    args = parser.parse_args()
    if args.case == "K6":
        n = 6
        edges = [(u, v) for u in range(n) for v in range(u + 1, n)]
        expected = [0, 0, 0, 0, 0, 6, 1]
    elif args.case == "P4":
        n, edges, expected = 4, [(0, 1), (1, 2), (2, 3)], [0, 2, 6, 4, 1]
    elif args.case == "C4":
        n, edges, expected = 4, [(0, 1), (1, 2), (2, 3), (0, 3)], [0, 0, 4, 4, 1]
    else:
        weights = (2, 3, 2, 2, 2, 2)
        owner = [i for i, weight in enumerate(weights) for _ in range(weight)]
        n = len(owner)
        edges = [(u, v) for u in range(n) for v in range(u + 1, n)
                 if owner[u] == owner[v] or ((owner[u] < 2) != (owner[v] < 2))]
        expected = symbolic(2, 3)
    actual = polynomial(n, edges)
    if actual != expected:
        print(json.dumps({"status": "reject", "reason": "CONTROL_MISMATCH", "case": args.case}))
        return 1
    if args.case == "small":
        if not args.certificate:
            raise ValueError("small control requires --certificate")
        with open(args.certificate, "rb") as handle:
            raw = handle.read(2_000_000)
            if handle.read(1):
                raise ValueError("oversize small certificate")
        if json.loads(raw)["coefficients"] != expected:
            print(json.dumps({"status": "reject", "reason": "CONTROL_MISMATCH", "case": args.case}))
            return 1
    elif args.certificate:
        raise ValueError("--certificate is only for the small control")
    print(json.dumps({"status": "ok", "reason": "CONTROL_OK", "case": args.case,
                      "subsets": 1 << n}))
    return 0


if __name__ == "__main__":
    sys.exit(main())
