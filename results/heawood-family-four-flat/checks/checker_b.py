#!/usr/bin/env python3
"""Independent recursive cellular invariant checker. GPT-6.1 Sol checker builder."""
import hashlib
import json
import sys


def require(test, reason):
    if not test:
        raise ValueError(reason)


def integer(x):
    return type(x) is int


def toggle(s, x):
    if x in s:
        s.remove(x)
    else:
        s.add(x)


def check(doc):
    require(type(doc) is dict, "certificate must be an object")
    require(doc.get("format") == "cycle-vk-mod2-v1", "unsupported format")
    n = doc.get("vertices")
    require(integer(n) and n >= 0, "invalid vertex count")
    edges, cycles, pairs = (doc.get(k) for k in ("edges", "cycles", "pairs"))
    require(all(type(x) is list for x in (edges, cycles, pairs)), "missing lists")
    edge_ids = {}
    for i, e in enumerate(edges):
        require(type(e) is list and len(e) == 2 and all(integer(v) for v in e), "invalid edge")
        u, v = e
        require(0 <= u < v < n, "edge endpoints out of range or order")
        require(tuple(e) not in edge_ids, "duplicate edge")
        edge_ids[tuple(e)] = i
    seen = set()
    boundaries = {(0, v): () for v in range(n)}
    for i, (u, v) in enumerate(edges):
        boundaries[1, i] = ((0, u), (0, v))
    supports = []
    for i, c in enumerate(cycles):
        require(type(c) is list and len(c) >= 3 and all(integer(v) for v in c), "invalid cycle")
        require(all(0 <= v < n for v in c) and len(set(c)) == len(c), "cycle is not simple or in range")
        require(c[0] == min(c) and c[1] < c[-1], "cycle not canonical")
        require(tuple(c) not in seen, "duplicate cycle")
        seen.add(tuple(c))
        boundary = []
        for u, v in zip(c, c[1:] + c[:1]):
            e = tuple(sorted((u, v)))
            require(e in edge_ids, "cycle edge missing")
            boundary.append((1, edge_ids[e]))
        boundaries[2, i] = tuple(boundary)
        supports.append(set(c))
    chain = set()
    seen_pairs = set()
    for pair in pairs:
        require(type(pair) is list and len(pair) == 2 and all(integer(v) for v in pair), "invalid pair")
        i, j = pair
        require(0 <= i < j < len(cycles), "pair indices out of range or order")
        require((i, j) not in seen_pairs, "duplicate pair")
        seen_pairs.add((i, j))
        require(supports[i].isdisjoint(supports[j]), "pair supports intersect")
        chain.add(((2, i), (2, j)))
        chain.add(((2, j), (2, i)))

    def boundary(c):
        out = set()
        for a, b in c:
            for f in boundaries[a]:
                toggle(out, (f, b))
            for f in boundaries[b]:
                toggle(out, (a, f))
        return out

    levels = []
    for dim in range(4, -1, -1):
        require(all(a != b and a[0] + b[0] == dim for a, b in chain), "invalid product dimension or diagonal")
        require({(b, a) for a, b in chain} == chain, "chain not swap symmetric")
        bd = boundary(chain)
        require(not bd, "nonzero boundary at dimension " + str(dim))
        half = {(a, b) for a, b in chain if a < b}
        require(len(half) * 2 == len(chain), "half-chain orbit failure")
        levels.append({"dimension": dim, "ordered_cells": len(chain), "half_cells": len(half)})
        if dim:
            chain = boundary(half)
        else:
            invariant = len(half) % 2
    require(invariant == 1, "invariant is zero")
    return {"valid": True, "invariant": invariant, "vertices": n, "edges": len(edges),
            "cycles": len(cycles), "pairs": len(pairs), "levels": levels}


def main():
    try:
        require(len(sys.argv) == 2, "usage: checker_b.py CERTIFICATE.json")
        with open(sys.argv[1], "rb") as f:
            raw = f.read()
        result = check(json.loads(raw))
        result["certificate_sha256"] = hashlib.sha256(raw).hexdigest()
        print(json.dumps(result, sort_keys=True))
        return 0
    except (ValueError, OSError, TypeError, KeyError, OverflowError) as exc:
        print(json.dumps({"valid": False, "reason": str(exc)}, sort_keys=True))
        return 1


if __name__ == "__main__":
    sys.exit(main())
