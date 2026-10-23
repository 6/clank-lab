#!/usr/bin/env python3
"""Standalone checker written from definitions (EJC 18(2011) P214) only.
Usage: python3 -I indep_check.py certificate.json  -> prints JSON, exit 0 iff accepted."""
import json, sys, itertools
from collections import deque

def check(cert):
    errs = []
    rows, start, path, closed = cert["rows"], cert["start"], cert["regular_moves"], set(cert["closed"])
    n = 7
    if len(rows) != n or any(not isinstance(r, int) or not 0 <= r < 2**n for r in rows):
        return ["bad rows"], {}
    # graph as explicit edge sets, from rows (bit j of row i = edge i-j)
    nb = [{j for j in range(n) if rows[i] >> j & 1} for i in range(n)]
    for i in range(n):
        if i in nb[i]: errs.append(f"loop at {i}")
        for j in nb[i]:
            if i not in nb[j]: errs.append(f"asymmetric {i},{j}")
    # faithfulness: complement of C6 + K1
    c6 = {frozenset((i, (i + 1) % 6)) for i in range(6)}
    edges = {frozenset((i, j)) for i in range(n) for j in nb[i]}
    want = {frozenset(p) for p in itertools.combinations(range(n), 2)} - c6 - {frozenset((i, 6)) for i in ()}
    # K1 vertex 6 is isolated in the disjoint union, so adjacent to all in the complement
    if edges != want: errs.append("graph != complement(C6 + K1)")
    # connected (BFS)
    seen, q = {0}, deque([0])
    while q:
        u = q.popleft()
        for w in nb[u]:
            if w not in seen: seen.add(w); q.append(w)
    if len(seen) != n: errs.append("not connected")
    # not complete multipartite for any m>=1: non-adjacency (distinct) must be an equivalence relation
    non = lambda a, b: a != b and b not in nb[a]
    trans = all(non(a, c) for a in range(n) for b in range(n) for c in range(n)
                if a != c and non(a, b) and non(b, c))
    if trans: errs.append("could be complete multipartite")
    # states as sets of lit vertices
    def lit(z): return frozenset(v for v in range(n) if z >> v & 1)
    def toggle(S, v): return S ^ nb[v]   # symmetric difference with neighbours
    S0 = lit(start)
    # regular path
    S = S0
    for v in path: S = toggle(S, v)
    reg_after = len(S)
    if reg_after != 0: errs.append("regular path does not reach 0")
    # lit-only closure: closed set contains start, every lit-move successor inside, min weight
    C = {lit(z) for z in closed}
    if S0 not in C: errs.append("start not in closed")
    for T in C:
        for v in T:
            if toggle(T, v) not in C: errs.append(f"not closed at {sorted(T)},{v}")
    lb = min(len(T) for T in C)
    if lb < 4: errs.append("lower bound <4")
    if 2 * lb <= n: errs.append("not >7/2")
    # recompute independently by exhaustive reachability from definitions
    def reach(lo):
        seen, q = {S0}, deque([S0])
        while q:
            T = q.popleft()
            for v in range(n):
                if lo and v not in T: continue
                U = toggle(T, v)
                if U not in seen: seen.add(U); q.append(U)
        return min(len(T) for T in seen)
    ml, mls = reach(False), reach(True)
    if (ml, mls) != (0, lb): errs.append(f"recompute mismatch ML={ml} ML*={mls} lb={lb}")
    info = dict(edges=len(edges), connected=len(seen) == n, regular_path_final_weight=reg_after,
                closed_size=len(C), lower_bound=lb, ML=ml, ML_star=mls,
                difference=mls - ml, threshold_n_over_2=n / 2)
    return errs, info

if __name__ == "__main__":
    cert = json.load(open(sys.argv[1]))
    errs, info = check(cert)
    print(json.dumps({"accepted": not errs, "errors": errs, **info}, sort_keys=True))
    sys.exit(0 if not errs else 1)
