"""Decide 3-colourability exactly by variable (bucket) elimination.

Standard library only; shares no code with the SAT route.  Every edge is a
binary "different colours" constraint.  Vertices are eliminated in
min-degree order of the current interaction graph; eliminating v joins all
constraints that mention v and projects v out.  The graph is 3-colourable
iff no constraint ever becomes empty.  The largest constraint scope is
reported (it counts the remaining variables after the eliminated one is
projected out).

Usage: check_col_elim.py graph.txt [--expect noncolourable|colourable]
Exit 0 when the result matches the expectation (default: noncolourable).
"""
import itertools
import sys


def read_graph(path):
    n = m = None
    edges = []
    for line in open(path):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        a, b = (int(x) for x in line.split())
        if n is None:
            n, m = a, b
            continue
        if not (0 <= a < n and 0 <= b < n) or a == b:
            raise SystemExit("bad edge %d %d" % (a, b))
        edges.append((a, b))
    if n is None or len(edges) != m or len(set(frozenset(e) for e in edges)) != m:
        raise SystemExit("bad header, edge count or repeated edge")
    return n, edges


def colourable(n, edges):
    # a constraint is (scope tuple, set of allowed colour tuples)
    cons = []
    for a, b in edges:
        allowed = {(x, y) for x in range(3) for y in range(3) if x != y}
        cons.append(((a, b), allowed))
    alive = set(range(n))
    maxscope = 0
    while alive:
        nbrs = {v: set() for v in alive}
        for scope, _ in cons:
            for u in scope:
                nbrs[u].update(w for w in scope if w != u)
        v = min(alive, key=lambda x: (len(nbrs[x]), x))
        mine = [c for c in cons if v in c[0]]
        cons = [c for c in cons if v not in c[0]]
        scope = tuple(sorted(set(u for s, _ in mine for u in s) - {v}))
        maxscope = max(maxscope, len(scope))
        allowed = set()
        for vals in itertools.product(range(3), repeat=len(scope)):
            asg = dict(zip(scope, vals))
            for cv in range(3):
                asg[v] = cv
                if all(tuple(asg[u] for u in s) in ok for s, ok in mine):
                    allowed.add(vals)
                    break
        if not allowed:
            return False, maxscope
        if scope:
            cons.append((scope, allowed))
        alive.discard(v)
    return True, maxscope


def main():
    path = sys.argv[1]
    expect = "noncolourable"
    if len(sys.argv) > 3 and sys.argv[2] == "--expect":
        expect = sys.argv[3]
    n, edges = read_graph(path)
    ok, w = colourable(n, edges)
    res = "colourable" if ok else "noncolourable"
    print("%s: %s (n=%d, m=%d, largest eliminated scope %d)" % (path, res.upper(), n, len(edges), w))
    sys.exit(0 if res == expect else 1)


if __name__ == "__main__":
    main()
