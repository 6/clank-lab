"""Write the CNF "graph.txt is properly 3-colourable" in DIMACS form.

Variable 3*v + c + 1 means vertex v has colour c.  Each vertex gets at least
one and at most one colour; adjacent vertices differ.  Symmetry: the
lexicographically first triangle (u < v < w) is fixed to colours 0, 1, 2,
which loses no generality because colours can be permuted.  Standard
library only.

Usage: col3_cnf.py graph.txt > col3.cnf
"""
import sys


def main():
    n = m = None
    edges = []
    for line in open(sys.argv[1]):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        a, b = (int(x) for x in line.split())
        if n is None:
            n, m = a, b
            continue
        edges.append((min(a, b), max(a, b)))
    assert len(edges) == m
    adj = [set() for _ in range(n)]
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)
    tri = None
    for u in range(n):
        for v in sorted(adj[u]):
            if v <= u:
                continue
            for w in sorted(adj[u] & adj[v]):
                if w > v:
                    tri = (u, v, w)
                    break
            if tri:
                break
        if tri:
            break
    x = lambda v, c: 3 * v + c + 1
    cls = []
    for v in range(n):
        cls.append([x(v, 0), x(v, 1), x(v, 2)])
        for a in range(3):
            for b in range(a + 1, 3):
                cls.append([-x(v, a), -x(v, b)])
    for a, b in edges:
        for c in range(3):
            cls.append([-x(a, c), -x(b, c)])
    if tri:
        for i, v in enumerate(tri):
            cls.append([x(v, i)])
    out = sys.stdout
    out.write("c 3-colourability of %s; fixed triangle %s\n" % (sys.argv[1], tri))
    out.write("p cnf %d %d\n" % (3 * n, len(cls)))
    for c in cls:
        out.write(" ".join(map(str, c)) + " 0\n")


if __name__ == "__main__":
    main()
