"""Certify planarity from a rotation system.

Checks that rotation.txt lists, for every vertex, a cyclic order of exactly
its neighbours in graph.txt; traces the faces of the induced combinatorial
map (the face after dart u->v is v->w, where w follows u in the rotation at
v); and checks that the graph is connected with V - E + F = 2.  A connected
rotation system with Euler characteristic 2 is a cellular embedding in the
sphere, so the graph is planar.

Usage: check_planar.py graph.txt rotation.txt
"""
import sys


def read_graph(path):
    n = m = None
    adj = None
    cnt = 0
    for line in open(path):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        a, b = (int(x) for x in line.split())
        if n is None:
            n, m = a, b
            adj = [set() for _ in range(n)]
            continue
        if not (0 <= a < n and 0 <= b < n) or a == b or b in adj[a]:
            raise SystemExit("bad or repeated edge")
        adj[a].add(b)
        adj[b].add(a)
        cnt += 1
    if cnt != m:
        raise SystemExit("edge count mismatch")
    return n, m, adj


def read_rotation(path, n):
    rot = {}
    for line in open(path):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        v, rest = line.split(":")
        rot[int(v)] = [int(x) for x in rest.split()]
    if sorted(rot) != list(range(n)):
        raise SystemExit("rotation must list every vertex once")
    return rot


def main():
    n, m, adj = read_graph(sys.argv[1])
    rot = read_rotation(sys.argv[2], n)
    for v in range(n):
        if len(rot[v]) != len(set(rot[v])) or set(rot[v]) != adj[v]:
            print("REJECT: rotation at %d is not a cyclic order of its neighbours" % v)
            sys.exit(1)
    # connectivity
    seen = {0}
    stack = [0]
    while stack:
        v = stack.pop()
        for w in adj[v]:
            if w not in seen:
                seen.add(w)
                stack.append(w)
    if len(seen) != n:
        print("REJECT: graph is not connected")
        sys.exit(1)
    pos = {v: {w: i for i, w in enumerate(rot[v])} for v in range(n)}
    darts = {(u, v) for u in range(n) for v in adj[u]}
    faces = 0
    while darts:
        start = next(iter(darts))
        d = start
        while True:
            darts.discard(d)
            u, v = d
            r = rot[v]
            w = r[(pos[v][u] + 1) % len(r)]
            d = (v, w)
            if d == start:
                break
        faces += 1
    chi = n - m + faces
    print("%s: V=%d E=%d F=%d, V-E+F=%d" % (sys.argv[2], n, m, faces, chi))
    if chi != 2:
        print("REJECT: not a spherical embedding")
        sys.exit(1)
    print("OK: planar (spherical rotation system)")


if __name__ == "__main__":
    main()
