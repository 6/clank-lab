"""Count the simple cycles of each length up to LMAX and reject forbidden ones.

Standard library only.  Every simple cycle is counted once: it is grown from
its smallest vertex s through larger vertices only, and kept when its second
vertex is smaller than its last.

Usage: check_cycles.py graph.txt [LMAX] [--forbid 4,9,10]
Exit 0 iff no cycle has a forbidden length.
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
            raise SystemExit("bad or repeated edge %d %d" % (a, b))
        adj[a].add(b)
        adj[b].add(a)
        cnt += 1
    if cnt != m:
        raise SystemExit("edge count mismatch")
    return n, [sorted(s) for s in adj]


def spectrum(n, adj, lmax):
    counts = [0] * (lmax + 1)
    for s in range(n):
        # iterative DFS over paths s -> ... with all inner vertices > s
        stack = [(s, [s], {s})]
        while stack:
            v, path, used = stack.pop()
            for w in adj[v]:
                if w == s:
                    if len(path) >= 3 and path[1] < path[-1]:
                        counts[len(path)] += 1
                elif w > s and w not in used and len(path) < lmax:
                    stack.append((w, path + [w], used | {w}))
    return counts


def main():
    path = sys.argv[1]
    lmax = 10
    forbid = {4, 9}
    args = sys.argv[2:]
    if args and not args[0].startswith("--"):
        lmax = int(args.pop(0))
    if args and args[0] == "--forbid":
        forbid = {int(x) for x in args[1].split(",")}
    n, adj = read_graph(path)
    counts = spectrum(n, adj, lmax)
    present = {l: counts[l] for l in range(3, lmax + 1) if counts[l]}
    bad = sorted(l for l in forbid if l <= lmax and counts[l])
    print("%s: cycle counts by length (<= %d): %s" % (path, lmax, present))
    if bad:
        print("REJECT: cycles of forbidden length(s) %s" % bad)
        sys.exit(1)
    print("OK: no cycle of length in %s" % sorted(forbid))


if __name__ == "__main__":
    main()
