#!/usr/bin/env python3
"""Check a 3-edge-colouring of K_n (lines "i j c") colours every edge once
and has no monochromatic path on m vertices (exhaustive DFS).  Independent
of the encoder and solver.  usage: check_colouring.py n m FILE"""
import sys, itertools

def main():
    n, m, path = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    col = {}
    for line in open(path):
        i, j, c = map(int, line.split())
        e = (min(i, j), max(i, j))
        if e in col or i == j or not (0 <= c < 3) or max(i, j) >= n:
            sys.exit(f'bad line: {line.strip()}')
        col[e] = c
    if len(col) != n * (n - 1) // 2:
        sys.exit('not every edge coloured')
    for c in range(3):
        adj = [[w for w in range(n) if w != v and col[(min(v, w), max(v, w))] == c] for v in range(n)]
        def longest(v, seen):
            best = 1
            for w in adj[v]:
                if w not in seen:
                    seen.add(w)
                    best = max(best, 1 + longest(w, seen))
                    seen.discard(w)
                    if best >= m:
                        return best
            return best
        for s in range(n):
            L = longest(s, {s})
            if L >= m:
                print(f'colour {c} has a path on {m} vertices from {s}: NOT a good colouring')
                sys.exit(1)
    print(f'check_colouring: K_{n} colouring has no monochromatic P_{m}')

if __name__ == '__main__':
    main()
