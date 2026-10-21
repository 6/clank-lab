#!/usr/bin/env python3
"""Check that every clause in a clause log is a path clause: for some colour
c and some path v_1 ... v_m on m distinct vertices of K_n, the clause is
exactly { -x((v_i, v_i+1), c) : i = 1..m-1 }, which every colouring with no
monochromatic P_m satisfies.  Shares no code with the encoder or solver;
variable convention x(e,c) = 3e + c + 1, edges (i,j), i<j, row-wise.

usage: check_paths.py n m LOG [LOG ...]   (exit 0 iff every clause passes)
"""
import sys, itertools

def main():
    n, m = int(sys.argv[1]), int(sys.argv[2])
    edges = list(itertools.combinations(range(n), 2))
    total = 0
    for path in sys.argv[3:]:
        with open(path) as f:
            for ln, line in enumerate(f, 1):
                lits = [int(t) for t in line.split()]
                if not lits or lits[-1] != 0:
                    sys.exit(f'{path}:{ln}: not a 0-terminated clause')
                lits = lits[:-1]
                if len(lits) != m - 1 or len(set(lits)) != m - 1:
                    sys.exit(f'{path}:{ln}: expected {m-1} distinct literals')
                cols, adj = set(), {}
                for l in lits:
                    if l >= 0 or -l > 3 * len(edges):
                        sys.exit(f'{path}:{ln}: literal {l} is not a negated colour variable')
                    e, c = divmod(-l - 1, 3)
                    cols.add(c)
                    a, b = edges[e]
                    adj.setdefault(a, []).append(b)
                    adj.setdefault(b, []).append(a)
                if len(cols) != 1:
                    sys.exit(f'{path}:{ln}: mixed colours')
                # m-1 distinct edges forming a path on m vertices: connected,
                # m vertices, all degrees <= 2, exactly two of degree 1.
                if len(adj) != m or any(len(v) > 2 for v in adj.values()):
                    sys.exit(f'{path}:{ln}: edges do not form a path on {m} vertices')
                ends = [v for v, nb in adj.items() if len(nb) == 1]
                if len(ends) != 2:
                    sys.exit(f'{path}:{ln}: not a path')
                seen, stack = {ends[0]}, [ends[0]]
                while stack:
                    for w in adj[stack.pop()]:
                        if w not in seen:
                            seen.add(w); stack.append(w)
                if len(seen) != m:
                    sys.exit(f'{path}:{ln}: not connected')
                total += 1
    print(f'check_paths: {total} path clauses OK (n={n}, m={m})')

if __name__ == '__main__':
    main()
