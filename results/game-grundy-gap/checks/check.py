#!/usr/bin/env python3
"""Check a literal strategy DAG; no imports from any search implementation."""
import json
import sys


def require(ok, message):
    if not ok:
        raise ValueError(message)


def integer(x):
    return type(x) is int


def verify(cert):
    require(cert.get('version') == 1, 'version')
    n, k = cert['n'], cert['k']
    require(integer(n) and 1 <= n <= 15, 'n')
    require(integer(k) and 1 <= k <= n, 'k')
    require(cert['game'] in ('ordinary', 'greedy'), 'game')
    require(cert['first'] in ('Alice', 'Bob'), 'first')
    require(cert['winner'] in ('Alice', 'Bob'), 'winner')
    require(type(cert['ordered']) is bool, 'ordered')
    adj = [set() for _ in range(n)]
    seen_edges = set()
    for edge in cert['edges']:
        require(type(edge) is list and len(edge) == 2, 'edge')
        u, v = edge
        require(integer(u) and integer(v) and 0 <= u < v < n, 'edge endpoints')
        require((u, v) not in seen_edges, 'duplicate edge')
        seen_edges.add((u, v))
        adj[u].add(v)
        adj[v].add(u)
    nodes = cert['nodes']
    require(type(nodes) is dict, 'nodes')
    stack = [(0,) * n]
    reached = set()
    while stack:
        s = stack.pop()
        key = ','.join(map(str, s))
        if key in reached:
            continue
        reached.add(key)
        require(key in nodes, 'missing state ' + key)
        require(all(0 <= c <= k for c in s), 'colour')
        require(all(not s[u] or s[u] != s[v] for u, v in seen_edges), 'improper state')
        moves = nodes[key]
        require(type(moves) is list, 'moves')
        legal = []
        blocked = False
        empty = [u for u in range(n) if not s[u]]
        for u in empty:
            absent = set(range(1, k + 1)) - {s[v] for v in adj[u]}
            if not absent:
                blocked = True
            if not cert['ordered'] or u == empty[0]:
                colours = sorted(absent)
                if cert['game'] == 'greedy':
                    colours = colours[:1]
                legal.extend((u, c) for c in colours)
        terminal = 'Alice' if not empty else 'Bob' if blocked else None
        if terminal:
            require(terminal == cert['winner'] and moves == [], 'false terminal')
            continue
        for m in moves:
            require(type(m) is list and len(m) == 2 and all(integer(x) for x in m), 'move format')
        selected = [tuple(m) for m in moves]
        require(len(set(selected)) == len(selected), 'duplicate move')
        turn = cert['first'] if (n - len(empty)) % 2 == 0 else ('Bob' if cert['first'] == 'Alice' else 'Alice')
        if turn == cert['winner']:
            require(len(selected) == 1 and selected[0] in legal, 'winner move')
        else:
            require(set(selected) == set(legal), 'opponent coverage')
        for u, c in selected:
            t = list(s)
            t[u] = c
            stack.append(tuple(t))
    require(reached == set(nodes), 'unreachable or noncanonical states')
    return {'accepted': True, 'winner': cert['winner'], 'nodes': len(reached)}


def no_duplicate_keys(pairs):
    d = {}
    for k, v in pairs:
        require(k not in d, 'duplicate JSON key')
        d[k] = v
    return d


if __name__ == '__main__':
    try:
        with open(sys.argv[1]) as f:
            cert = json.load(f, object_pairs_hook=no_duplicate_keys)
        print(json.dumps(verify(cert), sort_keys=True))
    except (ValueError, KeyError, TypeError, IndexError) as e:
        print('REJECT: ' + str(e), file=sys.stderr)
        sys.exit(1)
