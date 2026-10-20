#!/usr/bin/env python3
"""Standalone exact certificate checker (Python standard library only).

Usage: python3 check_ore.py GRAPH TREE ROTATION DELETION_COLORINGS
No search, SAT solver, repository imports, or network access is used.
"""
import json
from pathlib import Path
import sys


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def integers(values):
    require(isinstance(values, list) and all(type(v) is int for v in values),
            'expected an integer list')
    return values


def unique(values):
    values = integers(values)
    require(len(set(values)) == len(values), 'repeated label')
    return set(values)


def edge(u, v):
    require(type(u) is int and type(v) is int and u != v, 'bad edge')
    return min(u, v), max(u, v)


def graph(path):
    rows = [list(map(int, s.split())) for line in Path(path).read_text().splitlines()
            if (s := line.split('#')[0].strip())]
    require(len(rows[0]) == 2, 'graph header')
    n, m = rows[0]
    require((n, m) == (82, 136), 'expected the 82-vertex, 136-edge witness')
    require(len(rows) == m + 1 and all(len(r) == 2 for r in rows[1:]),
            'edge row count or width')
    edges = {edge(*r) for r in rows[1:]}
    require(len(edges) == m and all(0 <= u < v < n for u, v in edges),
            'graph is not simple on the declared vertices')
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    require(all(adj), 'isolated vertex')
    seen, todo = {0}, [0]
    while todo:
        for w in adj[todo.pop()] - seen:
            seen.add(w)
            todo.append(w)
    require(len(seen) == n, 'disconnected graph')
    return edges, adj


def planar(adj, path):
    rotations = {}
    for line in Path(path).read_text().splitlines():
        s = line.split('#')[0].strip()
        if not s:
            continue
        a, b = s.split(':')
        v = int(a)
        require(v not in rotations, 'repeated rotation vertex')
        rotations[v] = integers(list(map(int, b.split())))
    require(set(rotations) == set(range(len(adj))), 'rotation vertex set')
    successor = {}
    for v, neighbors in rotations.items():
        require(unique(neighbors) == adj[v], 'rotation neighbor mismatch')
        for i, u in enumerate(neighbors):
            successor[u, v] = (v, neighbors[(i + 1) % len(neighbors)])
    unseen, faces = set(successor), 0
    while unseen:
        start = min(unseen)
        dart = start
        while dart in unseen:
            unseen.remove(dart)
            dart = successor[dart]
        require(dart == start, 'face permutation does not close')
        faces += 1
    require(len(adj) - len(successor) // 2 + faces == 2,
            'rotation surface does not have Euler characteristic two')
    return faces


def cycles(adj):
    # Each cycle is started at its least vertex; the two orientations
    # are distinguished by comparing its second and last vertices.
    counts = [0] * 11
    for start in range(len(adj)):
        def extend(path, used):
            v = path[-1]
            if len(path) >= 3 and start in adj[v] and path[1] < v:
                counts[len(path)] += 1
            if len(path) == 10:
                return
            for w in sorted(adj[v]):
                if w > start and w not in used:
                    extend(path + [w], used | {w})
        extend([start], {start})
    require(counts[4] == counts[9] == counts[10] == 0, 'forbidden simple cycle')
    return counts[3:]


def ore(edges, n, path):
    tree = json.loads(Path(path).read_text())
    require(tree['format'] == 'ore-tree-1', 'tree format')
    nodes = tree['nodes']
    require(isinstance(nodes, list) and len(nodes) == 53, 'tree node count')
    built, uses = [], [0] * len(nodes)
    leaves = joins = 0
    for i, node in enumerate(nodes):
        if node['kind'] == 'K4':
            vs = unique(node['vertices'])
            require(len(vs) == 4, 'leaf is not K4')
            es = {edge(u, v) for u in vs for v in vs if u < v}
            leaves += 1
        else:
            require(node['kind'] == 'ore', 'unknown tree operation')
            a, b = node['left'], node['right']
            require(type(a) is int and type(b) is int and 0 <= a < i and 0 <= b < i
                    and a != b, 'children must be distinct earlier nodes')
            uses[a] += 1
            uses[b] += 1
            av, ae = built[a]
            bv, be = built[b]
            require(not av & bv, 'Ore operands are not vertex disjoint')
            xy = integers(node['edge'])
            require(len(xy) == 2, 'deleted edge width')
            x, y = xy
            require(edge(x, y) in ae, 'deleted edge absent from first operand')
            z = node['split']
            require(type(z) is int and z in bv, 'split vertex absent')
            nx, ny = unique(node['x_neighbors']), unique(node['y_neighbors'])
            neighbors = {v if u == z else u for u, v in be if z in (u, v)}
            require(nx and ny and not nx & ny and nx | ny == neighbors,
                    'split must partition the full neighborhood into two nonempty sets')
            vs = av | (bv - {z})
            es = (ae - {edge(x, y)}) | {e for e in be if z not in e}
            es |= {edge(x, w) for w in nx} | {edge(y, w) for w in ny}
            require(len(vs) == len(av) + len(bv) - 1 and
                    len(es) == len(ae) + len(be) - 1, 'Ore size invariant')
            joins += 1
        # Each accepted leaf is not 3-colorable. An accepted Ore join
        # preserves this property by the equality/identification argument.
        built.append((vs, es))
    root = tree['root']
    require(type(root) is int and root == len(nodes) - 1, 'tree root')
    require(uses[root] == 0 and all(u == 1 for u in uses[:root]),
            'certificate is not a tree using every node once')
    require((leaves, joins) == (27, 26), 'K4/Ore counts')
    mapping = {}
    for pair in tree['isomorphism']:
        require(len(integers(pair)) == 2, 'isomorphism pair')
        u, v = pair
        require(u not in mapping, 'repeated isomorphism source')
        mapping[u] = v
    vs, es = built[root]
    require(set(mapping) == vs and set(mapping.values()) == set(range(n))
            and len(mapping) == n, 'isomorphism is not a bijection')
    require({edge(mapping[u], mapping[v]) for u, v in es} == edges,
            'replayed graph differs from the published graph under the stated isomorphism')
    return leaves, joins


def critical(edges, n, path):
    data = json.loads(Path(path).read_text())
    require(data['format'] == 'edge-deletion-1', 'coloring format')
    rows = data['colorings']
    require(len(rows) == len(edges), 'wrong number of deletion colorings')
    seen = set()
    four = None
    for row in rows:
        pair = integers(row['edge'])
        require(len(pair) == 2, 'deletion edge width')
        deleted = edge(*pair)
        require(deleted in edges and deleted not in seen, 'missing or repeated deletion edge')
        seen.add(deleted)
        c = integers(row['colors'])
        require(len(c) == n and set(c) <= {0, 1, 2}, 'coloring domain or length')
        require(all(c[u] != c[v] for u, v in edges - {deleted}),
                f'improper coloring after deleting {deleted}')
        require(c[deleted[0]] == c[deleted[1]], 'deletion endpoints must have equal colors')
        four = c.copy()
        four[deleted[0]] = 3
    require(seen == edges, 'incomplete deletion coverage')
    require(all(four[u] != four[v] for u, v in edges), 'derived four-coloring failed')
    # No isolated vertices: every proper subgraph omits an edge, so one
    # of these colorings restricts to it. The derived coloring proves chi<=4.
    require(3 * len(edges) == 5 * n - 2, 'Kostochka-Yancey equality arithmetic')
    return len(seen)


def main():
    require(len(sys.argv) == 5, __doc__.strip())
    edges, adj = graph(sys.argv[1])
    faces = planar(adj, sys.argv[3])
    counts = cycles(adj)
    leaves, joins = ore(edges, len(adj), sys.argv[2])
    deletions = critical(edges, len(adj), sys.argv[4])
    print(json.dumps({'status': 'PASS', 'vertices': len(adj), 'edges': len(edges),
                      'faces': faces, 'cycles_3_through_10': counts,
                      'K4_leaves': leaves, 'Ore_joins': joins,
                      'isomorphism': 'checked', 'non_3_colorable': 'Ore induction',
                      'deletion_colorings': deletions, 'four_critical': True,
                      'KY_equality': '3*136=5*82-2'}, sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, TypeError, IndexError, OSError, RecursionError) as exc:
        print(f'REJECT: {exc}', file=sys.stderr)
        sys.exit(1)
