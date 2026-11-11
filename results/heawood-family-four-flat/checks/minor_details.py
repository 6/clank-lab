#!/usr/bin/env python3
"""GPT-6 Astra, release revision: direct minor comparisons and 2-apex witnesses."""
import itertools
import json
import sys

import networkx as nx


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def main():
    doc = json.load(open(sys.argv[1]))
    h = nx.Graph()
    h.add_nodes_from(range(doc['vertices']))
    h.add_edges_from(doc['edges'])
    family = [nx.Graph(edges) for edges in json.load(open(sys.argv[2]))]
    require(h.number_of_nodes() == 11 and h.number_of_edges() == 22,
            'wrong H size')
    require(all(d == 4 for _, d in h.degree()), 'H must be 4-regular')
    edge_set = {tuple(sorted(e)) for e in h.edges()}
    circulant = {tuple(sorted((v, (v + step) % 11)))
                 for v in range(11) for step in (4, 5)}
    require(edge_set == circulant, 'H circulant labeling mismatch')
    relabeled = {tuple(sorted((3*a % 11, 3*b % 11))) for a, b in edge_set}
    require(relabeled == {tuple(sorted((v, (v + step) % 11)))
                          for v in range(11) for step in (1, 4)},
            'C11(1,4) identification mismatch')
    require(len(family) == 78 and
            sum(g.number_of_edges() == 21 for g in family) == 20 and
            sum(g.number_of_edges() == 22 for g in family) == 58,
            'wrong family edge distribution')

    def excludes(g):
        return not any(g.number_of_nodes() == f.number_of_nodes() and
                       g.number_of_edges() == f.number_of_edges() and
                       nx.is_isomorphic(g, f) for f in family)

    require(excludes(h), 'H itself is a family member')
    edges = sorted(tuple(sorted(e)) for e in h.edges())
    remaining, orbits = set(edges), []
    automorphisms = list(nx.algorithms.isomorphism.GraphMatcher(h, h).isomorphisms_iter())
    while remaining:
        a, b = min(remaining)
        orbit = {tuple(sorted((f[a], f[b]))) for f in automorphisms}
        require(orbit <= remaining, 'overlapping edge orbits')
        remaining -= orbit
        orbits.append(sorted(orbit))
    require(sorted(map(len, orbits)) == [11, 11], 'unexpected edge orbits')
    records = []
    for a, b in edges:
        deleted = h.copy()
        deleted.remove_edge(a, b)
        contracted = nx.contracted_nodes(h, a, b, self_loops=False)
        for operation, g in [('delete', deleted), ('contract', contracted)]:
            require(excludes(g), 'single-edge minor is a family member')
            apex = None
            for pair in itertools.combinations(sorted(g), 2):
                planar = g.copy()
                planar.remove_nodes_from(pair)
                if nx.check_planarity(planar)[0]:
                    apex = pair
                    break
            require(apex is not None, 'single-edge minor is not 2-apex')
            records.append({'edge': [a, b], 'operation': operation,
                            'apex_vertices': apex})
    print(json.dumps({'accepted': True, 'family_edges': {'21': 20, '22': 58},
                      'h_and_single_edge_minors_compared': 45,
                      'edge_orbits': orbits, 'proper_minor_apex_witnesses': records},
                     sort_keys=True))


if __name__ == '__main__':
    main()
