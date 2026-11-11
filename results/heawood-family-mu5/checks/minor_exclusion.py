"""Exhaustive check that a graph G with m edges has no minor in a list of graphs
that all have at least m - r edges, for small r.

Every minor H of G with |E(H)| >= |E(G)| - r arises from G by at most r edge
deletions or contractions (each removes at least one edge; contraction also
merges parallel edges) followed by deleting isolated vertices (H has none).
So we enumerate all such operation sequences of length <= r (r = |E(G)| - min
|E(H)|), canonicalise each result (isolated vertices dropped) and compare with
every target up to isomorphism.  Usage: minor_exclusion.py G.g6-line-file TARGETS.json
TARGETS.json: list of edge lists (the 78 Heawood-family graphs).
"""
import json, sys
import networkx as nx

def ops(G):
    for e in list(G.edges()):
        H = G.copy(); H.remove_edge(*e); yield H
        H = nx.contracted_nodes(G, e[0], e[1], self_loops=False); yield H

def strip(G):
    H = G.copy(); H.remove_nodes_from([v for v in list(H) if H.degree(v) == 0])
    return nx.convert_node_labels_to_integers(H)

def minors_down_to(G, mmin):
    seen = {}; frontier = [strip(G)]; out = []
    while frontier:
        nxt = []
        for H in frontier:
            key = nx.weisfeiler_lehman_graph_hash(H, iterations=4)
            if any(nx.is_isomorphic(H, X) for X in seen.get(key, [])): continue
            seen.setdefault(key, []).append(H); out.append(H)
            if H.number_of_edges() > mmin:
                nxt.extend(strip(K) for K in ops(H) if K.number_of_edges() >= mmin)
        frontier = nxt
    return out

if __name__ == "__main__":
    targets = [nx.Graph(e) for e in json.load(open(sys.argv[2]))]
    mmin = min(T.number_of_edges() for T in targets)
    for line in open(sys.argv[1]):
        name, g6 = line.split()
        G = nx.from_graph6_bytes(g6.encode())
        Ms = minors_down_to(G, mmin)
        hits = [i for i, T in enumerate(targets) for H in Ms
                if H.number_of_edges() == T.number_of_edges() and H.number_of_nodes() == T.number_of_nodes()
                and nx.is_isomorphic(H, T)]
        print(json.dumps({"graph": name, "n": G.number_of_nodes(), "m": G.number_of_edges(),
                          "minors_enumerated": len(Ms), "target_minors_found": sorted(set(hits))}), flush=True)
