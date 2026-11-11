"""Heawood family: closure of K7 and K_{3,3,1,1} under Delta-Y and Y-Delta.

Y-Delta is applied only when the three new edges are absent (simple graphs).
Prints the family size by vertex count; the literature count is 78.
"""
import itertools, json, sys
import networkx as nx

def canon(G):
    return nx.weisfeiler_lehman_graph_hash(G, iterations=4)

def add(fam, G):
    h = canon(G)
    for H in fam.setdefault(h, []):
        if nx.is_isomorphic(G, H):
            return False
    fam[h].append(G)
    return True

def moves(G):
    nxt = max(G.nodes) + 1
    for a, b, c in (t for t in itertools.combinations(G.nodes, 3)
                    if G.has_edge(t[0], t[1]) and G.has_edge(t[1], t[2]) and G.has_edge(t[0], t[2])):
        H = G.copy(); H.remove_edges_from([(a, b), (b, c), (a, c)])
        H.add_edges_from([(nxt, a), (nxt, b), (nxt, c)])
        yield nx.convert_node_labels_to_integers(H)
    for v in G.nodes:
        if G.degree(v) == 3:
            a, b, c = G.neighbors(v)
            if not (G.has_edge(a, b) or G.has_edge(b, c) or G.has_edge(a, c)):
                H = G.copy(); H.remove_node(v); H.add_edges_from([(a, b), (b, c), (a, c)])
                yield nx.convert_node_labels_to_integers(H)

def family():
    K3311 = nx.complete_multipartite_graph(3, 3, 1, 1)
    fam = {}
    todo = [nx.complete_graph(7), nx.convert_node_labels_to_integers(K3311)]
    for G in todo: add(fam, G)
    while todo:
        G = todo.pop()
        for H in moves(G):
            if add(fam, H): todo.append(H)
    return [G for L in fam.values() for G in L]

if __name__ == "__main__":
    F = family()
    from collections import Counter
    print(len(F), sorted(Counter(G.number_of_nodes() for G in F).items()),
          set(G.number_of_edges() for G in F))
    json.dump([sorted(G.edges()) for G in F], open(sys.argv[1], "w")) if len(sys.argv) > 1 else None
