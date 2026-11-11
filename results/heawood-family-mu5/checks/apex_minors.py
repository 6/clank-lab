"""List the minor-minimal non-2-apex minors of G.

A 2-apex graph (planar after deleting two vertices) has mu <= 5, since
mu(G) <= mu(G - v) + 1 and planar graphs have mu <= 3.  So an obstruction to
mu <= 5 that is a minor of G (a minor-minimal graph with mu >= 6) is one of
the non-2-apex minors of G; all of them are listed (minors are reached one
edge deletion or contraction at a time, and a minor of a 2-apex graph is
2-apex, so the search never needs to pass through a 2-apex graph), and the
minimal ones are marked.  A 3-apex graph has mu <= 6 by the same argument.  Usage: apex_minors.py G6FILE
"""
import itertools, json, os, sys
import networkx as nx
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from minor_exclusion import ops, strip

def two_apex(G):
    return any(nx.check_planarity(G.subgraph(set(G) - {a, b}))[0]
               for a, b in itertools.combinations(G, 2))

def three_apex(G):
    return any(nx.check_planarity(G.subgraph(set(G) - set(c)))[0]
               for c in itertools.combinations(G, 3))

def minimal_non_2apex(G):
    seen = {}; out = []; frontier = [strip(G)]
    while frontier:
        nxt = []
        for H in frontier:
            key = nx.weisfeiler_lehman_graph_hash(H, iterations=4)
            if any(nx.is_isomorphic(H, X) for X in seen.get(key, [])): continue
            seen.setdefault(key, []).append(H)
            children = [strip(K) for K in ops(H)]
            bad = [K for K in children if not two_apex(K)]
            if not bad: out.append(H)
            nxt.extend(bad)
        frontier = nxt
    return out, [H for L in seen.values() for H in L]

if __name__ == "__main__":
    for line in open(sys.argv[1]):
        name, g6 = line.split()
        G = nx.from_graph6_bytes(g6.encode())
        if two_apex(G):
            print(json.dumps({"graph": name, "two_apex": True})); continue
        res, alln = minimal_non_2apex(G)
        print(json.dumps({"graph": name, "two_apex": False, "three_apex": three_apex(G), "non_2apex_minors": [
            {"n": H.number_of_nodes(), "m": H.number_of_edges(),
             "graph6": nx.to_graph6_bytes(H, header=False).decode().strip()} for H in alln],
            "minimal_non_2apex_minors": [
            {"n": H.number_of_nodes(), "m": H.number_of_edges(),
             "graph6": nx.to_graph6_bytes(H, header=False).decode().strip(),
             "is_G": nx.is_isomorphic(H, strip(G))} for H in res]}), flush=True)
