#!/usr/bin/env python3
"""Checker B: Heawood-family minors via branch-set model search; plus 2-apex minor census (item 4).

Usage: checker_b.py family            generate the family, print counts
       checker_b.py time1 G6          time one model search (largest-budget member) against graph G6
       checker_b.py minors            controls + G1/G2 decision + cross-check
       checker_b.py apex              item 4: non-2-apex minors of G1, G2
Written independently of check_cert.py, from the certificate format description only.
"""
import sys, itertools, time
import networkx as nx

G1_G6 = "J?bFF`wNA{?"
G2_G6 = "K?BD@jguAsBo"


def parse_graph6(s):
    d = [ord(c) - 63 for c in s]
    n = d[0]
    assert n <= 62 and len(d) == 1 + (n * (n - 1) // 2 + 5) // 6
    bits = [(x >> k) & 1 for x in d[1:] for k in range(5, -1, -1)]
    G = nx.Graph(); G.add_nodes_from(range(n))
    p = 0
    for j in range(1, n):
        for i in range(j):
            if bits[p]:
                G.add_edge(i, j)
            p += 1
    assert not any(bits[p:])
    return G


# ---------------------------------------------------------------- isomorphism classes
def inv(G):
    return (G.number_of_nodes(), G.number_of_edges(), tuple(sorted(d for _, d in G.degree())),
            nx.weisfeiler_lehman_graph_hash(G, iterations=4))


class IsoSet:
    def __init__(self):
        self.buckets = {}; self.items = []

    def find(self, G):
        for H in self.buckets.get(inv(G), []):
            if nx.is_isomorphic(G, H):
                return H
        return None

    def add(self, G):
        if self.find(G) is not None:
            return False
        G = nx.convert_node_labels_to_integers(G)
        self.buckets.setdefault(inv(G), []).append(G); self.items.append(G)
        return True


# ---------------------------------------------------------------- Heawood family
def delta_y(G, tri):
    a, b, c = tri
    H = G.copy(); H.remove_edges_from([(a, b), (b, c), (a, c)])
    v = max(H.nodes) + 1
    H.add_edges_from([(v, a), (v, b), (v, c)])
    return H


def y_delta(G, v):
    a, b, c = list(G[v])
    H = G.copy(); H.remove_node(v); H.add_edges_from([(a, b), (b, c), (a, c)])
    return H


def moves(G):
    for a, b, c in itertools.combinations(sorted(G.nodes), 3):
        if G.has_edge(a, b) and G.has_edge(b, c) and G.has_edge(a, c):
            yield delta_y(G, (a, b, c))
    for v in G.nodes:
        if G.degree(v) == 3:
            a, b, c = list(G[v])
            if not (G.has_edge(a, b) or G.has_edge(b, c) or G.has_edge(a, c)):
                yield y_delta(G, v)


def heawood_family():
    K7 = nx.complete_graph(7)
    K3311 = nx.complete_multipartite_graph(3, 3, 1, 1)
    fam = IsoSet(); origin = []
    for name, seed in (("K7", K7), ("K3311", K3311)):
        queue = [seed]
        if fam.add(seed): origin.append(name)
        while queue:
            G = queue.pop()
            for H in moves(G):
                if fam.add(H):
                    origin.append(name); queue.append(H)
    return fam.items, origin


# ---------------------------------------------------------------- branch-set model search
def connected_subsets(G, maxsize):
    """all connected vertex subsets of size <= maxsize (frozensets)"""
    out = set()
    frontier = {frozenset([v]) for v in G.nodes}
    out |= frontier
    for _ in range(maxsize - 1):
        nxt = set()
        for S in frontier:
            for v in S:
                for w in G[v]:
                    if w not in S:
                        nxt.add(S | {w})
        nxt -= out
        out |= nxt; frontier = nxt
    return out


def find_model(G, H, stats=None):
    """Return dict h -> branch set (frozenset of G vertices) witnessing H <= G as a minor, or None.
    Search: H vertices in a connectivity order; each gets a connected, unused G-vertex set adjacent to the
    branch sets of its already placed H-neighbours. Pruning: |V(H)|<=|V(G)|, |E(H)|<=|E(G)|, total excess
    sum(|B|-1) <= |E(G)|-|E(H)| and <= |V(G)|-|V(H)|, degree (edges leaving B >= deg_H), room for the rest."""
    nG, mG, nH, mH = G.number_of_nodes(), G.number_of_edges(), H.number_of_nodes(), H.number_of_edges()
    if nH > nG or mH > mG:
        return None
    budget = min(mG - mH, nG - nH)
    adjG = {v: set(G[v]) for v in G.nodes}
    subs = []
    for S in connected_subsets(G, budget + 1):
        N = set().union(*(adjG[v] for v in S)) - S
        out = sum(1 for v in S for w in adjG[v] if w not in S)
        subs.append((S, frozenset(N), out))
    subs.sort(key=lambda x: (len(x[0]), sorted(x[0])))
    # ordering of H: max degree first, then most placed neighbours
    order = []; rest = set(H.nodes)
    while rest:
        v = max(rest, key=lambda x: (sum(1 for w in H[x] if w in order), H.degree(x), -x))
        order.append(v); rest.remove(v)
    hpos = {v: k for k, v in enumerate(order)}
    placed = {}; nbset = {}
    count = [0]

    def rec(k, used, excess):
        count[0] += 1
        if k == nH:
            return True
        v = order[k]
        dv = H.degree(v)
        prev = [w for w in H[v] if hpos[w] < k]
        later = any(hpos[w] > k for w in H[v])
        remaining_after = nH - k - 1
        for S, N, out in subs:
            ex = len(S) - 1
            if excess + ex > budget or out < dv:
                continue
            if S & used:
                continue
            if nG - len(used) - len(S) < remaining_after:
                continue
            if any(not (N & placed[w]) for w in prev):
                continue
            if later and not (N - used):
                continue
            placed[v] = S; nbset[v] = N
            if rec(k + 1, used | S, excess + ex):
                return True
            del placed[v]; del nbset[v]
        return False

    ok = rec(0, frozenset(), 0)
    if stats is not None:
        stats["nodes"] = stats.get("nodes", 0) + count[0]
    return dict(placed) if ok else None


def verify_model(G, H, model):
    """independent verification of a branch-set model (own BFS, no shared code with the search)"""
    allv = [x for B in model.values() for x in B]
    if set(model) != set(H.nodes): return "model does not cover V(H)"
    if len(allv) != len(set(allv)): return "branch sets not disjoint"
    if not set(allv) <= set(G.nodes): return "vertex not in G"
    for h, B in model.items():
        B = set(B)
        if not B: return "empty branch set"
        start = next(iter(B)); seen = {start}; st = [start]
        while st:
            x = st.pop()
            for y in G.neighbors(x):
                if y in B and y not in seen:
                    seen.add(y); st.append(y)
        if seen != B: return "branch set of %s not connected" % h
    for a, b in H.edges:
        if not any(G.has_edge(x, y) for x in model[a] for y in model[b]):
            return "H-edge %s-%s not realised" % (a, b)
    return None


# ---------------------------------------------------------------- cross-check: minors with >= k edges
def contract(G, u, v):
    H = nx.contracted_nodes(G, u, v, self_loops=False)
    return nx.Graph(H)


def strip_isolated(G):
    H = G.copy(); H.remove_nodes_from([v for v in G if G.degree(v) == 0]); return H


def minors_with_at_least(G, k):
    """all minors (no isolated vertices) with >= k edges, by edge deletions/contractions"""
    seen = IsoSet(); seen.add(strip_isolated(G)); stack = [strip_isolated(G)]
    while stack:
        X = stack.pop()
        for e in list(X.edges):
            for Y in (nx.restricted_view(X, [], [e]).copy(), contract(X, *e)):
                Y = strip_isolated(nx.Graph(Y))
                if Y.number_of_edges() >= k and seen.add(Y):
                    stack.append(seen.items[-1])
    return seen.items


# ---------------------------------------------------------------- 2-apex
def is_planar(G):
    return nx.check_planarity(G)[0]


def is_2apex(G):
    V = list(G.nodes)
    if len(V) <= 2: return True
    for a, b in itertools.combinations(V, 2):
        H = G.copy(); H.remove_nodes_from([a, b])
        if is_planar(H):
            return True
    return False


def non2apex_minors(G):
    """2-apex is minor-closed, so non-2-apex minors form a down-closed-from-the-top set reachable by single steps
    through non-2-apex graphs: explore from G, keeping only non-2-apex children."""
    G = strip_isolated(G)
    res = IsoSet(); assert not is_2apex(G); res.add(G); stack = [res.items[-1]]
    tested = 0
    while stack:
        X = stack.pop()
        for e in list(X.edges):
            for Y in (nx.Graph(nx.restricted_view(X, [], [e])), contract(X, *e)):
                Y = strip_isolated(Y)
                if res.find(Y) is not None: continue
                tested += 1
                if not is_2apex(Y):
                    res.add(Y); stack.append(res.items[-1])
    return res.items, tested


def g6(G):
    return nx.to_graph6_bytes(nx.convert_node_labels_to_integers(G), header=False).decode().strip()


# ---------------------------------------------------------------- drivers
def cmd_family():
    fam, origin = heawood_family()
    from collections import Counter
    print("family size", len(fam), "by edges", dict(Counter(G.number_of_edges() for G in fam)),
          "by origin", dict(Counter(origin)))
    print("by (n,m):", sorted(Counter((G.number_of_nodes(), G.number_of_edges()) for G in fam).items()))
    hw = nx.heawood_graph()
    print("nx.heawood_graph() in family:", any(nx.is_isomorphic(hw, G) for G in fam))
    return fam


def cmd_time1(g):
    G = parse_graph6(g)
    fam, _ = heawood_family()
    cands = [H for H in fam if H.number_of_nodes() <= G.number_of_nodes()]
    H = max(cands, key=lambda H: (G.number_of_edges() - H.number_of_edges(), H.number_of_nodes()))
    st = {}; t = time.process_time(); m = find_model(G, H, st)
    print("one search: H n=%d m=%d -> %s, nodes=%d, cpu=%.3fs" % (H.number_of_nodes(), H.number_of_edges(),
          "FOUND" if m else "none", st["nodes"], time.process_time() - t))


def search_all(name, G, fam, verbose=True):
    found = []; st = {}
    t = time.process_time()
    for idx, H in enumerate(fam):
        m = find_model(G, H, st)
        if m is not None:
            err = verify_model(G, H, m)
            found.append(idx)
            if verbose:
                print("  %s: member #%d (n=%d,m=%d, %s) IS a minor; branch sets %s; independent verification: %s"
                      % (name, idx, H.number_of_nodes(), H.number_of_edges(), g6(H),
                         {h: sorted(B) for h, B in sorted(m.items())}, "OK" if err is None else "FAILED " + err))
            assert err is None
    print("  %s (n=%d,m=%d): %d family members are minors; search nodes=%d cpu=%.2fs"
          % (name, G.number_of_nodes(), G.number_of_edges(), len(found), st.get("nodes", 0), time.process_time() - t))
    return found


def cmd_minors():
    fam, origin = heawood_family()
    assert len(fam) == 78
    # positive controls
    print("Positive controls:")
    c1 = nx.complete_graph(7); c1.add_edge(0, 7)
    f = search_all("K7 + pendant edge", c1, fam, verbose=True); assert f
    hw = nx.heawood_graph()
    c2 = hw.copy()
    nxt = 14
    for (a, b) in [(0, 1), (2, 3), (5, 6)]:
        assert c2.has_edge(a, b)
        c2.remove_edge(a, b); c2.add_edges_from([(a, nxt), (nxt, b)]); nxt += 1
    extra = (0, 7) if not c2.has_edge(0, 7) else None
    c2.add_edge(*extra)
    print("  control 2: Heawood graph, edges 0-1,2-3,5-6 subdivided (17 vertices) + extra edge %s; n=%d m=%d"
          % (extra, c2.number_of_nodes(), c2.number_of_edges()))
    f = search_all("subdivided Heawood + edge", c2, fam, verbose=True); assert f
    # vertex split of a K3,3,1,1-family member: K3,3,1,1 itself, split one of the degree-7 vertices
    K = nx.complete_multipartite_graph(3, 3, 1, 1)
    v = 6; nb = sorted(K[v])
    c3 = K.copy(); c3.remove_node(v); w1, w2 = 100, 101
    c3.add_edge(w1, w2)
    for x in nb[:4]: c3.add_edge(w1, x)
    for x in nb[4:]: c3.add_edge(w2, x)
    print("  control 3: K3,3,1,1 with vertex 6 (deg 7) split into adjacent 100 (nbrs %s) and 101 (nbrs %s)" % (nb[:4], nb[4:]))
    f = search_all("K3311 vertex split", c3, fam, verbose=True); assert f
    # and a split of a 14-vertex-ish member of the K7 family (random member with a degree>=4 vertex)
    H = next(H for H in fam if H.number_of_edges() == 21 and H.number_of_nodes() == 10 and max(d for _, d in H.degree()) >= 4)
    v = max(H.nodes, key=H.degree); nb = sorted(H[v])
    c4 = H.copy(); c4.remove_node(v); c4.add_edge("a", "b")
    for x in nb[:2]: c4.add_edge("a", x)
    for x in nb[2:]: c4.add_edge("b", x)
    c4 = nx.convert_node_labels_to_integers(c4)
    print("  control 4: K7-family member %s (n=10) with vertex %d (deg %d) split" % (g6(H), v, len(nb)))
    f = search_all("K7-family member split", c4, fam, verbose=True); assert f
    # negative control: K7 minus an edge, and the targets
    print("Negative control:")
    c5 = nx.complete_graph(7); c5.remove_edge(0, 1)
    f = search_all("K7 - e", c5, fam); assert not f
    print("Targets:")
    res = {}
    for name, g in (("G1", G1_G6), ("G2", G2_G6)):
        G = parse_graph6(g)
        res[name] = search_all(name, G, fam)
    # cross-check by the other algorithm (enumerate minors with >= 21 edges, compare by isomorphism)
    print("Cross-check (deletion/contraction enumeration of minors with >= 21 edges):")
    famset = IsoSet()
    for H in fam: famset.add(H)
    for name, g in (("G1", G1_G6), ("G2", G2_G6)):
        G = parse_graph6(g)
        ms = minors_with_at_least(G, 21)
        hits = [M for M in ms if famset.find(M) is not None]
        print("  %s: %d minors with >=21 edges up to iso, %d isomorphic to a family member" % (name, len(ms), len(hits)))
        assert (len(hits) == 0) == (len(res[name]) == 0)
    for name in res:
        print("RESULT %s: %s" % (name, "NO Heawood-family minor" if not res[name] else "HAS Heawood-family minor(s)"))


def cmd_apex():
    K7 = nx.complete_graph(7); K7e = K7.copy(); K7e.remove_edge(0, 1)
    print("sanity: 2-apex(K7)=%s (expect False), 2-apex(K7-e)=%s (expect True), 2-apex(K3,3,1,1)=%s (expect False)"
          % (is_2apex(K7), is_2apex(K7e), is_2apex(nx.complete_multipartite_graph(3, 3, 1, 1))))
    G1 = parse_graph6(G1_G6); G2 = parse_graph6(G2_G6)
    R = G1.copy(); R.remove_edge(1, 10)
    print("G1 - {1,10}: degrees %s, g6 %s, 2-apex: %s" % (sorted(set(d for _, d in R.degree())), g6(R), is_2apex(R)))
    for name, G in (("G1", G1), ("G2", G2)):
        items, tested = non2apex_minors(G)
        print("%s: non-2-apex minors (up to iso, isolated vertices dropped): %d   [%d candidate graphs tested]" % (name, len(items), tested))
        for X in items:
            print("   n=%d m=%d degs=%s g6=%s  iso(G1)=%s iso(G2)=%s iso(G1-{1,10})=%s" % (
                X.number_of_nodes(), X.number_of_edges(), sorted(d for _, d in X.degree()), g6(X),
                nx.is_isomorphic(X, G1), nx.is_isomorphic(X, G2), nx.is_isomorphic(X, R)))
    # 2-apex-ness of one-step minors also confirms minimality picture
    print("G1 iso G2:", nx.is_isomorphic(G1, G2))


if __name__ == "__main__":
    c = sys.argv[1]
    if c == "family": cmd_family()
    elif c == "time1": cmd_time1(sys.argv[2])
    elif c == "minors": cmd_minors()
    elif c == "apex": cmd_apex()
