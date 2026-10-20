"""Facet types of a listed known 5-polytope Q, from its construction
(referee gap U2: Q may enter a class's elimination only when every facet
type of Q is in the input library; otherwise stage 2 has not listed Q's
vertex figure and Q is reported as a remark).

* `A5abcde`, `B5abcde`, `D5abcde` (Wythoff): the facets are the orbits of x
  under the parabolic subgroups W_{S - k}, for every node k such that every
  connected component of the diagram without k has a ringed node (otherwise
  the orbit lies in a lower-dimensional flat); the facet is the product of
  the Wythoff polytopes of the components (a ringed single node is a
  segment, a ringed pair with branch m an m-gon or, both ringed, a
  2m-gon, three nodes a polyhedron, four nodes a 4-polytope).  A D4
  component (centre d, leaves l1, l2, l3) is a B4 polytope: two leaves have
  the same ring y, the third has x, and the polytope is B4 (x, d, y, 0)
  (the B4 orbit with node 3 unringed is the W(D4)-orbit, D4 with leaves
  a0, a2, r3(a2) and centre a1; see tcert.WythoffModel).
* `prism-K`: K and the prisms over the cells of K.
* `{p}xX`: the prism over X and the duoprisms {p} x {q} over the faces of X.

Names are those of the facet library: the prism over the cube is B40001
(tesseract), over P_n duoprism-4-n, over A_n antiprism-prism-n; duoprisms
with p <= q, the 4-4 one is B40001; A4 rings up to reversal (the least of the
two strings).
"""
import geom
import tcert
EDGES5 = {'A5': {(0, 1): 3, (1, 2): 3, (2, 3): 3, (3, 4): 3}, 'B5': {(0, 1): 3, (1, 2): 3, (2, 3): 3, (3, 4): 4}, 'D5': {(0, 1): 3, (1, 2): 3, (2, 3): 3, (2, 4): 3}}

def duo(p, q):
    p, q = sorted((p, q))
    if (p, q) == (4, 4):
        return 'B40001'
    return 'duoprism-%d-%d' % (p, q)

def prism_of(label):
    if label == 'cube':
        return 'B40001'
    if label[0] == 'P' and label[1:].isdigit():
        return duo(4, int(label[1:]))
    if label[0] == 'A' and label[1:].isdigit():
        return 'antiprism-prism-%d' % int(label[1:])
    return 'pr-' + label

def face_sizes(label):
    """sizes of the faces of the polyhedron through a vertex"""
    if label[0] == 'P' and label[1:].isdigit():
        return {4, int(label[1:])}
    if label[0] == 'A' and label[1:].isdigit():
        return {3, int(label[1:])}
    M = tcert.model3(label)
    if isinstance(M, tcert.SnubModel):
        return {3} | {len(S) for S in M.planar}
    sizes = set()
    for i in range(3):
        for j in range(i + 1, 3):
            k = len(tcert.orbit([0], [M.gens[i], M.gens[j]]))
            if k >= 3:
                sizes.add(k)
    return sizes

def _components(edges, nodes):
    nodes = set(nodes)
    comps = []
    while nodes:
        st = [nodes.pop()]
        comp = set(st)
        while st:
            u = st.pop()
            for a, b in edges:
                for x, y in ((a, b), (b, a)):
                    if x == u and y in nodes:
                        nodes.discard(y)
                        comp.add(y)
                        st.append(y)
        comps.append(comp)
    return comps

def _chain(edges, comp, start=None):
    """the nodes of a path component in order (from `start` if given)"""
    adj = {u: [v for a, b in edges for x, v in ((a, b), (b, a)) if x == u and v in comp] for u in comp}
    ends = [u for u in comp if len(adj[u]) <= 1]
    if start is None:
        start = min(ends)
    order = [start]
    while len(order) < len(comp):
        nxt = [v for v in adj[order[-1]] if v not in order]
        if not len(nxt) == 1:
            raise AssertionError()
        order.append(nxt[0])
    return order

def _part(diag, comp, rings):
    """(dimension, name) of the Wythoff polytope of one component"""
    E = {e: m for e, m in EDGES5[diag].items() if e[0] in comp and e[1] in comp}
    r = {u: rings[u] for u in comp}
    if len(comp) == 1:
        return (1, 'seg')
    if len(comp) == 2:
        m, = E.values()
        both = all(r.values())
        return (2, ('poly', 2 * m if both else m))
    degs = {u: sum((1 for e in E if u in e)) for u in comp}
    if max(degs.values()) == 3:
        c = next((u for u in comp if degs[u] == 3))
        leaves = sorted((u for u in comp if u != c))
        lr = [r[u] for u in leaves]
        y = 1 if lr.count(1) >= 2 else 0
        x = lr[0] + lr[1] + lr[2] - 2 * y
        return (4, 'B4%d%d%d0' % (x, r[c], y))
    four = [e for e, m in E.items() if m == 4]
    if four:
        end4 = [u for u in comp if degs[u] == 1 and any((u in e for e in four))]
        ends = [u for u in comp if degs[u] == 1 and u not in end4]
        order = _chain(E, comp, ends[0])
        diag_c = 'B%d' % len(comp)
    else:
        order = _chain(E, comp)
        diag_c = 'A%d' % len(comp)
    rr = tuple((r[u] for u in order))
    if len(comp) == 3:
        return (3, ('poly3', geom.label3(diag_c, rr)))
    s = ''.join(map(str, rr))
    if diag_c == 'A4':
        s = min(s, s[::-1])
    return (4, diag_c + s)

def _product_name(parts):
    dims = sorted((d for d, _ in parts))
    if dims == [4]:
        return parts[0][1]
    if dims == [1, 3]:
        X = next((n for d, n in parts if d == 3))
        return prism_of(X[1])
    if dims == [2, 2]:
        return duo(parts[0][1][1], parts[1][1][1])
    if dims == [1, 1, 2]:
        P = next((n for d, n in parts if d == 2))
        return duo(4, P[1])
    raise ValueError(parts)

def facet_types(name, template=None):
    """the set of facet type names of the listed polytope `name`;
    template(K) gives the certified template of a 4-polytope K (for the cell
    labels of K in prism-K)"""
    if name[:2] in ('A5', 'B5', 'D5') and len(name) == 7:
        diag = name[:2]
        rings = tuple((int(c) for c in name[2:]))
        out = set()
        for k in range(5):
            nodes = [u for u in range(5) if u != k]
            E = {e: m for e, m in EDGES5[diag].items() if k not in e}
            comps = _components(E, nodes)
            if not all((any((rings[u] for u in c)) for c in comps)):
                continue
            out.add(_product_name([_part(diag, c, rings) for c in comps]))
        return out
    if name.startswith('prism-'):
        K = name[6:]
        if template is None:
            return {K}
        return {K} | {prism_of(c['label']) for c in template(K).cells}
    if name.startswith('{'):
        p = int(name[1:name.index('}')])
        X = name[name.index('x') + 1:]
        return {prism_of(X)} | {duo(p, q) for q in face_sizes(X)}
    raise KeyError(name)
