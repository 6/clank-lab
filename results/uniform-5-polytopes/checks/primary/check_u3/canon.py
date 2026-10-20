"""Exact combinatorial encodings of a star of v0.

A star (complete state) is: facets (type K, map m from the template's base
neighbours to point ids, defined up to the stabiliser of the base) and the
cells through v0, each in exactly two facets.  Geometry is a function of
this structure and of R: from one placed facet (a frame), every facet across
a cell is determined (search.place), and every vertex is a facet vertex.

encode(state, root, frame) labels the points by a breadth-first walk from the
root facet whose points are numbered by `frame` (point id -> template vertex
index of the frame); each new facet's representative map is the one, over the
stabiliser, with the least label tuple (unique, because an isometry fixing the
base, the centre and three labelled cell-polygon points is the identity).
Two stars with equal encodings from frames that a congruence g maps onto each
other are equal after g; equal encodings are an exact proof of equality.
"""

BIG = 10 ** 9


def facet_adjacency(s):
    adj = []
    for fi, F in enumerate(s.facets):
        lst = []
        for ci, cell in enumerate(F.T.cells):
            key = frozenset(F.m[t] for t in cell['poly'])
            other = [g for g, _ in s.cells[key] if g != fi]
            lst.append((key, other[0] if other else None))
        adj.append(lst)
    return adj


def encode(s, root, frame, adj=None):
    if adj is None:
        adj = facet_adjacency(s)
    labels = {}
    for pid in sorted(frame, key=lambda p: frame[p]):
        labels[pid] = len(labels)
    F = s.facets[root]
    out = [(F.type, tuple(sorted(labels[p] for p in F.m.values())))]
    visited = {root}
    queue = [root]
    while queue:
        g = queue.pop(0)
        nb = sorted((tuple(sorted(labels[p] for p in key)), h) for key, h in adj[g])
        for _, h in nb:
            if h is None or h in visited:
                continue
            visited.add(h)
            H = s.facets[h]
            T = H.T
            best = None
            for perm in T.stab_perm:
                tup = tuple(labels.get(H.m[int(perm[j])], BIG) for j in T.nb)
                if best is None or tup < best[0]:
                    best = (tup, perm)
            perm = best[1]
            for j in T.nb:
                p = H.m[int(perm[j])]
                if p not in labels:
                    labels[p] = len(labels)
            out.append((H.type, tuple(labels[H.m[int(perm[j])]] for j in T.nb)))
            queue.append(h)
    if len(visited) != len(s.facets):
        raise ValueError("star not connected")
    return tuple(out)


def frame_stab(F, perm):
    """frame of facet F composed with a stabiliser element: point m[j] gets
    template index perm[j]."""
    return {F.m[j]: int(perm[j]) for j in F.T.nb}


def canonical(s):
    adj = facet_adjacency(s)
    K0 = min(F.type for F in s.facets)
    best = None
    for fi, F in enumerate(s.facets):
        if F.type != K0:
            continue
        for perm in F.T.stab_perm:
            e = encode(s, fi, frame_stab(F, perm), adj)
            if best is None or e < best:
                best = e
    return best
