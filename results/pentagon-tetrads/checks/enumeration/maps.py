"""Enumerate the combinatorial types of tetrad boundary maps.

The union of the four tile boundaries is a connected plane graph G. Its faces
are the four tile interiors and the components of the complement of the union
(the outer face and any holes). Suppressing points where G is locally a
segment or a bend leaves a plane multigraph M whose vertices have degree >= 3.
We enumerate M through its dual D: a plane multigraph whose vertices are the
faces of M (tiles 0..3, then the outer face 4, then holes 5..), whose edges
are the edges of M and whose faces are the vertices of M.

Conditions on D (see NOTE.md, "Map lemma"):
  * no loops; every edge has a tile at one end at least (an edge of M lies on
    some tile boundary, and that tile is on one side of it);
  * non-tile vertices (outer, holes) are pairwise non-adjacent;
  * every pair of tiles is adjacent (the tetrad condition);
  * plane: V - E + F = 2 for the rotation system;
  * every face of D has length >= 3 (vertices of M have degree >= 3);
  * a tile appears at most once on each face of D (a tile boundary is a simple
    closed curve, so it passes each vertex of M at most once);
  * each non-tile vertex has degree >= 1 (holeless: the outer face exists).

Output: one representative per isomorphism class (tiles unlabelled, mirror
images identified), as JSON lines.
"""
import itertools
import json
import sys
from math import factorial


def faces_of(rot, ndarts):
    """rot: dict vertex -> list of outgoing darts in ccw order.
    Returns (succ, faces) with faces as lists of darts (orbits of phi)."""
    succ = [None] * ndarts
    for v, ds in rot.items():
        for k, d in enumerate(ds):
            succ[d] = ds[(k + 1) % len(ds)]
    seen = [False] * ndarts
    faces = []
    for d0 in range(ndarts):
        if seen[d0]:
            continue
        f = []
        d = d0
        while not seen[d]:
            seen[d] = True
            f.append(d)
            d = succ[d ^ 1]
        faces.append(f)
    return succ, faces


def canonical(succ, tail, color, ndarts):
    """Canonical code of a connected map with coloured vertices, minimised
    over root darts and both orientations (mirror images identified)."""
    pred = [None] * ndarts
    for d in range(ndarts):
        pred[succ[d]] = d
    best = None
    for orient in (succ, pred):
        for root in range(ndarts):
            num = {root: 0}
            order = [root]
            i = 0
            while i < len(order):
                d = order[i]
                for nd in (d ^ 1, orient[d]):
                    if nd not in num:
                        num[nd] = len(order)
                        order.append(nd)
                i += 1
            if len(order) != ndarts:
                return None  # disconnected
            code = tuple((num[d ^ 1], num[orient[d]], color[tail[d]]) for d in order)
            if best is None or code < best:
                best = code
    return best


def enumerate_maps(nholes=0, max_edges=9, min_edges=1):
    ntiles = 4
    nonT = list(range(4, 4 + 1 + nholes))
    V = 4 + len(nonT)
    tile_pairs = list(itertools.combinations(range(4), 2))
    nt_pairs = [(t, o) for o in nonT for t in range(4)]
    color = ['T'] * 4 + ['O'] + ['H'] * nholes
    found = {}
    stats = {'multigraphs': 0, 'rotations': 0, 'planar': 0}
    for E in range(min_edges, max_edges + 1):
        # multiplicities: tile pairs >= 1, tile-nontile >= 0, sum = E
        k = len(tile_pairs) + len(nt_pairs)
        extra = E - len(tile_pairs)
        if extra < 0:
            continue
        for comp in compositions(extra, k):
            mult = [1 + comp[i] for i in range(len(tile_pairs))] + list(comp[len(tile_pairs):])
            pairs = tile_pairs + nt_pairs
            # each non-tile vertex needs degree >= 2 (a face of M with one edge
            # would be bounded by a loop; allowed for O? see below) -> use >= 1
            degs = [0] * V
            edges = []
            for (a, b), m in zip(pairs, mult):
                for _ in range(m):
                    edges.append((a, b))
                    degs[a] += 1
                    degs[b] += 1
            if any(degs[o] < 1 for o in nonT):
                continue
            stats['multigraphs'] += 1
            ndarts = 2 * len(edges)
            tail = [None] * ndarts
            out = {v: [] for v in range(V)}
            for e, (a, b) in enumerate(edges):
                tail[2 * e] = a
                tail[2 * e + 1] = b
                out[a].append(2 * e)
                out[b].append(2 * e + 1)
            # rotation systems: fix first dart at each vertex
            perms = []
            for v in range(V):
                ds = out[v]
                if len(ds) <= 1:
                    perms.append([ds])
                else:
                    perms.append([[ds[0]] + list(p) for p in itertools.permutations(ds[1:])])
            for choice in itertools.product(*perms):
                stats['rotations'] += 1
                rot = {v: choice[v] for v in range(V)}
                succ, faces = faces_of(rot, ndarts)
                if V - len(edges) + len(faces) != 2:
                    continue
                stats['planar'] += 1
                ok = True
                for f in faces:
                    if len(f) < 3:
                        ok = False
                        break
                    ts = [tail[d] for d in f if tail[d] < 4]
                    if len(ts) != len(set(ts)):
                        ok = False
                        break
                if not ok:
                    continue
                code = canonical(succ, tail, color, ndarts)
                if code is None or code in found:
                    continue
                found[code] = {
                    'edges': edges,
                    'rot': {str(v): rot[v] for v in range(V)},
                    'nholes': nholes,
                }
    return found, stats


def compositions(n, k):
    """All k-tuples of non-negative integers summing to n."""
    if k == 1:
        yield (n,)
        return
    for i in range(n + 1):
        for rest in compositions(n - i, k - 1):
            yield (i,) + rest


def describe(m):
    """Derived data: tile boundary cycles and map vertices."""
    edges = m['edges']
    rot = {int(v): ds for v, ds in m['rot'].items()}
    ndarts = 2 * len(edges)
    succ, faces = faces_of(rot, ndarts)
    tail = [edges[d // 2][d % 2] for d in range(ndarts)]
    face_of = {}
    for i, f in enumerate(faces):
        for d in f:
            face_of[d] = i
    return succ, faces, tail, face_of


if __name__ == '__main__':
    nholes = int(sys.argv[1]) if len(sys.argv) > 1 else 0
    max_edges = int(sys.argv[2]) if len(sys.argv) > 2 else 9
    found, stats = enumerate_maps(nholes, max_edges)
    for code in sorted(found):
        print(json.dumps(found[code], sort_keys=True))
    print(json.dumps({'stats': stats, 'classes': len(found)}), file=sys.stderr)
