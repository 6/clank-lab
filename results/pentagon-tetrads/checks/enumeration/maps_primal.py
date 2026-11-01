"""Independent check of the map classification (holeless case), written
without maps.py: enumerate the PRIMAL boundary maps M directly.

M is a connected plane multigraph (loops allowed) with V vertices of degree
>= 3 and 5 faces (4 tiles, 1 outer). Euler: E = V + 3 and sum(deg - 2) = 6,
so V <= 6. For every multigraph and rotation system with 5 faces, every
choice of the outer face is tested against:
  * no edge has the same face on both sides;
  * each tile face boundary visits each vertex at most once (simple cycle);
  * every two tiles share an edge.
Survivors are reduced by an isomorphism code of the face-coloured map
(mirror images identified). Output: the number of classes and, for
comparison with maps.py, the dual of each class as edges + rotation in the
same JSON format.
"""
import itertools
import json
import sys


def multigraphs(V, E):
    """Multisets of E edges on vertices 0..V-1 (loops allowed), all degrees
    >= 3, as sorted tuples of pairs. Vertices are interchangeable, so we
    require nonincreasing degrees as a weak symmetry filter (not a canonical
    form: duplicates are removed later by the map code)."""
    pairs = [(i, j) for i in range(V) for j in range(i, V)]
    out = []

    def rec(k, start, deg, cur):
        if k == E:
            if all(d >= 3 for d in deg):
                out.append(tuple(cur))
            return
        # remaining edges must be able to lift all degrees to 3
        need = sum(max(0, 3 - d) for d in deg)
        if need > 2 * (E - k):
            return
        for idx in range(start, len(pairs)):
            i, j = pairs[idx]
            deg[i] += 1
            deg[j] += 1
            cur.append((i, j))
            rec(k + 1, idx, deg, cur)
            cur.pop()
            deg[i] -= 1
            deg[j] -= 1
    rec(0, 0, [0] * V, [])
    return out


def maps_of(V, edges):
    # darts: 2e (i -> j), 2e+1 (j -> i); a loop gives two darts at the same vertex
    nd = 2 * len(edges)
    at = [[] for _ in range(V)]
    for e, (i, j) in enumerate(edges):
        at[i].append(2 * e)
        at[j].append(2 * e + 1)
    choices = []
    for v in range(V):
        ds = at[v]
        choices.append([[ds[0]] + list(pm) for pm in itertools.permutations(ds[1:])])
    for rot in itertools.product(*choices):
        nxt = [0] * nd
        for ds in rot:
            for k, d in enumerate(ds):
                nxt[d] = ds[(k + 1) % len(ds)]
        # face permutation: after traversing dart d (tail -> head), continue with
        # the dart after the reverse of d in the rotation at the head
        face = [-1] * nd
        faces = []
        for d0 in range(nd):
            if face[d0] >= 0:
                continue
            f = []
            d = d0
            while face[d] < 0:
                face[d] = len(faces)
                f.append(d)
                d = nxt[d ^ 1]
            faces.append(f)
        if len(faces) != 5:
            continue
        yield rot, nxt, face, faces


def tail(edges, d):
    i, j = edges[d // 2]
    return i if d % 2 == 0 else j


def valid(edges, face, faces, outer):
    # face on the two sides of edge e: face[2e] and face[2e+1]
    for e in range(len(edges)):
        if face[2 * e] == face[2 * e + 1]:
            return False
    tiles = [f for f in range(5) if f != outer]
    for f in tiles:
        vs = [tail(edges, d) for d in faces[f]]
        if len(vs) != len(set(vs)):
            return False
    adj = set()
    for e in range(len(edges)):
        a, b = face[2 * e], face[2 * e + 1]
        adj.add((min(a, b), max(a, b)))
    for a, b in itertools.combinations(tiles, 2):
        if (a, b) not in adj:
            return False
    return True


def code(nd, nxt, face, outer):
    """Isomorphism code: BFS from each root dart, both orientations; darts
    coloured by whether the face on their left is the outer face."""
    prv = [0] * nd
    for d in range(nd):
        prv[nxt[d]] = d
    best = None
    for rot in (nxt, prv):
        # in the mirror, the face on the left of d becomes the face on the left of d^1
        for r in range(nd):
            num = {r: 0}
            order = [r]
            i = 0
            while i < len(order):
                d = order[i]
                for x in (d ^ 1, rot[d]):
                    if x not in num:
                        num[x] = len(order)
                        order.append(x)
                i += 1
            if len(order) != nd:
                return None
            if rot is nxt:
                col = [face[d] == outer for d in order]
            else:
                col = [face[d ^ 1] == outer for d in order]
            c = tuple((num[d ^ 1], num[rot[d]], col[k]) for k, d in enumerate(order))
            if best is None or c < best:
                best = c
    return best


def main():
    classes = {}
    stats = {}
    for V in range(1, 7):
        E = V + 3
        mg = multigraphs(V, E)
        cnt = 0
        for edges in mg:
            for rot, nxt, face, faces in maps_of(V, edges):
                for outer in range(5):
                    if not valid(edges, face, faces, outer):
                        continue
                    c = code(2 * len(edges), nxt, face, outer)
                    if c is not None and c not in classes:
                        classes[c] = (V, edges, [list(x) for x in rot], outer)
                        cnt += 1
        stats[V] = (len(mg), cnt)
    print(json.dumps({'stats': stats, 'classes': len(classes)}))
    for c, (V, edges, rot, outer) in classes.items():
        degs = [0] * V
        for i, j in edges:
            degs[i] += 1
            degs[j] += 1
        print(json.dumps({'V': V, 'degrees': sorted(degs), 'edges': edges, 'rot': rot, 'outer': outer}))


if __name__ == '__main__':
    main()
