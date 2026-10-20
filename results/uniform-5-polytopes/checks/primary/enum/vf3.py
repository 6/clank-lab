"""4-D control, stage 2: assemble vertex figures (polyhedra) from edge
neighbourhoods of equal radius.

The vertex figure VF of a uniform polychoron with circumradius R lies on a
2-sphere of radius r = sqrt(1 - 1/(4 R^2)); its faces are the vertex figures
of the cells (cyclic polygons with sides 2 cos(pi/q) in the cell's vertex
configuration, circumradius r_C = sqrt(1 - 1/(4 R_C^2))); the faces around
each VF vertex form an edge neighbourhood of the radius-R class.  The search
places faces geometrically across open edges, keeps the polyhedron convex,
and checks every closed vertex against the neighbourhood list.
"""
import math, sys, json, itertools
import numpy as np

TOL = 1e-7


def chord(q):
    return 2 * math.cos(math.pi / q)


def small_r(Rbig):
    return math.sqrt(1 - 1 / (4 * Rbig * Rbig))


class Face:
    def __init__(self, cell, labels, verts, normal, d):
        self.cell, self.labels, self.verts, self.normal, self.d = cell, labels, verts, normal, d


def polygon_in_plane(labels, rc):
    """Vertices (2-D) of the cyclic polygon with sides chord(labels[i]) between vertex i and i+1."""
    th = [2 * math.asin(min(1.0, chord(q) / (2 * rc))) for q in labels]
    if abs(sum(th) - 2 * math.pi) > 1e-6:
        return None
    pts, t = [], 0.0
    for x in th:
        pts.append((rc * math.cos(t), rc * math.sin(t)))
        t += x
    return np.array(pts)


def place_face(x, y, labels, rc, r):
    """Candidate 3-D placements of a polygon whose first edge (vertex0 -> vertex1, label labels[0])
    is the chord x -> y, lying on the sphere of radius r.  Returns list of (points, normal, d)."""
    d2 = r * r - rc * rc
    if d2 < -1e-12:
        return []
    d = math.sqrt(max(0.0, d2))
    P2 = polygon_in_plane(labels, rc)
    if P2 is None:
        return []
    m = (x + y) / 2
    u = (y - x) / np.linalg.norm(y - x)
    w = m / np.linalg.norm(m)            # direction from centre to chord midpoint
    w = w - np.dot(w, u) * u
    w /= np.linalg.norm(w)
    v = np.cross(u, w)
    out = []
    # plane normal n = cos(phi) w + sin(phi) v (unit, orthogonal to u); n . x = d
    mm = np.linalg.norm(m)
    if mm < d - 1e-9:
        return []
    c = d / mm
    phis = [math.acos(max(-1, min(1, c)))]
    phis = [phis[0], -phis[0]]
    for phi in phis:
        n = math.cos(phi) * w + math.sin(phi) * v
        centre = d * n
        # in-plane frame with P2[0] -> x, P2[1] -> y
        a2, b2 = P2[0], P2[1]
        e1 = (y - x) / np.linalg.norm(y - x)
        e2 = np.cross(n, e1)
        # map 2-D polygon: choose rotation so that a2->x, b2->y (both orientations)
        for flip in (1, -1):
            Q = P2.copy()
            Q[:, 1] *= flip
            a, b = Q[0], Q[1]
            ed = (b - a) / np.linalg.norm(b - a)
            ep = np.array([-ed[1], ed[0]])
            pts = [x + (q - a) @ ed * e1 + (q - a) @ ep * e2 for q in Q]
            pts = np.array(pts)
            if np.max(np.abs(np.linalg.norm(pts, axis=1) - r)) > 1e-6:
                continue
            if abs(np.linalg.norm(pts[1] - y)) > 1e-6:
                continue
            out.append((pts, n, d))
    return out


class VF:
    def __init__(self, r):
        self.r = r
        self.pos = []
        self.faces = []
        self.edges = {}   # frozenset(i,j) -> list of (face index, label)

    def vid(self, p):
        for i, q in enumerate(self.pos):
            if np.linalg.norm(p - q) < 1e-6:
                return i
        self.pos.append(p)
        return len(self.pos) - 1

    def copy(self):
        o = VF(self.r)
        o.pos = list(self.pos)
        o.faces = list(self.faces)
        o.edges = {k: list(v) for k, v in self.edges.items()}
        return o


def try_add(vf, cell, labels, pts, n, d):
    # convexity: all existing vertices inside new plane, new vertices inside existing planes
    for p in vf.pos:
        if np.dot(n, p) > d + 1e-7:
            return None
    for f in vf.faces:
        for p in pts:
            if np.dot(f.normal, p) > f.d + 1e-7:
                return None
        if np.linalg.norm(f.normal - n) < 1e-7:
            return None
    o = vf.copy()
    ids = [o.vid(p) for p in pts]
    if len(set(ids)) != len(ids):
        return None
    k = len(ids)
    fi = len(o.faces)
    for i in range(k):
        e = frozenset((ids[i], ids[(i + 1) % k]))
        lst = o.edges.setdefault(e, [])
        if lst and lst[0][1] != labels[i]:
            return None
        lst.append((fi, labels[i]))
        if len(lst) > 2:
            return None
    o.faces.append(Face(cell, labels, ids, n, d))
    return o


def vertex_fan(vf, v):
    """Closed fan around vertex v as a cyclic list of (cell, label of the edge after it); None if open."""
    inc = [fi for fi, f in enumerate(vf.faces) if v in f.verts]
    if len(inc) < 3:
        return None
    nb = {}  # face -> its two neighbour vertices at v
    for fi in inc:
        f = vf.faces[fi]
        k = len(f.verts)
        i = f.verts.index(v)
        nb[fi] = (f.verts[(i - 1) % k], f.verts[(i + 1) % k])
    for fi in inc:
        for w in nb[fi]:
            if len(vf.edges[frozenset((v, w))]) != 2:
                return None
    # walk: start at inc[0], leave through its 'next' neighbour
    seq = []
    cur = inc[0]
    w = nb[cur][1]
    for _ in range(len(inc)):
        e = frozenset((v, w))
        seq.append((vf.faces[cur].cell, vf.edges[e][0][1]))
        other = [fi for fi, _ in vf.edges[e] if fi != cur]
        if not other:
            return None
        cur = other[0]
        a, b = nb[cur]
        w = b if a == w else a
    if cur != inc[0]:
        return None
    if len(set(c for c in [x for x in inc])) != len(inc):
        return None
    return seq


def canon_cycle(seq):
    k = len(seq)
    cands = []
    for rr in range(k):
        rot = seq[rr:] + seq[:rr]
        cands.append(tuple(rot))
        # reversed: labels shift (label after cell i becomes label before)
        rev_cells = [c for c, _ in reversed(rot)]
        rev_labs = [l for _, l in reversed(rot)]
        rev_labs = rev_labs[1:] + rev_labs[:1]
        cands.append(tuple(zip(rev_cells, rev_labs)))
    return min(cands)


def chain_at(vf, v):
    """Faces around v as one chain: returns (faces_in_order, start_open_neighbour, end_open_neighbour)
    walking from one open edge to the other; ('closed', seq) if closed; None if several chains."""
    inc = [fi for fi, f in enumerate(vf.faces) if v in f.verts]
    nb = {}
    for fi in inc:
        f = vf.faces[fi]
        k = len(f.verts)
        i = f.verts.index(v)
        nb[fi] = (f.verts[(i - 1) % k], f.verts[(i + 1) % k])
    open_ws = [w for fi in inc for w in nb[fi] if len(vf.edges[frozenset((v, w))]) == 1]
    if not open_ws:
        return ('closed', vertex_fan(vf, v))
    if len(open_ws) != 2:
        return None
    # walk from open_ws[0]
    w = open_ws[0]
    cur = [fi for fi, _ in vf.edges[frozenset((v, w))]][0]
    order = []
    labels = []  # label of edge after each face (walking direction)
    for _ in range(len(inc)):
        order.append(cur)
        a, b = nb[cur]
        w2 = b if a == w else a
        lab = vf.edges[frozenset((v, w2))][0][1]
        labels.append(lab)
        others = [fi for fi, _ in vf.edges[frozenset((v, w2))] if fi != cur]
        if not others:
            break
        cur = others[0]
        w = w2
    if len(order) != len(inc):
        return None
    start_w = open_ws[0]
    end_w = w2
    first_label = vf.edges[frozenset((v, start_w))][0][1]
    return (order, start_w, end_w, first_label, labels)


def type_variants(t):
    """All rotations and reflections of a neighbourhood cycle [(cell, label_after)]."""
    k = len(t)
    out = []
    for rr in range(k):
        rot = t[rr:] + t[:rr]
        out.append(rot)
        rev_cells = [c for c, _ in reversed(rot)]
        rev_labs = [l for _, l in reversed(rot)]
        rev_labs = rev_labs[1:] + rev_labs[:1]
        out.append(list(zip(rev_cells, rev_labs)))
    return out


def corner_labelings(conf, lin, lout):
    """Label sequences (starting with the edge into the corner) of the polygon conf with a corner (lin, lout)."""
    m = len(conf)
    res = set()
    for s in range(m):
        fw = [conf[(s + t) % m] for t in range(m)]
        bw = [conf[(s - t) % m] for t in range(m)]
        for seq in (fw, bw):
            if seq[0] == lin and seq[1] == lout:
                res.add(tuple(seq))
    return [list(x) for x in res]


def enumerate_vfs(Rclass, cfg, cellR, Rbig, limit=200000):
    r = small_r(Rbig)
    types = []
    for nb in Rclass:
        t = list(zip(nb['cells'], nb['faces']))
        c = canon_cycle(t)
        if c not in [canon_cycle(x) for x in types]:
            types.append(list(c))
    types.sort()
    results = {}
    nodes = [0]
    for j, seed in enumerate(types):
        allowed_types = types[j:]
        allowed = set(canon_cycle(t) for t in allowed_types)
        variants = [vt for t in allowed_types for vt in type_variants(t)]

        def ok_closed(vf):
            for v in range(len(vf.pos)):
                fan = vertex_fan(vf, v)
                if fan is not None and canon_cycle(fan) not in allowed:
                    return False
            return True

        def complete_vertex(vf, v, chain):
            order, start_w, end_w, first_label, labels = chain
            k0 = len(order)
            cells_have = [vf.faces[fi].cell for fi in order]
            # walking direction: start_w -(first_label)- face0 -(labels[0])- face1 ... -(labels[-1])- end_w
            outs = []
            for vt in variants:
                K = len(vt)
                if K <= k0:
                    continue
                # vt[i] = (cell_i, label after cell_i); label before cell_0 = vt[-1][1]
                if [c for c, _ in vt[:k0]] != cells_have:
                    continue
                if vt[-1][1] != first_label or [l for _, l in vt[:k0]] != labels:
                    continue
                outs.append(vt[k0:])
            return outs

        def place_rest(vf, v, w, lin, rest):
            if not rest:
                return [vf]
            cell, lout = rest[0]
            res = []
            x, y = vf.pos[w], vf.pos[v]
            rc = small_r(cellR[cell])
            for labs in corner_labelings(cfg[cell], lin, lout):
                for pts, n, d in place_face(x, y, labs, rc, r):
                    o = try_add(vf, cell, labs, pts, n, d)
                    if o is None:
                        continue
                    # the new face's vertex after v
                    fi = len(o.faces) - 1
                    fv = o.faces[fi].verts
                    k = len(fv)
                    iv = fv.index(o.vid(y))
                    w2 = fv[(iv + 1) % k]
                    res.extend(place_rest(o, v, w2, lout, rest[1:]))
            return res

        def search(vf):
            nodes[0] += 1
            if nodes[0] > limit:
                return
            # choose an open vertex with a single chain, max faces
            best = None
            for v in range(len(vf.pos)):
                ch = chain_at(vf, v)
                if ch is None or ch[0] == 'closed':
                    continue
                if best is None or len(ch[0]) > len(best[1][0]):
                    best = (v, ch)
            if best is None:
                if all(chain_at(vf, v) is not None and chain_at(vf, v)[0] == 'closed' for v in range(len(vf.pos))):
                    if ok_closed(vf):
                        sig = (tuple(sorted(f.cell for f in vf.faces)),
                               tuple(sorted(canon_cycle(vertex_fan(vf, v)) for v in range(len(vf.pos)))))
                        if sig not in results:
                            results[sig] = dict(count=0, pos=[p.tolist() for p in vf.pos],
                                                faces=[(f.cell, list(f.labels), list(f.verts)) for f in vf.faces])
                        results[sig]['count'] += 1
                return
            v, ch = best
            order, start_w, end_w, first_label, labels = ch
            for rest in complete_vertex(vf, v, ch):
                for o in place_rest(vf, v, end_w, labels[-1], rest):
                    # closing edge (v, start_w) must now have 2 faces
                    if len(o.edges.get(frozenset((v, start_w)), [])) != 2:
                        continue
                    if ok_closed(o):
                        search(o)

        # seed: first face of the seed type, placed, then complete its vertex 0
        cell0, lab0 = seed[0]
        labin = seed[-1][1]
        conf = cfg[cell0]
        rc = small_r(cellR[cell0])
        for labs in corner_labelings(conf, labin, lab0)[:1]:
            P2 = polygon_in_plane(labs, rc)
            if P2 is None:
                continue
            d = math.sqrt(max(0.0, r * r - rc * rc))
            pts = np.array([[p[0], p[1], d] for p in P2])
            vf = try_add(VF(r), cell0, labs, pts, np.array([0, 0, 1.0]), d)
            # complete the corner vertex (polygon vertex 1 has edges labs[0] in, labs[1] out)
            v = vf.vid(pts[1])
            ch = chain_at(vf, v)
            order, start_w, end_w, first_label, labels = ch
            for o in place_rest(vf, v, end_w, labels[-1], seed[1:]) if [c for c, _ in seed][:1] == [vf.faces[order[0]].cell] and first_label == labin else []:
                if len(o.edges.get(frozenset((v, start_w)), [])) == 2 and ok_closed(o):
                    search(o)
    return results, nodes[0]
