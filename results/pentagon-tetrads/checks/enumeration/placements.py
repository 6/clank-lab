"""Corner placements on a tetrad map.

For a map (from maps.py), a placement says, for every tile sector at a map
vertex, whether the tile has a corner there (C) or is straight (S), and for
every map edge how many bends it has. A bend on an edge between two tiles is a
corner of both; a bend on an edge between a tile and a non-tile face is a
corner of that tile. Every tile has exactly n corners.

A labelled placement adds, for each tile, the dihedral identification of its
corners (ccw order) with the corners 0..n-1 of the prototile P.
"""
import itertools
import json
import sys

from maps import describe


class MapData:
    def __init__(self, m):
        self.m = m
        self.edges = [tuple(e) for e in m['edges']]
        self.rot = {int(v): ds for v, ds in m['rot'].items()}
        self.succ, self.faces, self.tail, self.face_of = describe(m)
        self.ntiles = 4
        self.tile_sectors = [d for d in range(2 * len(self.edges)) if self.tail[d] < 4]
        # map vertex -> list of sector darts
        self.vertex_sectors = [list(f) for f in self.faces]
        self.vertex_interior = [all(self.tail[d] < 4 for d in f) for f in self.faces]

    def tile_cycle(self, t):
        return self.rot[t]

    def edge_is_tt(self, e):
        a, b = self.edges[e]
        return a < 4 and b < 4


def placements(md, n):
    """Yield (cs, bends): cs maps tile-sector dart -> 'C'/'S'; bends[e] >= 0."""
    sectors = md.tile_sectors
    E = len(md.edges)
    # at most one S per map vertex
    vert_of = {d: md.face_of[d] for d in sectors}
    for cs_bits in itertools.product('CS', repeat=len(sectors)):
        cs = dict(zip(sectors, cs_bits))
        cnt = {}
        bad = False
        for d, c in cs.items():
            if c == 'S':
                v = vert_of[d]
                cnt[v] = cnt.get(v, 0) + 1
                if cnt[v] > 1:
                    bad = True
                    break
        if bad:
            continue
        # corners at vertices per tile
        base = [0] * 4
        for d, c in cs.items():
            if c == 'C':
                base[md.tail[d]] += 1
        if any(b > n for b in base):
            continue
        # distribute bends: tile t needs n - base[t] bend-corners
        need = [n - b for b in base]
        yield from _bends(md, cs, need, 0, [0] * E)


def _bends(md, cs, need, e, cur):
    E = len(md.edges)
    if e == E:
        if all(x == 0 for x in need):
            yield dict(cs), list(cur)
        return
    a, b = md.edges[e]
    tiles = [x for x in (a, b) if x < 4]
    mx = min(need[x] for x in tiles)
    for k in range(mx + 1):
        for x in tiles:
            need[x] -= k
        cur[e] = k
        yield from _bends(md, cs, need, e + 1, cur)
        for x in tiles:
            need[x] += k
    cur[e] = 0


def corner_sequence(md, cs, bends, t):
    """Corners of tile t in ccw order, as position keys, and for each corner
    the boundary edge segment following it (list of map edges up to next
    corner) is not needed here."""
    seq = []
    for d in md.tile_cycle(t):
        if cs[d] == 'C':
            seq.append(('V', d))
        e = d // 2
        b = bends[e]
        js = range(b) if d % 2 == 0 else range(b - 1, -1, -1)
        for j in js:
            seq.append(('B', e, j))
    return seq


DIHEDRAL5 = None


def dihedral(n):
    """Labelings: list of (proper, shift); corner k -> (shift + k) % n if
    proper else (shift - k) % n."""
    return [(True, s) for s in range(n)] + [(False, s) for s in range(n)]


def label_of(lab, k, n):
    proper, s = lab
    return (s + k) % n if proper else (s - k) % n


if __name__ == '__main__':
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    total = 0
    for line in open(sys.argv[1]):
        md = MapData(json.loads(line))
        c = sum(1 for _ in placements(md, n))
        print(len(md.edges), c)
        total += c
    print('total', total)
