#!/usr/bin/env python3
"""Exact rectilinear cell decomposition; standard library only.

This checks a concrete finite diagram, not a general surface theorem.
The written bridge must identify it with the paper and apply Penner.
"""
import argparse
from collections import deque
from fractions import Fraction as Q
import itertools
import json


# Optimization would disable the explicit assertion-based validation below.
if not __debug__:
    raise SystemExit(2)


def inside(r, p):
    x0, x1, y0, y1 = r
    x, y = p
    return x0 < x < x1 and y0 < y < y1


def on(r, p):
    x0, x1, y0, y1 = r
    x, y = p
    return ((x in (x0, x1) and y0 <= y <= y1) or
            (y in (y0, y1) and x0 <= x <= x1))


def crossings(r, s):
    points = []
    for a, b in ((r, s), (s, r)):
        for x in a[:2]:
            for y in b[2:]:
                if b[0] < x < b[1] and a[2] < y < a[3]:
                    points.append((x, y))
    # Any intersection on a corner or common segment would invalidate the
    # transverse arrangement semantics; rule them out independently.
    for a, b in ((r, s), (s, r)):
        for p in itertools.product(a[:2], a[2:]):
            assert not on(b, p), 'nontransverse contact'
    return sorted(points)


def check(data):
    assert data['schema'] == 1
    rs = data['rectangles']
    assert set(rs) == {'a', 'd', 'c', 'Cprime', 'C'}
    pts = {int(k): tuple(v) for k, v in data['punctures'].items()}
    assert set(pts) == set(range(1, 6)) and len(set(pts.values())) == 5
    expected_parts = {'a': [1, 2], 'd': [2, 3], 'c': [3, 4],
                      'Cprime': [1, 2, 3], 'C': [2, 3, 4]}
    assert data['partitions'] == expected_parts
    for name, r in rs.items():
        assert len(r) == 4 and all(type(x) is int for x in r)
        assert r[0] < r[1] and r[2] < r[3]
        assert not any(on(r, p) for p in pts.values())
        part = sorted(n for n, p in pts.items() if inside(r, p))
        assert part == expected_parts[name] and 2 <= len(part) <= 3
    # Partitions distinguish these particular curves; this does NOT assert
    # that partitions classify arbitrary punctured-sphere isotopy classes.
    parts = [frozenset(v) for v in expected_parts.values()]
    assert len(set(parts)) == 5
    cycle = ['a', 'd', 'c', 'Cprime', 'C']
    for i, u in enumerate(cycle):
        for j in range(i + 1, 5):
            v = cycle[j]
            assert len(crossings(rs[u], rs[v])) == (2 if (j-i) in (1, 4) else 0)

    names = ('a', 'd', 'c')
    rr = [rs[n] for n in names]
    xs = sorted({-4, 22, *(x for r in rr for x in r[:2])})
    ys = sorted({-10, 10, *(y for r in rr for y in r[2:])})
    # Each grid cell is an exact open rectangle, with no curve in its
    # interior. Crossing a grid edge is allowed exactly when it is uncut.
    cells = set(itertools.product(range(len(xs)-1), range(len(ys)-1)))
    comps = []
    while cells:
        start = min(cells)
        cells.remove(start)
        comp = {start}
        queue = deque([start])
        while queue:
            i, j = queue.popleft()
            candidates = [((i-1,j),(xs[i], Q(ys[j]+ys[j+1],2))),
                          ((i+1,j),(xs[i+1],Q(ys[j]+ys[j+1],2))),
                          ((i,j-1),(Q(xs[i]+xs[i+1],2),ys[j])),
                          ((i,j+1),(Q(xs[i]+xs[i+1],2),ys[j+1]))]
            for cell, midpoint in candidates:
                if cell in cells and not any(on(r, midpoint) for r in rr):
                    cells.remove(cell)
                    comp.add(cell)
                    queue.append(cell)
        comps.append(comp)
    all_cross = set(crossings(rr[0],rr[1])+crossings(rr[1],rr[2]))
    assert len(all_cross) == 4
    observed = []
    for comp in comps:
        edges = set()
        vertices = set()
        for i, j in comp:
            v = [(xs[i],ys[j]),(xs[i+1],ys[j]),
                 (xs[i+1],ys[j+1]),(xs[i],ys[j+1])]
            vertices.update(v)
            for u,w in zip(v,v[1:]+v[:1]):
                e = tuple(sorted((u,w)))
                if e in edges:
                    edges.remove(e)
                else:
                    edges.add(e)
        boundary_vertices = set(itertools.chain.from_iterable(edges))
        # Disk or annulus via a connected finite planar grid subcomplex.
        # Check boundary is a disjoint union of simple cycles as well as chi.
        adj = {v:set() for v in boundary_vertices}
        for u,w in edges:
            adj[u].add(w); adj[w].add(u)
        assert all(len(ns)==2 for ns in adj.values())
        unseen = set(adj)
        loops = 0
        while unseen:
            stack = [unseen.pop()]; loops += 1
            while stack:
                for n in adj[stack.pop()]:
                    if n in unseen:
                        unseen.remove(n); stack.append(n)
        # Recover all cell edges, including interior edges, for Euler chi.
        total_edges = (4*len(comp)+len(edges))//2
        chi = len(vertices)-total_edges+len(comp)
        outer = any(x in (-4,22) or y in (-10,10) for x,y in boundary_vertices)
        assert (loops,chi) == ((2,0) if outer else (1,1))
        # The external boundary is capped by the sphere's unmarked disk.
        i,j = next(iter(comp))
        sample = (Q(xs[i]+xs[i+1],2),Q(ys[j]+ys[j+1],2))
        sig = sorted(n for n in names if inside(rs[n],sample))
        holes = sorted(n for n,p in pts.items() if any(
            xs[i] < p[0] < xs[i+1] and ys[j] < p[1] < ys[j+1] for i,j in comp))
        corners = len(all_cross & boundary_vertices)
        assert corners >= (2 if holes else 3)
        observed.append({'inside':sig,'punctures':holes,'corners':corners})
    key = lambda d: tuple(d['inside'])
    assert sorted(observed,key=key) == sorted(data['penner_faces'],key=key)
    assert len(observed)==6 and sorted(len(f['punctures']) for f in observed)==[0,1,1,1,1,1]
    assert data['pants']==[[1,2,'a'],[3,4,'c'],['a','c',5]]
    # The round disjoint disks a,c give two inside pants and their outside
    # sphere-with-three-boundaries. The displayed partitions are checked.
    return {'verdict':'ACCEPT','crossings':4,'edges':8,'faces':6,
            'unpunctured_disks':1,'punctured_disks':5,'pants':3}


if __name__ == '__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('certificate')
    args=ap.parse_args()
    try:
        result=check(json.load(open(args.certificate)))
    except (AssertionError,KeyError,ValueError,TypeError) as e:
        print(json.dumps({'verdict':'REJECT','reason':str(e)}))
        raise SystemExit(1)
    print(json.dumps(result,sort_keys=True))
