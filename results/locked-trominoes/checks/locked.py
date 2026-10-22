#!/usr/bin/env python3
"""Exact certificate checker: no solver, encoder, or placement templates."""
from functools import lru_cache
from itertools import combinations
import json
import sys


def require(test, message):
    if not test:
        raise ValueError(message)


def connected3(points):
    # A simple graph on three vertices is connected iff it has >= 2 edges.
    return len(points) == 3 and sum(abs(a[0]-b[0])+abs(a[1]-b[1]) == 1
                                  for a,b in combinations(points,2)) >= 2


@lru_cache(None)
def split_count(points):
    count = 0
    for a,b in combinations(range(1,6),2):
        first = (points[0],points[a],points[b])
        second = tuple(points[i] for i in range(1,6) if i not in (a,b))
        count += connected3(first) and connected3(second)
    return count


def check_pair(a,b):
    points = a+b
    require(len(set(points)) == 6,'pair overlap')
    r0,c0=min(r for r,c in points),min(c for r,c in points)
    key=tuple(sorted((r-r0,c-c0) for r,c in points))
    require(split_count(key) == 1,'alternative recombination')


def parse_block(b):
    require(type(b) is dict and set(b)=={'height','width','tiles'},'block schema')
    h,w=b['height'],b['width']
    require(type(h) is int and type(w) is int and h>0 and w>0,'dimensions')
    require(type(b['tiles']) is list,'tiles schema')
    occupied=set()
    tiles=[]
    for raw in b['tiles']:
        require(type(raw) is list and len(raw)==3,'tile size')
        require(all(type(p) is list and len(p)==2 and
                    all(type(x) is int for x in p) for p in raw),'coordinate schema')
        t=tuple(map(tuple,raw))
        require(len(set(t))==3 and connected3(t),'not a connected triple')
        require(all(0<=r<h and 0<=c<w for r,c in t),'out of bounds')
        require(not occupied.intersection(t),'overlap')
        occupied.update(t)
        tiles.append(t)
    require(len(occupied)==h*w,'not a partition')
    return h,w,tiles


def check_certificate(cert):
    require(type(cert) is dict and set(cert)=={'blocks','vertical','horizontal'},'schema')
    require(type(cert['blocks']) is dict and cert['blocks'],'blocks schema')
    parsed={}
    pairs=0
    for name,b in cert['blocks'].items():
        require(type(name) is str and name,'block name')
        h,w,tiles=parse_block(b)
        for a,b in combinations(tiles,2):
            check_pair(a,b)
            pairs+=1
        if h>=6 and h%3==0 and w>=4:
            straight={frozenset((r+k,c) for k in range(3))
                      for r in range(0,h,3) for c in range(w)}
            require({frozenset(t) for t in tiles} != straight,'no other tiling shown')
        parsed[name]=(h,w,tiles)
    seams=0
    for axis in ('vertical','horizontal'):
        require(type(cert[axis]) is list,'seam schema')
        seen=set()
        for s in cert[axis]:
            require(type(s) is list and len(s)==2 and
                    all(type(x) is str and x in parsed for x in s),'bad seam')
            require(tuple(s) not in seen,'duplicate seam')
            seen.add(tuple(s))
            h,w,aa=parsed[s[0]]
            hb,wb,bb=parsed[s[1]]
            require(w==wb if axis=='vertical' else h==hb,'seam dimensions')
            dr,dc=(h,0) if axis=='vertical' else (0,w)
            shifted=[tuple((r+dr,c+dc) for r,c in t) for t in bb]
            for a in aa:
                for b in shifted:
                    check_pair(a,b)
                    pairs+=1
            seams+=1
    return {'accepted':True,'blocks':len(parsed),'seams':seams,'pairs':pairs}


def load(path):
    def unique(pairs):
        out={}
        for k,v in pairs:
            require(k not in out,'duplicate JSON key')
            out[k]=v
        return out
    with open(path) as f:
        return json.load(f,object_pairs_hook=unique)


if __name__=='__main__':
    try:
        print(json.dumps(check_certificate(load(sys.argv[1])),sort_keys=True))
    except (ValueError,OSError) as exc:
        print(str(exc),file=sys.stderr)
        sys.exit(1)
