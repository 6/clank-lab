#!/usr/bin/env python3
"""Untrusted witness producer, rebuilt from connected-triple definition.

Requires python-sat; verification never imports this module.
"""
import argparse
from functools import lru_cache
from itertools import combinations, product
import json
from pathlib import Path
import time
from pysat.solvers import Solver


def neighbours(p):
    r, c = p
    return ((r-1,c),(r+1,c),(r,c-1),(r,c+1))


def connected(s):
    s = set(s)
    seen = {next(iter(s))}
    while True:
        more = {q for p in seen for q in neighbours(p)} & s
        if more <= seen:
            return seen == s
        seen |= more


def placements(h, w):
    cells = set(product(range(h), range(w)))
    pairs = {frozenset((p,q)) for p in cells for q in neighbours(p) if q in cells}
    return sorted({tuple(sorted(s | {q})) for s in pairs
                   for p in s for q in neighbours(p) if q in cells and q not in s})


@lru_cache(None)
def splits(u):
    whole = set(u)
    return tuple(frozenset((frozenset(a), frozenset(whole-set(a))))
                 for a in combinations(u,3) if u[0] in a and connected(a)
                 and connected(whole-set(a)))


def incompatible(a,b):
    if set(a) & set(b):
        return False  # exact cover handles overlap
    if not any(q in b for p in a for q in neighbours(p)):
        return False
    u = sorted(a+b)
    r0, c0 = min(r for r,c in u), min(c for r,c in u)
    normalized = tuple((r-r0,c-c0) for r,c in u)
    return len(splits(normalized)) > 1


class Encoder:
    def __init__(self):
        self.blocks = {}
        self.clauses = []
        self.nextvar = 1
        self.vertical = []
        self.horizontal = []

    def block(self, name, h, w):
        ps = placements(h,w)
        vs = list(range(self.nextvar,self.nextvar+len(ps)))
        self.nextvar += len(ps)
        self.blocks[name] = (h,w,ps,vs)
        at = {p:[] for p in product(range(h),range(w))}
        for tile,v in zip(ps,vs):
            for p in tile:
                at[p].append(v)
        for cover in at.values():
            self.clauses.append(cover)
            self.clauses.extend([-a,-b] for a,b in combinations(cover,2))
        self.forbid(ps,vs,ps,vs,same=True)

    def forbid(self, aa, av, bb, bv, same=False):
        at = {}
        for j,b in enumerate(bb):
            for p in b:
                at.setdefault(p,[]).append(j)
        for i,a in enumerate(aa):
            js = {j for p in a for q in neighbours(p) for j in at.get(q,())}
            for j in sorted(js):
                if same and j <= i:
                    continue
                if incompatible(a,bb[j]):
                    self.clauses.append([-av[i],-bv[j]])

    def seam(self, a, b, axis):
        h,w,aa,av = self.blocks[a]
        hb,wb,bb,bv = self.blocks[b]
        if axis == 'vertical':
            if w != wb:
                raise ValueError('vertical widths')
            shift = (h,0)
            self.vertical.append([a,b])
        else:
            if h != hb:
                raise ValueError('horizontal heights')
            shift = (0,w)
            self.horizontal.append([a,b])
        bb = [tuple((r+shift[0],c+shift[1]) for r,c in t) for t in bb]
        self.forbid(aa,av,bb,bv)

    def certificate(self, model):
        positive = set(x for x in model if x>0)
        return {'blocks':{name:{'height':h,'width':w,
                 'tiles':[t for t,v in zip(ps,vs) if v in positive]}
                 for name,(h,w,ps,vs) in self.blocks.items()},
                'vertical':self.vertical, 'horizontal':self.horizontal}


def canonical(tiles,h,w):
    transforms = [lambda r,c:(r,c),lambda r,c:(h-1-r,c),
                  lambda r,c:(r,w-1-c),lambda r,c:(h-1-r,w-1-c)]
    if h == w:
        transforms += [lambda r,c:(c,r),lambda r,c:(h-1-c,r),
                       lambda r,c:(c,h-1-r),lambda r,c:(h-1-c,h-1-r)]
    return min(tuple(sorted(tuple(sorted(f(r,c) for r,c in t)) for t in tiles))
               for f in transforms)


def main():
    p = argparse.ArgumentParser()
    p.add_argument('mode',choices=['count','direct','stack','palette'])
    p.add_argument('numbers',type=int,nargs='+')
    p.add_argument('--out',required=True)
    args=p.parse_args()
    wall,cpu=time.perf_counter(),time.process_time()
    e=Encoder()
    if args.mode in ('count','direct'):
        h,w=args.numbers
        e.block('A',h,w)
    elif args.mode == 'stack':
        w,*heights=args.numbers
        names=[]
        for h in heights:
            name=f'h{h}w{w}'
            e.block(name,h,w)
            names.append(name)
        for a,b in product(names,repeat=2):
            e.seam(a,b,'vertical')
    else:
        wa,wb=args.numbers
        for h,w in product((6,9),(wa,wb)):
            e.block(f'h{h}w{w}',h,w)
        for w,ha,hb in product((wa,wb),(6,9),(6,9)):
            e.seam(f'h{ha}w{w}',f'h{hb}w{w}','vertical')
        for h,a,b in product((6,9),(wa,wb),(wa,wb)):
            e.seam(f'h{h}w{a}',f'h{h}w{b}','horizontal')
    results=[]
    orbits=set()
    with Solver(name='cadical195',bootstrap_with=e.clauses) as solver:
        while solver.solve():
            cert=e.certificate(solver.get_model())
            results.append(cert)
            if args.mode != 'count':
                break
            orbits.add(canonical(cert['blocks']['A']['tiles'],h,w))
            selected=[v for v in solver.get_model() if 0<v<e.nextvar]
            solver.add_clause([-v for v in selected])
        stats=solver.accum_stats()
    receipt={'mode':args.mode,'parameters':args.numbers,
             'status':'SAT' if results else 'UNSAT_UNCERTIFIED',
             'count':len(results),'orbits':len(orbits) if args.mode=='count' else None,
             'variables':e.nextvar-1,'clauses':len(e.clauses),
             'wall_seconds':time.perf_counter()-wall,'cpu_seconds':time.process_time()-cpu,
             'solver_stats':stats}
    out=Path(args.out)
    out.parent.mkdir(parents=True,exist_ok=True)
    out.write_text(json.dumps(results if args.mode=='count' else results[0] if results else None)+'\n')
    out.with_suffix('.receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt),flush=True)


if __name__=='__main__':
    main()
