#!/usr/bin/env python3
"""Finite controls for the pseudo-Anosov-base extension in the Artin model.

All-k claims require the Lean algebra plus the written surface argument.
"""
import argparse
import importlib.util
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('extension_free_group', ROOT/'check_free_group.py')
model = importlib.util.module_from_spec(spec)
spec.loader.exec_module(model)


def check(kmax, corruption=None, mutation=None):
    curves = dict(model.CURVES)
    if corruption:
        curves.update({k:tuple(v) for k,v in json.loads(Path(corruption).read_text()).items()})
    log=[]
    # Retain the original curve-name controls.
    model.check(curves, 1, log)
    failures=[s for s in log if s.startswith('FAIL')]
    checks=len(log)

    def expect(ok, label):
        nonlocal checks
        checks += 1
        if not ok:
            failures.append(label)

    for sign in (1,-1):
        def tw(name,n):
            return model.tw(name,sign*n)
        t=tw('a',1)*tw('c',1)
        ti=tw('c',-1)*tw('a',-1)
        for k in range(1,kmax+1):
            g=tw('a',-1)*tw('c',-(k+(0 if mutation=='exponent' else 1)))*tw('d',1)
            if mutation=='order':
                g=tw('d',1)*tw('c',-(k+1))*tw('a',-1)
            def member(n):
                return (t.power(n) if n>=0 else ti.power(-n))*g
            for n in sorted({-2,-1,0,1,2,k,k+1,k+2}):
                rhs=tw('a',n-1)*tw('c',n-k-1)*tw('d',1)
                expect(member(n)==rhs, f'identity sign={sign} k={k} n={n}')
            expect(model.same_curve(member(1)(curves['C']),curves['C']),
                   f'fix-C sign={sign} k={k}')
            expect(model.same_curve(member(k+1)(curves['Cp']),curves['Cp']),
                   f'fix-Cprime sign={sign} k={k}')
            ga=g(curves['a'])
            for name in ('a','c'):
                expect(not model.same_curve(tw(name,1)(ga),ga),
                       f'intersect-{name} sign={sign} k={k}')
    return {'checker':'extension-free-group','kmax':kmax,'checks':checks,
            'failures':len(failures),'first_failure':next(iter(failures),None),
            'verdict':'REJECT' if failures else 'ACCEPT'}


if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--kmax',type=int,default=12)
    ap.add_argument('--curves')
    ap.add_argument('--mutation',choices=['order','exponent'])
    args=ap.parse_args()
    if args.kmax<1:
        ap.error('kmax must be positive')
    result=check(args.kmax,args.curves,args.mutation)
    print(json.dumps(result,sort_keys=True))
    raise SystemExit(result['verdict']!='ACCEPT')
