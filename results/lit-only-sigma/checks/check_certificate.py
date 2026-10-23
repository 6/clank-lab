#!/usr/bin/env python3
"""Standalone direct validator of the finite closure certificate."""
import json
import sys

def check(c):
    a=c['rows'];n=len(a);x=c['start'];moves=c['regular_moves'];closed=c['closed']
    assert 0<n<=12 and all(type(r) is int and 0<=r<1<<n for r in a)
    assert all(bool(a[i]&(1<<j))==bool(a[j]&(1<<i)) for i in range(n) for j in range(n))
    reached={0};todo=[0]
    for i in todo:
        for j in range(n):
            if a[i]&(1<<j) and j not in reached:reached.add(j);todo.append(j)
    assert len(reached)==n
    # Nonadjacency is an equivalence relation in complete multipartite graphs.
    loopless=all(not (a[i]&(1<<i)) for i in range(n))
    transitive=all(not (not(a[i]&(1<<j)) and not(a[j]&(1<<k))) or not(a[i]&(1<<k))
                   for i in range(n) for j in range(n) for k in range(n))
    representatives=[]
    for i in range(n):
        if all(a[i]&(1<<r) for r in representatives):representatives.append(i)
    exception=loopless and transitive and len(representatives)%4==3
    assert not exception
    assert type(x) is int and 0<=x<1<<n
    y=x
    for v in moves:
        assert type(v) is int and 0<=v<n
        y^=a[v]
    assert all(type(z) is int and 0<=z<1<<n for z in closed)
    s=set(closed)
    assert len(s)==len(closed) and x in s
    for z in s:
        assert 2*(z.bit_count()-y.bit_count())>n
        for v in range(n):
            if z&(1<<v):assert z^a[v] in s
    return dict(accepted=True,n=n,start=x,regular_upper=y.bit_count(),lit_lower=min(z.bit_count() for z in s),closed_states=len(s))

if __name__=='__main__':
    print(json.dumps(check(json.load(open(sys.argv[1])))))
