#!/usr/bin/env python3
"""Checker A for the Nash-Williams counterexamples (independent of every search).

Conventions (Kuehn-Osthus survey, arXiv:1006.0590v1, Sec. 2.3; KOT arXiv:0807.1827v1):
a digraph has no loops and at most one arc in each direction between two vertices;
d+_1 <= ... <= d+_n and d-_1 <= ... <= d-_n are the sorted out- and in-degree sequences.
Hypothesis NW(G): for every integer i with 1 <= i < n/2,
  (i)  d+_i >= i+1  or  d-_{n-i} >= n-i,   and
  (ii) d-_i >= i+1  or  d+_{n-i} >= n-i.
KOT's condition (iii) (n even): d+_{n/2} >= n/2 or d-_{n/2} >= n/2.

For each witness this checks: well-formed, NW(G), strongly connected, no Hamilton cycle
(Held-Karp dynamic programme over subsets), and reports (iii).
Usage: check_a.py WITNESS_FILE... [--family NMIN NMAX]
Exit status 0 only if every witness is a strongly connected, non-Hamiltonian digraph satisfying NW.
"""
import sys

def read_witness(path):
    out = {}
    for line in open(path):
        line = line.split('#', 1)[0].strip()
        if not line:
            continue
        v, rest = line.split(':')
        v = int(v)
        if v in out:
            raise ValueError('vertex listed twice: %d' % v)
        out[v] = [int(x) for x in rest.split()]
    n = len(out)
    if sorted(out) != list(range(n)):
        raise ValueError('vertices must be 0..n-1')
    adj = [set() for _ in range(n)]
    for v, ws in out.items():
        for w in ws:
            if not 0 <= w < n or w == v or w in adj[v]:
                raise ValueError('bad arc %d->%d' % (v, w))
            adj[v].add(w)
    return adj

def family(u, l):
    """F(u,l): U={0..u-1} (each sends an arc to every other vertex), w=0, s=u, t=u+1,
    R={u+2..u+l-1}; L'={t} u R is a complete digraph; s->t, s->w, t->w; nothing else."""
    n = u + l
    adj = [set() for _ in range(n)]
    for x in range(u):
        adj[x] = set(range(n)) - {x}
    lp = [u + 1] + list(range(u + 2, n))
    for a in lp:
        for b in lp:
            if a != b:
                adj[a].add(b)
    adj[u] |= {u + 1, 0}
    adj[u + 1].add(0)
    return adj

def nw_hypothesis(adj):
    n = len(adj)
    dp = sorted(len(a) for a in adj)
    dm = sorted(sum(1 for u in range(n) if v in adj[u]) for v in range(n))
    d = lambda s, i: s[i - 1]  # 1-indexed
    ok = True
    for i in range(1, n):
        if 2 * i >= n:
            break
        ok &= (d(dp, i) >= i + 1 or d(dm, n - i) >= n - i)
        ok &= (d(dm, i) >= i + 1 or d(dp, n - i) >= n - i)
    cond3 = None if n % 2 else (d(dp, n // 2) >= n // 2 or d(dm, n // 2) >= n // 2)
    return ok, cond3, dp, dm

def strongly_connected(adj):
    n = len(adj)
    def reach(nbrs):
        seen, stack = {0}, [0]
        while stack:
            x = stack.pop()
            for y in nbrs[x]:
                if y not in seen:
                    seen.add(y); stack.append(y)
        return len(seen) == n
    rev = [set() for _ in range(n)]
    for x in range(n):
        for y in adj[x]:
            rev[y].add(x)
    return reach(adj) and reach(rev)

def hamiltonian(adj):
    n = len(adj)
    full = (1 << n) - 1
    reach = [0] * (1 << n)   # reach[S]: bitmask of end vertices of paths from 0 covering exactly S
    reach[1] = 1
    for S in range(1, 1 << n, 2):
        ends = reach[S]
        if not ends:
            continue
        for v in range(n):
            if ends >> v & 1:
                for w in adj[v]:
                    if not S >> w & 1:
                        reach[S | 1 << w] |= 1 << w
    return any(reach[full] >> v & 1 and 0 in adj[v] for v in range(n))

def report(name, adj):
    ok, c3, dp, dm = nw_hypothesis(adj)
    sc, ham = strongly_connected(adj), hamiltonian(adj)
    good = ok and sc and not ham and len(adj) >= 3
    print('%s n=%d out=%s in=%s NW=%s strong=%s hamiltonian=%s cond_iii=%s -> %s' %
          (name, len(adj), dp, dm, ok, sc, ham, c3, 'COUNTEREXAMPLE' if good else 'FAIL'))
    return good

def main(argv):
    args, fam = [], None
    i = 0
    while i < len(argv):
        if argv[i] == '--family':
            fam = (int(argv[i + 1]), int(argv[i + 2])); i += 3
        else:
            args.append(argv[i]); i += 1
    good = True
    for p in args:
        good &= report(p, read_witness(p))
    if fam:
        for n in range(fam[0], fam[1] + 1):
            good &= report('F(%d,4)' % (n - 4), family(n - 4, 4))
    print('PASS' if good else 'REJECT')
    return 0 if good else 1

if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
