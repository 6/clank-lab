import json, sys, itertools
from collections import Counter, defaultdict
sys.dont_write_bytecode = True  # write nothing into this folder
import specht_lattice as S
R = json.load(open(sys.argv[1]))
by = {(tuple(r['lam']), r['k']): r for r in R if r['lattice'] == 'specht'}
def conj(l):
    return tuple(sum(1 for x in l if x > j) for j in range(l[0]))
stats = defaultdict(lambda: [0, 0]); sym_bad = 0; det_bad = 0; rank_bad = 0; weak_bad = []
def eigen(lam, k):
    _, cnt = S.predicted(lam, k)
    ev = []
    for (i, j), c in cnt.items(): ev += [j - i] * c
    return ev
def products(ev):
    ps = {1}
    for e in ev:
        ps |= {p * abs(e) for p in ps}
    return ps
for (lam, k), r in sorted(by.items()):
    stats[r['n']][0] += 1; stats[r['n']][1] += (not r['ok'])
    rc = by[(conj(lam), k)]
    if rc['snf'] != r['snf']: sym_bad += 1
    ev = eigen(lam, k)
    nz = [e for e in ev if e]
    if sum(1 for x in r['snf'] if x) != len(nz): rank_bad += 1
    if len(nz) == len(ev):
        p = 1
        for e in ev: p *= e
        q = 1
        for x in r['snf']: q *= x
        if abs(p) != q: det_bad += 1
    ps = products(ev)
    if any(x and x not in ps for x in r['snf']):
        weak_bad.append((r['n'], lam, k))
print("per n: cases, mismatches", dict(stats))
print("transpose-symmetry violations", sym_bad, "rank violations", rank_bad, "det violations", det_bad)
print("weak-form (each entry a product of eigenvalues) failures:", len(weak_bad), weak_bad[:6])
first = min((r['n'], sum(r['lam']) and tuple(r['lam']), r['k']) for r in by.values() if not r['ok'])
print("first mismatch", first)
