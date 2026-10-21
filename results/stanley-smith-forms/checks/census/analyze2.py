import json, sys
from collections import Counter, defaultdict
from sympy import factorint
sys.dont_write_bytecode = True  # write nothing into this folder
import specht_lattice as S
R = [r for r in json.load(open(sys.argv[1])) if r['lattice'] == 'specht']
def ppart(lst, p):
    out = []
    for x in lst:
        if x == 0: out.append('0'); continue
        e = 0
        while x % p == 0: x //= p; e += 1
        out.append(e)
    return out
primes_bad = Counter(); byk = Counter(); tot_k = Counter(); diag_ok = 0
for r in R:
    tot_k[(r['k'] == r['n'])] += 1
    ev = []
    _, cnt = S.predicted(tuple(r['lam']), r['k'])
    for (i, j), c in cnt.items(): ev += [j - i] * c
    import flint
    d = flint.fmpz_mat([[ev[i] if i == j else 0 for j in range(len(ev))] for i in range(len(ev))]).snf()
    dd = S.normalize([abs(int(d[i, i])) for i in range(len(ev))])
    diag_ok += dd == r['snf']
    if r['ok']: continue
    byk[(r['k'] == r['n'])] += 1
    for p in [2, 3, 5, 7]:
        if ppart(r['snf'], p) != ppart(r['pred'], p): primes_bad[p] += 1
print("mismatch primes", dict(primes_bad), "| mismatches with k==n vs k<n", dict(byk), "of", dict(tot_k))
print("cases where SNF equals SNF of the diagonal eigenvalue matrix:", diag_ok, "of", len(R))
two_row = [r for r in R if len(r['lam']) <= 2 and not r['ok']]
print("two-row mismatches:", [(tuple(r['lam']), r['k']) for r in two_row])
