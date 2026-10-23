#!/usr/bin/env python3
"""Exact coefficient comparison after substituting H-invariant generators.

Independent of CAS/search and the prior generating-series construction.
The 486-vector type is evaluated through its complete mod-3 character table;
the 270 two-coordinate vectors are summed explicitly on their possible supports.
"""
import argparse, ast, hashlib, itertools, json, math, pathlib, time
from functools import lru_cache

P = 1009
W = next(x for x in range(2, P) if pow(x, 3, P) == 1)
THETA = (W - W * W) % P

def compositions(n, length):
    if length == 1:
        yield (n,)
    else:
        for i in range(n + 1):
            for tail in compositions(n - i, length - 1):
                yield (i,) + tail

def add(d, e, c):
    d[e] = (d.get(e, 0) + c) % P
    if not d[e]:
        del d[e]

@lru_cache(None)
def powers(a, c, d):
    ans = {(0, 0, 0, 0): 1}
    for power, count in [(3, a), (6, c), (9, d)]:
        for _ in range(count):
            nxt = {}
            for e, coefficient in ans.items():
                for j in range(4):
                    f = list(e); f[j] += power
                    add(nxt, tuple(f), coefficient)
            ans = nxt
    return ans

def from_input(path, corrupt=False):
    ans = {}
    rows = path.read_text().splitlines()
    for index, row in enumerate(rows):
        exponent, coefficient = row.split(':')
        a, b, c, d, ey, ez = ast.literal_eval(exponent.replace('{','[').replace('}',']'))
        coefficient = int(coefficient) + int(corrupt and index == 0)
        for e, value in powers(a, c, d).items():
            add(ans, tuple(v + b for v in e) + (ey, ez), coefficient * value)
    return ans

@lru_cache(None)
def last_coordinates(a, b):
    # (y+z)^a (y-z)^b; index is the z exponent.
    values = [0] * (a + b + 1)
    for j in range(a + 1):
        for k in range(b + 1):
            values[j + k] += math.comb(a, j) * math.comb(b, k) * (-1)**k
    return [(a + b - z, z, value % P) for z, value in enumerate(values) if value % P]

def characters():
    # Both signs coincide for the even degrees checked below.
    vectors = [a + ((-sum(a)) % 3,) for a in itertools.product(range(3), repeat=5)]
    result = {}
    for residue in itertools.product(range(3), repeat=6):
        value = 2 * sum(pow(W, sum(a*b for a,b in zip(v,residue)) % 3, P) for v in vectors) % P
        expected = 486 if len(set(residue)) == 1 else 0
        assert value == expected, (residue, value)
        if value:
            result[residue] = value
    return result

def source_coefficients(degree, chars):
    fact = math.factorial(degree) % P
    invfacts = [pow(math.factorial(j) % P, -1, P) for j in range(degree + 1)]
    original = {}
    for residue, character in chars.items():
        rem = degree - sum(residue)
        if rem >= 0 and rem % 3 == 0:
            for pieces in compositions(rem // 3, 6):
                e = tuple(3*x+r for x,r in zip(pieces,residue))
                coefficient = fact * character
                for x in e: coefficient = coefficient * invfacts[x] % P
                add(original, e, coefficient)
    # Directly sum the 18 vectors on each coordinate pair. A zero exponent
    # on an absent coordinate contributes 1; nonzero absent exponents give 0.
    for i, j in itertools.combinations(range(6), 2):
        vectors = [(sign*THETA*pow(W,a,P) % P, -sign*THETA*pow(W,b,P) % P)
                   for a,b in itertools.product(range(3),repeat=2) for sign in [1,-1]]
        for u in range(degree + 1):
            e = [0]*6; e[i] = u; e[j] = degree-u
            moment = sum(pow(x,u,P)*pow(y,degree-u,P) for x,y in vectors) % P
            add(original, tuple(e), math.comb(degree,u)*moment)
    expanded = {}
    for e, coefficient in original.items():
        for ey, ez, value in last_coordinates(e[4],e[5]):
            add(expanded, e[:4]+(ey,ez), coefficient*value)
    return expanded, len(original)

def digest(poly):
    data = '\n'.join(','.join(map(str,e))+':'+str(poly[e]) for e in sorted(poly))
    return hashlib.sha256(data.encode()).hexdigest()

def main():
    parser=argparse.ArgumentParser();parser.add_argument('inputs',type=pathlib.Path);parser.add_argument('--out',type=pathlib.Path,required=True)
    args=parser.parse_args();start=time.perf_counter();cpu=time.process_time()
    chars=characters();rows=[]
    for degree in [6,12,18,24,30,42]:
        st=time.perf_counter();path=args.inputs/f'input-{degree}.txt'
        got=from_input(path);expected,n=source_coefficients(degree,chars)
        assert got==expected, ('coefficient mismatch',degree)
        assert from_input(path,True)!=expected, ('corruption accepted',degree)
        rows.append({'degree':degree,'original_support':n,'expanded_support':len(got),'sha256':digest(got),'all_coefficients_equal':True,'coefficient_corruption_rejected':True,'wall_seconds':time.perf_counter()-st})
    result={'prime':P,'character_residues_checked':3**6,'nonzero_character_residues':len(chars),'vector_count':486+270,'checks':rows,'unresolved':0,'cpu_seconds':time.process_time()-cpu,'wall_seconds':time.perf_counter()-start,'scope':'all coefficients of six modular polynomial input identities; source lattice/group identification remains a mathematical premise'}
    args.out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))

if __name__=='__main__':main()
