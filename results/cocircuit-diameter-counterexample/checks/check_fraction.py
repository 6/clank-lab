#!/usr/bin/env python3
"""Independent scalar/integer geometry, labelled edges and distance checks.

No search code imports. Full basis cover is exhaustive only for the
discovery control. The main-size regular closure is checked but its
geometric completeness theorem is not asserted proved by this script.
"""
from collections import defaultdict
from fractions import Fraction as F
from functools import reduce
import hashlib
from itertools import combinations
import json
from math import gcd, lcm
from multiprocessing import Pool
import os
from pathlib import Path
import sys


def determinant(M):
    a = [row[:] for row in M]
    n = len(a)
    prev, sign = 1, 1
    for k in range(n-1):
        pivot = next((i for i in range(k, n) if a[i][k]), None)
        if pivot is None:
            return 0
        if pivot != k:
            a[pivot], a[k] = a[k], a[pivot]
            sign = -sign
        p = a[k][k]
        for i in range(k+1, n):
            for j in range(k+1, n):
                v = a[i][j]*p-a[i][k]*a[k][j]
                assert v % prev == 0
                a[i][j] = v//prev
            a[i][k] = 0
        prev = p
    return sign*a[-1][-1]


def integer_row(row):
    q = [F(x) for x in row]
    den = lcm(*(x.denominator for x in q))
    return [int(x*den) for x in q]


def check_vertex(payload):
    A, label, vals = payload
    v = integer_row(vals)
    assert v[0] > 0
    slacks = [sum(x*y for x, y in zip(row, v)) for row in A]
    assert all(x >= 0 for x in slacks)
    assert [i for i,x in enumerate(slacks) if x == 0] == label
    assert determinant([A[i][1:] for i in label]) != 0
    return True


def verify(cert, input_path, workers=1):
    raw = Path(input_path).read_bytes()
    assert cert['input_sha256'] == hashlib.sha256(raw).hexdigest()
    A = json.loads(raw)
    if cert['chart_last']:
        A = [[row[-1]]+row[:-1] for row in A]
    assert cert['matrix'] == A
    A = [integer_row(row) for row in A]
    n, r = len(A), len(A[0])
    labels = cert['labels']
    assert labels and all(len(x) == r-1 and x == sorted(set(x)) for x in labels)
    assert labels == sorted(set(map(tuple, labels))) or labels == list(map(list, sorted(set(map(tuple, labels)))))
    assert len(labels) == len(cert['vertices'])
    items = ((A, lab, v) for lab, v in zip(labels, cert['vertices']))
    if workers > 1:
        with Pool(workers) as pool:
            assert all(pool.imap_unordered(check_vertex, items, chunksize=128))
    else:
        assert all(map(check_vertex, items))
    ridges = defaultdict(set)
    for i, lab in enumerate(labels):
        for j in lab:
            ridges[tuple(x for x in lab if x != j)].add(i)
    assert all(len(x) == 2 for x in ridges.values())
    actual_edges = sorted(sorted(x) for x in ridges.values())
    assert cert['edges'] == actual_edges
    p = cert['potential']
    s, t = cert['endpoints']
    assert labels[s] == list(range(r-1)) and labels[t] == list(range(r-1,n))
    assert len(p) == len(labels) and p[s] == 0
    assert all(isinstance(x,int) and x >= 0 for x in p)
    assert all(abs(p[a]-p[b]) <= 1 for a,b in actual_edges)
    path = cert['endpoint_path']
    E = set(map(tuple, actual_edges))
    assert path[0] == s and path[-1] == t and len(path)-1 == p[t]
    assert all(tuple(sorted((a,b))) in E for a,b in zip(path,path[1:]))
    # An exhaustive independent cover at the control size; never C(80,41).
    if n <= 6:
        cover = set()
        for B in combinations(range(n), r-1):
            v = [(-1)**j*determinant([[A[i][k] for k in range(r) if k != j] for i in B]) for j in range(r)]
            for sign in [-1,1]:
                w = [sign*x for x in v]
                if not any(w):
                    continue
                slacks = [sum(x*y for x,y in zip(a,w)) for a in A]
                if min(slacks) >= 0:
                    assert w[0] > 0
                    cover.add(tuple(i for i,x in enumerate(slacks) if x == 0))
        assert cover == set(map(tuple, labels))
    return {'checker':'integer-Bareiss-scalar', 'accepted_relative_graph':True,
            'vertices':len(labels), 'edges':len(actual_edges),
            'endpoint_distance':p[t], 'control_cover_exhaustive':n<=6,
            'full_target_accepted':False}


if __name__ == '__main__':
    c = json.loads(Path(sys.argv[1]).read_text())
    print(json.dumps(verify(c,sys.argv[2],int(os.environ.get('PROOF_CPUS','1')))))
