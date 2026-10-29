#!/usr/bin/env python3
"""Independent rational-matrix checker; no producer/other-checker imports."""
import hashlib
from itertools import combinations
import json
from multiprocessing import Pool
import os
from pathlib import Path
import sys
from flint import fmpq, fmpq_mat


def vertex_check(data):
    matrix,label,vector = data
    A = fmpq_mat(matrix)
    v = fmpq_mat([[x] for x in vector])
    assert v[0,0] == 1
    s = A*v
    assert all(s[i,0] >= 0 for i in range(A.nrows()))
    assert label == [i for i in range(A.nrows()) if s[i,0] == 0]
    B = fmpq_mat([[matrix[i][j] for j in range(1,A.ncols())] for i in label])
    assert B.det() != 0
    return True


def verify(obj, input_path, workers=1):
    raw = Path(input_path).read_bytes()
    assert hashlib.sha256(raw).hexdigest() == obj['input_sha256']
    matrix = json.loads(raw)
    if obj['chart_last']:
        matrix = [row[-1:] + row[:-1] for row in matrix]
    assert obj['matrix'] == matrix
    n,d = len(matrix), len(matrix[0])-1
    labs = obj['labels']
    assert len(labs) == len(obj['vertices']) > 0
    assert all(len(B) == d and B == sorted(set(B)) for B in labs)
    masks = [sum(1 << j for j in B) for B in labs]
    lookup = {m:i for i,m in enumerate(masks)}
    assert len(lookup) == len(labs)
    tasks = ((matrix,B,v) for B,v in zip(labs,obj['vertices']))
    if workers > 1:
        with Pool(workers) as p:
            assert all(p.imap_unordered(vertex_check,tasks,chunksize=128))
    else:
        assert all(map(vertex_check,tasks))
    edges = set()
    for i,(B,mask) in enumerate(zip(labs,masks)):
        near = set()
        for leave in B:
            # The cover lemma needs every basis direction, not merely
            # the total degree. Check each removed label independently.
            direction = []
            for enter in range(n):
                if mask & (1<<enter):
                    continue
                m = mask ^ (1<<leave) ^ (1<<enter)
                if m in lookup:
                    direction.append(lookup[m])
            assert len(direction) == 1
            near.add(direction[0])
        assert len(near) == d
        for j in near:
            if i < j:
                edges.add((i,j))
    assert sorted(edges) == list(map(tuple,obj['edges']))
    s,t = obj['endpoints']
    assert labs[s] == list(range(d)) and labs[t] == list(range(d,n))
    level = obj['potential']
    assert len(level) == len(labs) and level[s] == 0
    assert all(type(x) is int and x>=0 for x in level)
    for i,j in edges:
        assert -1 <= level[i]-level[j] <= 1
    path = obj['endpoint_path']
    assert path[0] == s and path[-1] == t and len(path)-1 == level[t]
    for i,j in zip(path,path[1:]):
        assert tuple(sorted([i,j])) in edges
    if n<=6:
        cover = set()
        for B in combinations(range(n),d):
            v = [(-1)**k*fmpq_mat([[matrix[i][j] for j in range(d+1) if j!=k] for i in B]).det() for k in range(d+1)]
            for sign in (1,-1):
                w = fmpq_mat([[sign*x] for x in v])
                sl = fmpq_mat(matrix)*w
                if any(x for x in v) and all(sl[i,0]>=0 for i in range(n)):
                    assert w[0,0]>0
                    cover.add(sum(1<<i for i in range(n) if sl[i,0]==0))
        assert cover == set(masks)
    return {'checker':'FLINT-rational-matrix', 'accepted_relative_graph':True,
            'vertices':len(labs),'edges':len(edges),'endpoint_distance':level[t],
            'control_cover_exhaustive':n<=6,'full_target_accepted':False}


if __name__ == '__main__':
    obj = json.loads(Path(sys.argv[1]).read_text())
    print(json.dumps(verify(obj,sys.argv[2],int(os.environ.get('PROOF_CPUS','1')))))
