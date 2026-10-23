#!/usr/bin/env python3
"""Partition, exact covers, and symmetric endpoint ranks; no search import."""
import gzip,json,sys

def check(graph,certificate):
    labels=[tuple(x) for x in graph['labels']]
    if len(labels)!=len(set(labels)): raise ValueError('duplicate vertex')
    ids={v:i+1 for i,v in enumerate(labels)}
    ranks={i+1:r for i,r in enumerate(graph['ranks'])}
    edges={tuple(e) for e in graph['edges']}
    used=set()
    if certificate['group']!=graph['group']:raise ValueError('group')
    for chain in certificate['chains']:
        if not chain:raise ValueError('empty chain')
        path=[]
        for label in chain:
            vertex=ids.get(tuple(label))
            if vertex is None or vertex in used:raise ValueError('missing/duplicate vertex')
            used.add(vertex);path.append(vertex)
        if ranks[path[0]]+ranks[path[-1]]!=graph['rank']:raise ValueError('asymmetry')
        for a,b in zip(path,path[1:]):
            if ranks[b]!=ranks[a]+1 or (a,b) not in edges:raise ValueError('noncover')
    if len(used)!=len(labels):raise ValueError('incomplete partition')

if __name__=='__main__':
    try:
        graph=json.load(open(sys.argv[1])); raw=open(sys.argv[2],'rb').read()
        cert=json.loads(gzip.decompress(raw) if sys.argv[2].endswith('.gz') else raw)
        check(graph,cert)
        print(json.dumps({'accepted':True,'checker':'python','vertices':len(graph['labels']),'chains':len(cert['chains']),'rank_sizes':[graph['ranks'].count(i) for i in range(graph['rank']+1)]}))
    except Exception as exc:
        print('REJECT',str(exc));sys.exit(1)
