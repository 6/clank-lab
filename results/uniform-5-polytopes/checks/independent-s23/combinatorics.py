"""Exact cyclic words and complete, finite combinatorial tests."""
from geometry import Impossible


def rotations(seq):
    seq = tuple(seq)
    return [seq[i:]+seq[:i] for i in range(len(seq))]


def polygon_key(seq):
    return min(rotations(seq)+rotations(tuple(reversed(seq))))


def word_variants(word):
    w = tuple(tuple(x) for x in word)
    n = len(w)
    rev = tuple((w[-i % n][0], w[(-i-1) % n][1]) for i in range(n))
    return rotations(w)+rotations(rev)


def word_key(word):
    return min(word_variants(word))


def cycle_word(c):
    return word_key(zip(c['facets'], c['cells'], strict=True))


def signature_key(sig):
    return (tuple(sorted(sig['facets'])), tuple(sorted(word_key(w) for w in sig['cycles'])))


def build_incidence(placed, models):
    ridges, edges = {}, {}
    for fi,f in enumerate(placed):
        model = models[f['name']]
        ids = f['map']
        if len(set(ids)) != len(ids):
            raise Impossible('facet vertices identified with each other')
        for ri,r in enumerate(model.ridges):
            order = tuple(ids[i] for i in r['vertices'])
            key = tuple(sorted(order))
            entry = ridges.setdefault(key, {'order': polygon_key(order), 'label': r['label'], 'uses': []})
            if entry['label'] != r['label'] or entry['order'] != polygon_key(order):
                raise Impossible('ridge label or cyclic order mismatch')
            entry['uses'].append((fi,ri,order))
            if len(entry['uses']) > 2:
                raise Impossible('ridge in more than two facets')
        intrinsic = len(model.vf_points[0])
        if intrinsic == 2:
            supports = [((i,), None) for i in range(len(ids))]
        elif intrinsic == 3:
            supports = list(model.edge_p.items())
        else:
            raise ValueError('S2 supports only intrinsic dimensions two and three')
        for support,p in supports:
            key = tuple(sorted(ids[i] for i in support))
            entry = edges.setdefault(key, {'p':p, 'facets':[]})
            if entry['p'] != p:
                raise Impossible('polygon-size mismatch')
            entry['facets'].append(fi)
    return ridges, edges


def check_cycles(placed, models, allowed, complete=False):
    ridges, edges = build_incidence(placed,models)
    words = []
    for edge, data in edges.items():
        graph = {f:[] for f in data['facets']}
        for key,r in ridges.items():
            if not set(edge).issubset(key):
                continue
            # Only sides of the polygon count, not a diagonal.
            order = r['order']
            if len(edge) == 2 and edge not in {tuple(sorted((order[i],order[(i+1)%len(order)]))) for i in range(len(order))}:
                continue
            if len(r['uses']) == 2:
                a,b = (u[0] for u in r['uses'])
                graph[a].append((b,r['label']))
                graph[b].append((a,r['label']))
        if any(len(v)>2 for v in graph.values()):
            raise Impossible('branched link of edge')
        remaining = set(graph)
        components = []
        while remaining:
            todo=[min(remaining)]; comp=set()
            while todo:
                x=todo.pop()
                if x in comp: continue
                comp.add(x); todo.extend(y for y,_ in graph[x])
            remaining -= comp
            components.append(comp)
        for comp in components:
            ends=[x for x in comp if len(graph[x])<2]
            closed=not ends
            if closed and (len(components)>1 or len(comp)<3):
                raise Impossible('closed proper edge-link component')
            start=min(ends or comp)
            fs=[]; cs=[]; prev=None; cur=start
            while True:
                fs.append(placed[cur]['name'])
                options=[(x,c) for x,c in graph[cur] if x!=prev]
                if not options: break
                nxt,lab=options[0]
                cs.append(lab)
                if nxt==start: break
                prev,cur=cur,nxt
                if len(fs)>len(comp):
                    raise Impossible('invalid link traversal')
            options=allowed.get(data['p'],())
            if closed:
                w=word_key(zip(fs,cs,strict=True))
                if w not in options:
                    raise Impossible('closed edge cycle not allowed')
                words.append(w)
            else:
                if complete:
                    raise Impossible('open edge cycle in completed figure')
                possible=False
                for w in options:
                    for v in word_variants(w):
                        if len(v)>=len(fs) and all(v[i][0]==x for i,x in enumerate(fs)) and all(v[i][1]==x for i,x in enumerate(cs)):
                            possible=True;break
                    if possible:break
                if not possible:
                    raise Impossible('edge-link path extends no allowed cycle')
    if complete and any(len(r['uses'])!=2 for r in ridges.values()):
        raise Impossible('unpaired ridge')
    return ridges, {'facets':sorted(f['name'] for f in placed), 'cycles':sorted(words)}
