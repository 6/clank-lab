"""Derive closure constants from exact full facet geometry in dimensions 3..5."""
from collections import defaultdict
from flint import arb
from geometry import Impossible, sub, dot, norm2, positive_sqrt
from s3_arith import independent, circumcentre
from s3_stars import model_geometry


def closure_cycles(state,models):
    """Cycles about codimension-three faces of the full polytope.

    Their supports in the VF are edges in D=5, vertices in D=4, and
    the empty face in D=3. Incident model ridges represent full faces of
    dimension D-2, so their centres use D-2 independent edge vectors.
    No fitted angles or interval-overlap equalities are used.
    """
    faces=defaultdict(list)
    intrinsic=None
    for fi,f in enumerate(state['facets']):
        m=models[f['name']]
        points,base,ns=model_geometry(m)
        dimension=len(points[0])
        if dimension not in (2,3,4):
            raise ValueError('closure supports full polytope dimensions 3, 4 and 5')
        if intrinsic is not None and dimension!=intrinsic:
            raise ValueError('mixed full facet dimensions in closure cycle')
        intrinsic=dimension
        if len(f['map'])!=len(ns) or len(set(f['map']))!=len(ns):
            raise Impossible('invalid closure facet neighbour map')
        if dimension==4:
            supports=[(tuple(edge),p) for edge,p in m.edge_p.items()]
        elif dimension==3:
            supports=[((a,),None) for a in range(len(ns))]
        else:
            supports=[((),None)]
        e=[sub(points[i],points[base]) for i in ns]
        for support,p in supports:
            key=tuple(sorted(f['map'][i] for i in support))
            rs=[r for r in m.ridges if set(support)<=set(r['vertices'])]
            if len(rs)!=2:
                raise ValueError('model cycle support must have exactly two incident VF ridges')
            ridges=[tuple(sorted(f['map'][j] for j in r['vertices'])) for r in rs]
            if len(set(ridges))!=2:
                raise Impossible('collapsed incident closure ridges')
            oG=(circumcentre([e[i] for i in support]) if support
                else (arb(0),)*dimension)
            cs=[]
            for r in rs:
                candidates=[e[i] for i in r['vertices']]
                ids=independent(candidates,dimension-1)
                cs.append(circumcentre([candidates[i] for i in ids]))
            rays=[sub(c,oG) for c in cs]
            d2=[norm2(u) for u in rays]
            ca=dot(*rays)/positive_sqrt(d2[0]*d2[1])
            faces[key].append({'facet':fi,'p':p,'ridges':ridges,
                               'd2':d2,'cos_alpha':ca,'rho2':norm2(oG)})
    cycles=[]
    for key,uses in sorted(faces.items()):
        if len(uses)<3: raise Impossible('fewer than three facets in a closure cycle')
        p=uses[0]['p']
        if any(u['p']!=p for u in uses): raise Impossible('polygon size mismatch')
        incidence=defaultdict(list)
        for k,u in enumerate(uses):
            for r in u['ridges']: incidence[r].append(k)
        if any(len(v)!=2 for v in incidence.values()):
            raise Impossible('not a closed facet cycle at VF support')
        order=[];d2=[];ca=[];seen=set();cur=0;incoming=uses[0]['ridges'][0]
        while cur not in seen:
            seen.add(cur);u=uses[cur];order.append(u['facet'])
            j=1-u['ridges'].index(incoming)
            outgoing=u['ridges'][j]
            d2.append(u['d2'][j]);ca.append(u['cos_alpha'])
            nxt=[v for v in incidence[outgoing] if v!=cur]
            if len(nxt)!=1: raise Impossible('invalid closure ridge pairing')
            incoming=outgoing;cur=nxt[0]
        if cur!=0 or len(seen)!=len(uses): raise Impossible('disconnected facet cycle')
        cycle={'rho2':uses[0]['rho2'],'d2':d2,'cos_alpha':ca,
               'edge':list(key),'p':p,'facet_indices':order}
        if intrinsic!=4:
            cycle['face_kind']='edge' if intrinsic==3 else 'vertex'
        cycles.append(cycle)
    return cycles
