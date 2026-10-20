"""Independent exhaustive gluing from paper S2, with exact option certificates.

Only mathematical-model APIs are imported. Recorded stage-2/3 outputs are
never inputs to the search. All pruning is necessary under the hypothesis
that the branch belongs to one uniform polytope.
"""
from dataclasses import dataclass
from collections import Counter
from itertools import chain
import json
import time
from flint import arb
from geometry import (Undecided, Impossible, ball_interval, dot, add, sub,
                      scale, norm2, positive_sqrt, unit, gram_schmidt, cross,
                      resolve, identity, encode_ball, encode_points)
from combinatorics import rotations, polygon_key, cycle_word, check_cycles, signature_key
from provenance import json_digest


def ordered_options(model):
    result=[]
    for ri,r in enumerate(model.ridges):
        for seq in rotations(r['vertices'])+rotations(tuple(reversed(r['vertices']))):
            option = (ri,tuple(seq))
            if option not in result:
                result.append(option)
    return result


def equivalences(model):
    """Each removed correspondence has an exact model-symmetry witness.

    model.verify_stabilizer must certify membership by exact construction,
    not by overlapping numerical coordinates. An empty group retains all.
    """
    options=ordered_options(model)
    inverse={o:i for i,o in enumerate(options)}
    ridge_ids={tuple(sorted(r['vertices'])):i for i,r in enumerate(model.ridges)}
    n=len(model.vf_points)
    identity_perm=tuple(range(n))
    perms=[identity_perm]
    for perm in model.stabilizers:
        perm=tuple(perm)
        if perm==identity_perm: continue
        if sorted(perm)!=list(range(n)) or not model.verify_stabilizer(perm):
            raise ValueError('invalid exact stabilizer certificate')
        perms.append(perm)
    retained=[]; records=[]; covered={}
    for oi,(ri,order) in enumerate(options):
        if oi in covered:
            rep,perm=covered[oi]
            records.append({'option':oi,'representative':rep,'permutation':list(perm)})
            continue
        retained.append(oi)
        records.append({'option':oi,'representative':oi,'permutation':list(identity_perm)})
        for perm in perms:
            image=tuple(perm[i] for i in order)
            rj=ridge_ids.get(tuple(sorted(image)))
            if rj is None or model.ridges[rj]['label']!=model.ridges[ri]['label']:
                raise ValueError('stabilizer does not preserve ridge labels')
            if any(model.edge_p.get(tuple(sorted((perm[a],perm[b]))))!=p for (a,b),p in model.edge_p.items()):
                raise ValueError('stabilizer does not preserve polygon sizes')
            oj=inverse.get((rj,image))
            if oj is None: raise ValueError('stabilizer does not preserve cyclic orders')
            # This witness maps retained -> discarded. Its inverse is also exact.
            covered.setdefault(oj,(oi,perm))
    return [options[i] for i in retained], {'options':[[r,list(o)] for r,o in options], 'retained':retained,'records':records}


def source_frame(model, order):
    points = model.vf_points
    intrinsic = len(points[0])
    if intrinsic not in (2, 3) or any(len(p) != intrinsic for p in points):
        raise ValueError('S2 requires uniformly 2-D or 3-D facet vertex figures')
    a = points[order[0]]
    directions = gram_schmidt([sub(points[i], a) for i in order[1:intrinsic]])
    normal = (unit((-directions[0][1], directions[0][0])) if intrinsic == 2 else
              unit(cross(*directions)))
    s = dot(normal, a)
    if s > 0: normal = scale(-1, normal)
    elif not s < 0: raise Undecided('template ridge plane goes through VF centre')
    return a, directions + (normal,)


def seed(model,height):
    intrinsic = len(model.vf_points[0])
    pts = [tuple(x)+(height,) for x in model.vf_points]
    ambient = intrinsic + 1
    return pts, {'name':model.name,'map':list(range(len(pts))),
                 'normal':tuple(arb(i == intrinsic) for i in range(ambient)), 'height':height,
                 'source_origin':(arb(0),)*intrinsic,
                 'target_origin':(arb(0),)*intrinsic+(height,),
                 'source_frame':tuple(tuple(arb(i==j) for i in range(intrinsic)) for j in range(intrinsic)),
                 'target_frame':tuple(tuple(arb(i==j) for i in range(ambient)) for j in range(intrinsic)),
                 'hinge':None}


def placements(model, order, target, old_normal, height):
    """The opposite-side hinge, for a segment or polygon target ridge.

    The directions of a codimension-two ridge have dimension D-2 in the
    D-dimensional VF. Its perpendicular plane is spanned by its radial
    centre t and the old facet normal's component orthogonal to t.
    The negative coefficient chooses the opposite side exactly as in 5D.
    """
    a, sf = source_frame(model, order)
    ambient = len(old_normal)
    if ambient != len(sf)+1 or any(len(p) != ambient for p in target):
        raise ValueError('mixed S2 model/placement dimension')
    q = target[0]
    directions = gram_schmidt([sub(p, q) for p in target[1:ambient-1]])
    t = q
    for axis in directions:
        t = sub(t, scale(dot(q,axis),axis))
    t2 = norm2(t)
    if not t2 > 0: raise Undecided('target ridge centre unresolved')
    u = unit(sub(old_normal,scale(dot(old_normal,t)/t2,t)))
    rad = 1-height**2/t2
    if rad <= 0: raise Impossible('no nondegenerate hinge')
    g = positive_sqrt(rad)
    for sign in (-1,):
        normal = add(scale(height/t2,t),scale(sign*g,u))
        inward = unit(sub(scale(height,normal),t))
        tf = directions + (inward,)
        points = [add(q, tuple(sum((dot(sub(x,a),sf[j])*tf[j][i]
                    for j in range(ambient-1)),arb(0)) for i in range(ambient)))
                  for x in model.vf_points]
        yield points, {'name':model.name,'normal':normal,'height':height,
                       'source_origin':a,'target_origin':q,'source_frame':sf,
                       'target_frame':tf,'hinge':sign,
                       'required_ridge':list(zip(order,target,strict=True))}


def attach(points, facets, proposed, placement):
    for si,y in placement.get('required_ridge',[]):
        if not identity(proposed[si],y):
            raise Impossible('ordered ridge correspondence misses its target')
    indices=[]; result=list(points)
    for x in proposed:
        idx=resolve(x,result)
        if idx is None: idx=len(result);result.append(x)
        indices.append(idx)
    if len(set(indices))!=len(indices):
        raise Impossible('collapsed model facet')
    key=frozenset(indices)
    if any(frozenset(f['map'])==key for f in facets):
        raise Impossible('duplicate facet')
    new=dict(placement,map=indices)
    for f in facets+[new]:
        for i,x in enumerate(result):
            if i not in f['map'] and dot(f['normal'],x)>f['height']:
                raise Impossible('strict supporting-plane violation')
    return result,facets+[new]


def assert_strict(points,facets):
    for f in facets:
        for i,x in enumerate(points):
            if i not in f['map'] and not dot(f['normal'],x)<f['height']:
                raise Undecided('nonincident vertex not certified strictly interior')


@dataclass
class SearchResult:
    index: int
    radius: list
    states: list
    statistics: dict
    open_reasons: list
    input_class_sha256: str

    def record(self,include_states=False):
        sigs={signature_key(s['signature']):s['signature'] for s in self.states}
        record={'index':self.index,'R':self.radius,
                'input_class_sha256':self.input_class_sha256,
                'status':'OPEN' if self.open_reasons else 'COMPLETE',
                'vfs':[sigs[k] for k in sorted(sigs)],'statistics':self.statistics,
                'open_reasons':self.open_reasons}
        if include_states:
            record['states']=[]
            for s in self.states:
                fs=[]
                for f in s['facets']:
                    d={k:f[k] for k in ('name','map','hinge')}
                    for k in ('normal','source_origin','target_origin'):
                        d[k]=[encode_ball(x) for x in f[k]]
                    for k in ('source_frame','target_frame'):
                        d[k]=encode_points(f[k])
                    d['height']=encode_ball(f['height']);fs.append(d)
                record['states'].append({'points':encode_points(s['points']),'facets':fs,'signature':s['signature']})
        return record


def search_class(c,models,node_limit=None):
    start=time.process_time()
    R=ball_interval(*c['R']);r2=1-1/(4*R**2)
    allowed={}
    for cycle in c['cycles']:
        allowed.setdefault(cycle['p'],set()).add(cycle_word(cycle))
    names=sorted(set(chain.from_iterable(w['facets'] for w in c['cycles'])))
    heights={}; options={}; stats=Counter(); states=[]; opens=[]
    try:
        for name in names:
            m=models[name]
            h2=r2-(1-1/(4*m.radius2))
            if h2<=0: continue
            heights[name]=positive_sqrt(h2)
            options[name]=equivalences(m)[0]
    except (Undecided,Impossible) as e:
        return SearchResult(c['index'],c['R'],[],dict(stats),[str(e)],json_digest(c))

    def visit(points,facets,minname):
        stats['nodes']+=1
        if node_limit is not None and stats['nodes']>node_limit:
            raise Undecided('explicit node limit reached; search not exhausted')
        try:
            ridges,_=check_cycles(facets,models,allowed)
            unpaired=[(key,r) for key,r in ridges.items() if len(r['uses'])==1]
            if not unpaired:
                _,sig=check_cycles(facets,models,allowed,complete=True)
                assert_strict(points,facets)
                states.append({'points':points,'facets':facets,'signature':sig})
                stats['complete_states']+=1
                return
            def optlist(r):
                return [(name,ri,order) for name in heights if name>=minname for ri,order in options[name]
                        if models[name].ridges[ri]['label']==r['label'] and len(order)==len(r['order'])]
            key,r=min(unpaired,key=lambda kv:(len(optlist(kv[1])),kv[0]))
            fi,_,order=r['uses'][0]
            target=[points[i] for i in order]
            for name,ri,source_order in optlist(r):
                # Every candidate remains unless a necessary condition is disproved.
                try:
                    for pp,pf in placements(models[name],source_order,target,facets[fi]['normal'],heights[name]):
                        stats['hinges']+=1
                        try:
                            np,nf=attach(points,facets,pp,pf)
                            visit(np,nf,minname)
                        except Impossible as e: stats[str(e)]+=1
                except Impossible as e: stats[str(e)]+=1
        except Impossible as e: stats[str(e)]+=1

    for name in heights:
        points,f=seed(models[name],heights[name])
        try: visit(points,[f],name)
        except Undecided as e:
            opens.append(f'{name}: {e}')
    stats['cpu_seconds']=time.process_time()-start
    return SearchResult(c['index'],c['R'],states,dict(stats),opens,json_digest(c))
