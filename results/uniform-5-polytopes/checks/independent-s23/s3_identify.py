"""Identification by complete elimination (paper S3), NEVER overlap equality."""
from flint import arb
from geometry import Undecided, sub, norm2
from s3_arith import columns, inverse, independent, apply, apart
from s3_grid import PointIndex
from s3_stars import model_full_points


def exact_neighbour_count(Q):
    """Construction-exact count; caller must certify_known_model first.

    exact_neighbours is available without expanding the full orbit. The
    fallback supports small verified providers with full index lists.
    """
    return len(Q.exact_neighbours) if hasattr(Q,'exact_neighbours') else len(Q.neighbours)


def exclude_known(star,Q,frame_limit=None):
    """NO iff EVERY potentially isometric anchor frame has a strict mismatch.

    Q's full centered vertex set and exact neighbour indices are model
    facts. A surviving numerical frame proves nothing about equality.
    """
    if not Q.certify_known_model(): raise Undecided('known model construction not certified')
    return _exclude_certified_known(star,Q,frame_limit)


def _exclude_certified_known(star,Q,frame_limit=None):
    # Internal continuation after certificate verification, with no mutation
    # between verification and use. Avoid rerunning a full exact-orbit audit
    # once per candidate realisation.
    if len(star.neighbours)!=exact_neighbour_count(Q):
        return {'status':'NO','reason':'exact neighbour count','frames':0}
    dimension=len(star.base)
    points=tuple(tuple(arb(x) for x in p) for p in model_full_points(Q,known=True))
    if not points or any(len(p)!=dimension for p in points):
        raise ValueError('known model/star dimension mismatch')
    ns=tuple(Q.neighbours)
    if (not isinstance(Q.base_index,int) or not 0<=Q.base_index<len(points) or
            len(set(ns))!=len(ns) or Q.base_index in ns or
            any(not isinstance(i,int) or not 0<=i<len(points) for i in ns)):
        raise ValueError('invalid known-model base/neighbour indices')
    point_index=PointIndex(points)
    src=[sub(p,star.centre) for p in star.neighbours]
    # Base plus D-1 neighbours span D dimensions; VF directions span D-1.
    from itertools import combinations
    ids=None;Ui=None
    for proposal in combinations(range(len(src)),dimension-1):
        U=columns([sub(star.base,star.centre)]+[src[i] for i in proposal])
        if U.det()>0 or U.det()<0:
            Ui=inverse(U);ids=proposal;break
    if ids is None: raise Undecided('no certified full known-comparison frame')
    anchors=[star.base]+[star.neighbours[i] for i in ids]
    dist=[[norm2(sub(a,b)) for b in anchors] for a in anchors]
    frames=0;unresolved=0
    full=[p for f in star.facets for p in f.points]
    def visit(chosen,available):
        nonlocal frames,unresolved
        k=len(chosen)
        if k==dimension:
            frames+=1
            if frame_limit is not None and frames>frame_limit:
                raise Undecided('known-comparison frame limit')
            V=columns([points[i] for i in chosen]);A=V*Ui
            for p in full:
                moved=apply(A,sub(p,star.centre))
                if all(apart(moved,points[j]) for j in point_index.candidates(moved)): return False
            unresolved+=1
            return True
        for j in available:
            # Rejection uses only certified interval squared-distance
            # disjointness; every true anchor congruence remains.
            if any((norm2(sub(points[j],points[chosen[t]]))-dist[k][t])>0 or
                   (norm2(sub(points[j],points[chosen[t]]))-dist[k][t])<0
                   for t in range(k)):
                continue
            if visit(chosen+[j],[v for v in available if v!=j]): return True
        return False
    possible=visit([Q.base_index],list(ns))
    return {'status':'POSSIBLE' if possible else 'NO','frames':frames,
            'unresolved_frames':unresolved,
            'reason':'surviving interval frame is consistency only' if possible else 'all frames strictly excluded'}


def identify_by_elimination(realisations,known,interval,allowed_types,coverage_complete,frame_limit=None):
    """Return rigorous assignment only after complete S2/orientation coverage.

    `realisations` must already be EXACT congruence classes; grouping by
    numerical overlap, a signature alone, or rounded keys is forbidden.
    One realisation may have multiple constructed names.
    """
    result={i:[] for i in range(len(realisations))};reported=[]
    if not coverage_complete:
        return {'status':'OPEN','reason':'realisation coverage incomplete','identified':result}
    lo,hi=map(arb,interval)
    for Q in known:
        try:
            # Radius2 is a certified construction enclosure supplied by the
            # model API. Avoid expanding every full5D orbit in every class.
            r=arb(Q.radius2).sqrt()
            if r<lo or r>hi:
                reported.append({'name':Q.name,'status':'OUTSIDE'});continue
            if not r>lo or not r<hi:
                raise Undecided('known radius not certified strictly inside class')
            if not set(Q.facet_types).issubset(set(allowed_types)):
                reported.append({'name':Q.name,'status':'OUTSIDE-LIBRARY'});continue
            if not Q.certify_known_model(): raise Undecided('model certificate absent')
            # Logical elimination: a certified Q MUST appear in this complete
            # class. Count mismatches are exact construction contradictions.
            # Once only one class remains, no frame consistency check is
            # required: it cannot change the identification proof.
            count=exact_neighbour_count(Q)
            checks=[({'status':'NO','reason':'exact neighbour count','frames':0}
                     if len(s.neighbours)!=count else
                     {'status':'UNTESTED','reason':'awaiting elimination','frames':0})
                    for s in realisations]
            possible=[i for i,c in enumerate(checks) if c['status']!='NO']
            for i in tuple(possible):
                if len(possible)<=1: break
                checks[i]=_exclude_certified_known(realisations[i],Q,frame_limit)
                if checks[i]['status']=='NO': possible.remove(i)
            if len(possible)==1 and checks[possible[0]]['status']=='UNTESTED':
                checks[possible[0]]={'status':'SOLE-REMAINING',
                    'reason':'certified Q exists in this complete class; all other realisations excluded',
                    'frames':0}
            if not possible:
                # Q itself must be in a complete class: this signals an
                # inconsistent model/search contract, NOT a classification.
                raise Undecided('known model excluded from every complete realisation')
            if len(possible)==1:
                result[possible[0]].append(Q.name)
                status='IDENTIFIED-BY-ELIMINATION'
            else: status='OPEN'
            reported.append({'name':Q.name,'status':status,'possible':possible,'checks':checks})
        except Undecided as e:
            reported.append({'name':Q.name,'status':'OPEN','reason':str(e)})
    return {'status':'COMPLETE' if all(c['status']!='OPEN' for c in reported) else 'OPEN',
            'identified':result,'known':reported}
