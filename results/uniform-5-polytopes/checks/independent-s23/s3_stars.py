"""Full facet stars, complete neighbour candidates, exact star symmetries.

The model layer is an explicit mathematical trust boundary: its certified
full symmetry permutations are construction facts. Coordinate overlap is
never used to certify one of these permutations.
"""
from dataclasses import dataclass
from functools import lru_cache
from itertools import combinations
from flint import arb, arb_mat
from geometry import Undecided, Impossible, add, sub, norm2, dot, scale
from s3_grid import PointIndex
from s3_arith import (columns, inverse, independent, apply, finite,
                      conditional_same, apart, perfect_matching, frobenius_upper)


@dataclass
class PlacedFacet:
    name: str
    points: tuple                 # in MODEL full vertex order
    # Present only for full facets produced by reconstruct_star and carried
    # through transform_star: one affine image of this certified model.
    affine_model: object=None
    affine_anchors: tuple=()

@dataclass
class Star:
    base: tuple
    centre: tuple
    neighbours: tuple
    facets: tuple
    vf_state: object=None


def model_full_points(model, *, known=False):
    """Generic full coordinates, with the original provider names accepted.

    Names points4/points5 are historical API names, not dimension evidence.
    Exact construction certification stays the provider's responsibility.
    """
    fields=('points_full','points5','points4') if known else ('points_full','points4','points3')
    for field in fields:
        try:
            return getattr(model,field)
        except AttributeError:
            continue
    raise Undecided(f'{model.name}: missing full model coordinates')


@lru_cache(maxsize=256)
def model_geometry(m):
    for field in ('base_index','neighbours'):
        if not hasattr(m,field): raise Undecided(f'{m.name}: missing S3 model field {field}')
    points=tuple(tuple(arb(x) for x in p) for p in model_full_points(m))
    dimension=len(points[0]) if points else 0
    if dimension<2 or any(len(p)!=dimension for p in points):
        raise ValueError('full facet model must have a consistent intrinsic dimension')
    base=m.base_index;neighbours=tuple(m.neighbours)
    if not isinstance(base,int) or not 0<=base<len(points):
        raise ValueError('invalid full facet base index')
    if (len(set(neighbours))!=len(neighbours) or base in neighbours or
            any(not isinstance(i,int) or not 0<=i<len(points) for i in neighbours)):
        raise ValueError('invalid full facet neighbour indices')
    return points,base,neighbours


@lru_cache(maxsize=512)
def model_symmetries(m,target):
    """Provider contract: ALL exact full-vertex metric permutations base->target.

    symmetries_to is a certified mathematical model routine, not a list of
    fitted matrices. Its implementation must prove soundness/completeness
    by exact algebraic Gram tests. The optional older explicit certificate
    API is also accepted. Absent proofs must raise Undecided.
    """
    points,b,_=model_geometry(m)
    if hasattr(m,'symmetries_to'):
        perms=m.symmetries_to(target)
    else:
        for field in ('full_symmetries','verify_full_symmetry','certify_full_symmetry_completeness'):
            if not hasattr(m,field): raise Undecided(f'{m.name}: missing certified symmetry enumerator')
        if not m.certify_full_symmetry_completeness():
            raise Undecided(f'{m.name}: full symmetry completeness not proved')
        perms=[]
        for p in m.full_symmetries:
            if not m.verify_full_symmetry(p): raise ValueError('rejected exact full symmetry')
            if p[b]==target: perms.append(p)
    result=[]
    for p in perms:
        p=tuple(p)
        if sorted(p)!=list(range(len(points))) or p[b]!=target:
            raise ValueError(f'{m.name}: invalid exact symmetry permutation')
        result.append(p)
    if not result: raise Undecided(f'{m.name}: no certified base->target symmetry')
    return tuple(result)


def reconstruct_star(state,R,models):
    """Paper VF formula; no fitted frame and no free ambient normal sign."""
    R=arb(R)
    if not R>0: raise Undecided('radius not positive')
    vf=tuple(tuple(arb(x) for x in p) for p in state['points'])
    dimension=len(vf[0])+1 if vf else 0
    if dimension<3 or any(len(p)!=dimension-1 for p in vf):
        raise ValueError('inconsistent vertex-figure dimension')
    z=1/(2*R);zero=(arb(0),)*dimension
    neighbours=tuple(p+(z,) for p in vf)
    centre=(arb(0),)*(dimension-1)+(R,)
    facets=[]
    for f in state['facets']:
        m=models[f['name']];points,b,ns=model_geometry(m)
        if len(points[0])!=dimension-1: raise ValueError('facet/VF dimension mismatch')
        if len(ns)!=len(f['map']): raise ValueError('VF neighbour order mismatch')
        if len(set(f['map']))!=len(f['map']): raise Impossible('collapsed full facet neighbour map')
        if any(not isinstance(i,int) or not 0<=i<len(neighbours) for i in f['map']):
            raise ValueError('full facet neighbour map index out of range')
        edges=[sub(points[i],points[b]) for i in ns]
        ids=independent(edges,dimension-1)
        A=columns([edges[i] for i in ids])
        B=columns([neighbours[f['map'][i]] for i in ids])
        L=B*inverse(A)
        # S2's certified template placement guarantees the exact isometry.
        # These rejection-only guards catch corrupted archived maps.
        G=L.transpose()*L
        if any(not (G[i,j]-int(i==j)).contains(0) for i in range(dimension-1) for j in range(dimension-1)):
            raise Impossible('full facet anchor Gram mismatch')
        pp=tuple(apply(L,sub(p,points[b])) for p in points)
        for i,j in enumerate(ns):
            if apart(pp[j],neighbours[f['map'][i]]):
                raise Impossible('corrupted full facet neighbour map')
        facets.append(PlacedFacet(f['name'],pp,m,tuple([b]+[ns[i] for i in ids])))
    return Star(zero,centre,neighbours,tuple(facets),state)


def facet_compatible(a,b,point_index=None):
    """Necessary condition only, no equality claim across candidate stars.

    Use unconditional apartness and a COMPLETE matching. Unknown pairs
    remain edges. A failed matching alone certifies incompatibility.
    """
    if a.name!=b.name or len(a.points)!=len(b.points): return False
    if point_index is None:point_index=PointIndex(b.points)
    graph=[[j for j in point_index.candidates(p) if not apart(p,b.points[j])] for p in a.points]
    return perfect_matching(graph,len(b.points)) is not None


def contains_known(candidate, known):
    indices={}
    def compatible(a,j,b):
        if a.name!=b.name or len(a.points)!=len(b.points):return False
        if j not in indices:indices[j]=PointIndex(b.points)
        return facet_compatible(a,b,indices[j])
    graph=[[j for j,b in enumerate(candidate.facets) if compatible(a,j,b)] for a in known]
    return perfect_matching(graph,len(candidate.facets)) is not None


def transform_star(star,g):
    O=star.centre
    move=lambda p:add(O,apply(g,sub(p,O)))
    return Star(move(star.base),O,tuple(move(p) for p in star.neighbours),
                tuple(PlacedFacet(f.name,tuple(move(p) for p in f.points),
                                  f.affine_model,f.affine_anchors) for f in star.facets))


def candidate_maps(star,w,known,models):
    """All isometries moving base to w and one star facet onto known[0].

    Every map fixes the circumcentre. Model permutations taking the source
    base to target vertex enumerate ALL facet isometries, by the model
    completeness certificate. No floating filters or candidate de-dup.
    """
    if not known: raise Undecided('no known facet through target vertex')
    dimension=len(star.base)
    target=known[0];m=models[target.name]
    _,b,ns=model_geometry(m)
    target_ids=[]
    for j,p in enumerate(target.points):
        if conditional_same(w,p): target_ids.append(j)
    if len(target_ids)!=1: raise Undecided('target vertex not uniquely located in known facet')
    j=target_ids[0]
    # Source base, D-1 independent edges, and centre determine the full map.
    for source in star.facets:
        if source.name!=target.name: continue
        edges=[sub(source.points[i],source.points[b]) for i in ns]
        ids=independent(edges,dimension-1)
        anchors=[ns[i] for i in ids]
        U=columns([sub(source.points[i],star.centre) for i in [b]+anchors])
        Ui=inverse(U)
        for perm in model_symmetries(m,j):
            V=columns([sub(target.points[perm[i]],star.centre) for i in [b]+anchors])
            g=V*Ui
            # This is an exact isometry by construction (facet isometry and
            # fixed centre outside facet); guard only rejects corruption.
            H=g.transpose()*g
            if any(not (H[a,c]-int(a==c)).contains(0) for a in range(dimension) for c in range(dimension)):
                raise Impossible('candidate full-frame Gram mismatch')
            yield g


def correspondence_isomorphisms(state,target,models,node_limit=None,first_only=False):
    """Full-star congruences at one fixed radius, proved by Lemma D.

    Only model full-facet stabilizers are allowed; this preserves chiral
    full-star orientation, as required for elimination and forcing.
    """
    fs=state['facets'];ts=target['facets'];points=state['points'];n=len(points)
    if len(fs)!=len(ts) or n!=len(target['points']): return []
    options=[]
    for f in fs:
        m=models[f['name']];_,b,ns=model_geometry(m)
        invns={v:i for i,v in enumerate(ns)}
        stabilizers=[]
        for p in model_symmetries(m,b):
            if p[b]==b:
                try: stabilizers.append(tuple(invns[p[v]] for v in ns))
                except KeyError as exc: raise ValueError('symmetry violates exact neighbour set') from exc
        opt=[]
        for j,t in enumerate(ts):
            if f['name']!=t['name']: continue
            for p in stabilizers:
                opt.append((j,dict(zip(f['map'],[t['map'][p[k]] for k in range(len(ns))],strict=True))))
        options.append(opt)
    seen=set();answer=[];nodes=0
    def visit(mapping,used,remaining):
        nonlocal nodes
        if first_only and answer: return
        nodes+=1
        if node_limit is not None and nodes>node_limit:
            raise Undecided('automorphism resource limit')
        if not remaining:
            if len(mapping)!=n: raise Undecided('VF point not covered by facets')
            p=tuple(mapping[i] for i in range(n))
            if p not in seen: seen.add(p);answer.append(p)
            return
        def compatible(f):
            return [(j,q) for j,q in options[f] if j not in used
                    and all(a not in mapping or mapping[a]==v for a,v in q.items())
                    and all(v not in mapping.values() or mapping.get(a)==v for a,v in q.items())]
        f=min(remaining,key=lambda i:len(compatible(i)))
        for j,q in compatible(f): visit(mapping|q,used|{j},remaining-{f})
    visit({},set(),set(range(len(fs))))
    return answer


def star_automorphisms(star,models,node_limit=None,allowed_permutations=None):
    """Exact subgroup from full-facet correspondence automorphisms.

    Lemma D supplies exact isometry; full-model permutations fix full
    facets. No completeness assumption on this subgroup is needed.
    """
    state=star.vf_state
    if state is None: raise Undecided('exact star correspondences unavailable')
    points=state['points']
    answer=correspondence_isomorphisms(state,state,models,node_limit)
    if allowed_permutations is not None:
        requested={tuple(p) for p in allowed_permutations}
        if not requested<=set(answer):
            raise ValueError('unproved star symmetry permutation requested')
        answer=[p for p in answer if p in requested]
    dimension=len(star.base)
    ids=independent(points,dimension-1);U=inverse(columns([points[i] for i in ids]))
    result=[]
    for p in answer:
        A=columns([points[p[i]] for i in ids])*U
        M=arb_mat(dimension,dimension)
        for i in range(dimension-1):
            for j in range(dimension-1): M[i,j]=A[i,j]
        M[dimension-1,dimension-1]=1
        result.append(M)
    return result


def _local_uniqueness_one_step(star,models,symmetry_permutations=None,node_limit=None):
    """Rigorous coset proof from the paper, no overlap-based star merging."""
    # Optional controls may WEAKEN the proved group using integer VF
    # permutations. Raw matrices are never accepted as symmetry proofs.
    automorphisms=star_automorphisms(star,models,node_limit,symmetry_permutations)
    R=positive_radius(star)
    witnesses=[]
    for wi,w in enumerate(star.neighbours):
        known=[]
        for f in star.facets:
            if any(conditional_same(w,p) for p in f.points): known.append(f)
        kept=[];excluded=0
        for g in candidate_maps(star,w,known,models):
            candidate=transform_star(star,g)
            if contains_known(candidate,known): kept.append(g)
            else: excluded+=1
        if not kept: raise Impossible('no candidate neighbour star contains known facets')
        g1=kept[0];epsilon=arb(0)
        for g in kept:
            bounds=[frobenius_upper(g1*t-g) for t in automorphisms]
            if not bounds: raise Undecided('empty exact star symmetry subgroup')
            bound=min(bounds)
            if not 2*R*bound<arb(1)/2:
                raise _CosetAmbiguity(f'neighbour {wi}: surviving candidates not certified one coset')
            if bound>epsilon: epsilon=bound
        witnesses.append({'neighbour':wi,'kept':len(kept),'excluded':excluded,
                          'coset_bound':str((2*R*epsilon).upper())})
    return {'status':'FORCED','neighbours':witnesses,'exact_star_symmetries':len(automorphisms)}


class _CosetAmbiguity(Undecided):
    """The complete root-compatible candidate set has several possible cosets."""


def _cross_star_separation(candidate,known):
    """Rejection witness conditional on both stars belonging to the same P.

    `known` is either the root star or a star already proved forced from it.
    Candidate vertices become vertices of P only under the candidate hypothesis.
    An unresolved distance retains the candidate.
    """
    from geometry import encode_ball
    for fi,a in enumerate(candidate.facets):
        for fj,b in enumerate(known.facets):
            for i,p in enumerate(a.points):
                for j,q in enumerate(b.points):
                    d=norm2(sub(p,q))
                    if d.is_finite() and d>0 and d<1:
                        return {'candidate_facet':fi,'known_facet':fj,
                                'model_vertices':[i,j],
                                'squared_distance':encode_ball(d),
                                'reason':'separation 0<distance²<1 against a forced star'}
    return None


def _collar_known_facets(star,forced,w):
    """Necessary facets at w, with the development code's distinctness test.

    Every input star is already forced under the SAME root hypothesis.
    Conditional vertex identity may raise Undecided/Impossible; neither is
    converted into a guessed incidence. Uncertain facet duplicates are omitted.
    """
    known=[]
    for source,known_star in [(None,star)]+list(forced.items()):
        for fi,f in enumerate(known_star.facets):
            if any(conditional_same(w,p) for p in f.points):known.append((source,fi,f))
    # EXACT same provably-distinct subset criterion as s3_develop.develop.
    from s3_arith import apart
    distinct=[];sources=[]
    for source,fi,f in known:
        if all(any(all(apart(p,q) for q in g.points) for p in f.points) or
               any(all(apart(q,p) for p in f.points) for q in g.points)
               for g in distinct):
            distinct.append(f);sources.append({'forced_neighbour':source,'facet':fi})
    return distinct,sources


def _collar_facet_obstruction(candidate,known,sources):
    """A failed COMPLETE matching is necessary rejection, never equality."""
    if contains_known(candidate,known):return None
    # Export the same complete possible-incidence graph as a small witness.
    from s3_arith import perfect_matching
    graph=[[j for j,b in enumerate(candidate.facets) if facet_compatible(a,b)]
           for a in known]
    if perfect_matching(graph,len(candidate.facets)) is not None:
        raise ValueError('known-facet matching witness disagrees with contains_known')
    return {'kind':'known-facet-matching','reason':'no complete matching of forced known facets',
            'known_facet_sources':sources,'possible_incidence_graph':graph,
            'candidate_facets':len(candidate.facets)}


def _propagate_one_star(star,models,forced,automorphisms,R,max_targets=4):
    """Force one additional star, conditional on the same common root P.

    Always use the ORIGINAL root star as source of candidate_maps and its
    exact automorphisms. A moved star's unchanged vf_state is not a frame
    certificate for invoking local_uniqueness on that moved star.
    Uncertainty while testing an optional frontier target records/skips it;
    uncertainty in the earlier identity/deduplication scan returns OPEN.
    Neither eliminates a required continuation. A finite cap returns OPEN.
    """
    from geometry import encode_ball
    targets=[]
    for source,known_star in forced.items():
        for ni,w in enumerate(known_star.neighbours):
            if any(conditional_same(w,p) for p in (star.base,)+tuple(star.neighbours)):continue
            if any(conditional_same(w,s.base) for s in forced.values()):continue
            if any(conditional_same(w,t[2]) for t in targets):continue
            try:required,sources=_collar_known_facets(star,forced,w)
            except Undecided:continue
            if required:targets.append((source,ni,w,required,sources))
    targets.sort(key=lambda t:-len(t[3]))
    attempts=[]
    for source,ni,w,required,sources in targets[:max_targets]:
        kept=[];excluded=[];raw=0
        try:
            for ci,g in enumerate(candidate_maps(star,w,required,models)):
                raw+=1;candidate=transform_star(star,g);witness=None;origin=None
                for origin,known in [(None,star)]+list(forced.items()):
                    witness=_cross_star_separation(candidate,known)
                    if witness is not None:break
                if witness is None:witness=_collar_facet_obstruction(candidate,required,sources)
                if witness is None:kept.append((ci,g,candidate))
                elif witness.get('kind')=='known-facet-matching':excluded.append({'candidate':ci,'witness':witness})
                else:excluded.append({'candidate':ci,'forced_neighbour':origin,'witness':witness})
        except Undecided as exc:
            attempts.append({'source_star':source,'source_neighbour':ni,'status':'OPEN','reason':str(exc)})
            continue
        if not kept:raise Impossible('additional forced vertex has no compatible star')
        g1=kept[0][1];epsilon=arb(0);same=True
        for _,g,_ in kept:
            bounds=[frobenius_upper(g1*t-g) for t in automorphisms]
            if not bounds:raise Undecided('empty exact star symmetry subgroup')
            bound=min(bounds)
            if not 2*R*bound<arb(1)/2:same=False;break
            if bound>epsilon:epsilon=bound
        if not same:
            attempts.append({'source_star':source,'source_neighbour':ni,'status':'OPEN',
                             'raw_candidates':raw,'kept_candidates':[ci for ci,_,_ in kept]})
            continue
        proof={'source_star':source,'source_neighbour':ni,'vertex':[encode_ball(x) for x in w],
               'prior_forced_stars':list(forced),'required_facet_sources':sources,
               'raw_candidates':raw,'exclusions':excluded,'kept_candidates':[ci for ci,_,_ in kept],
               'representative':kept[0][0],'coset_bound':str((2*R*epsilon).upper()),
               'earlier_open_targets':attempts}
        return kept[0][2],proof
    raise Undecided('additional-star propagation found no one-coset target among '+str(min(len(targets),max_targets))+' tested vertices')


def _local_uniqueness_collar(star,models,symmetry_permutations=None,node_limit=None):
    """Force a finite collar, using only consequences of the common root star.

    Induction invariant: every stored forced star is the same in EVERY uniform
    P realising the root star. At an unresolved neighbour all true congruences
    occur among candidate_maps and survive contains_known. A candidate can be
    excluded only by strict separation or failed complete matching of the
    already-forced facets through that neighbour. If the remaining
    maps pass the original coset proof, their common star is therefore forced
    and can be added to the collar. Root-neighbour steps occur at most once
    per root neighbour; a stalled root collar may add at most two extra
    forced stars, testing at most four frontier targets per addition. If these
    bounded tests make no progress the result is OPEN. No known-Q coordinates enter.
    """
    automorphisms=star_automorphisms(star,models,node_limit,symmetry_permutations)
    R=positive_radius(star)
    pending={};counts={}
    for wi,w in enumerate(star.neighbours):
        known=[f for f in star.facets if any(conditional_same(w,p) for p in f.points)]
        kept=[];excluded=0;raw=0
        for ci,g in enumerate(candidate_maps(star,w,known,models)):
            raw+=1
            candidate=transform_star(star,g)
            if contains_known(candidate,known):kept.append((ci,g,candidate))
            else:excluded+=1
        if not kept:raise Impossible('no candidate neighbour star contains known facets')
        pending[wi]=kept
        counts[wi]={'raw_candidates':raw,'root_excluded':excluded}
    forced={};steps=[];exclusions={wi:[] for wi in pending};propagation_steps=[]
    # A bounded work unit: each added non-root star is a rigorous consequence,
    # not a promise of unlimited propagation or a completeness assertion.
    max_extra_stars=2
    while pending:
        progress=False
        for wi in list(pending):
            kept=[];required=None;required_sources=None
            for ci,g,candidate in pending[wi]:
                witness=None;source=None
                # Root-only separation is necessary as well. The key None
                # denotes the root, rather than a propagated neighbour.
                for source,known in [(None,star)]+list(forced.items()):
                    witness=_cross_star_separation(candidate,known)
                    if witness is not None:break
                # Keep separation first, preserving its existing witnesses.
                # An actual continuation must contain ALL already-forced
                # facets through this neighbour, up to a complete matching.
                if witness is None:
                    if required is None:
                        required,required_sources=_collar_known_facets(star,forced,star.neighbours[wi])
                    witness=_collar_facet_obstruction(candidate,required,required_sources)
                if witness is None:kept.append((ci,g,candidate))
                elif witness.get('kind')=='known-facet-matching':
                    exclusions[wi].append({'candidate':ci,'witness':witness})
                else:
                    exclusions[wi].append({'candidate':ci,'forced_neighbour':source,
                                          'witness':witness})
            pending[wi]=kept
            if not kept:raise Impossible('all neighbour candidates contradict forced stars')
            g1=kept[0][1];epsilon=arb(0);same_coset=True
            for _,g,_ in kept:
                bounds=[frobenius_upper(g1*t-g) for t in automorphisms]
                if not bounds:raise Undecided('empty exact star symmetry subgroup')
                bound=min(bounds)
                if not 2*R*bound<arb(1)/2:
                    same_coset=False;break
                if bound>epsilon:epsilon=bound
            if not same_coset:continue
            steps.append({'neighbour':wi,'prior_forced_neighbours':list(forced),
                          **counts[wi],'collar_exclusions':exclusions[wi],
                          'kept_candidates':[ci for ci,_,_ in kept],
                          'representative':kept[0][0],
                          'kept':len(kept),
                          'excluded':counts[wi]['root_excluded']+len(exclusions[wi]),
                          'coset_bound':str((2*R*epsilon).upper())})
            forced[wi]=kept[0][2]
            del pending[wi];progress=True
        if not progress:
            if len(propagation_steps)>=max_extra_stars:
                raise Undecided('additional-star propagation bound reached; unresolved root neighbours '+','.join(map(str,pending)))
            extra,proof=_propagate_one_star(star,models,forced,automorphisms,R)
            key=len(star.neighbours)+len(propagation_steps)
            proof['forced_star_id']=key;propagation_steps.append(proof)
            forced[key]=extra
    result={'status':'FORCED','method':'forced-neighbour-collar',
            'neighbours':steps,'exact_star_symmetries':len(automorphisms)}
    if propagation_steps:
        result.update(method='propagated-star-collar',propagation_steps=propagation_steps,
                      forcing_order=list(forced))
    return result


def local_uniqueness(star,models,symmetry_permutations=None,node_limit=None):
    """Original coset test, then a certified finite forced-neighbour collar.

    The original fast path and its output are unchanged when it succeeds.
    Uncertainty outside a genuine coset ambiguity is not caught or weakened.
    """
    try:
        return _local_uniqueness_one_step(star,models,symmetry_permutations,node_limit)
    except _CosetAmbiguity:
        return _local_uniqueness_collar(star,models,symmetry_permutations,node_limit)


def positive_radius(star):
    r2=norm2(sub(star.base,star.centre))
    if not r2>0: raise Undecided('nonpositive radius')
    return r2.sqrt()


def separation_obstruction(star,facet_names=None):
    """Optional rejection-only search across full facets of one star.

    A returned witness is an unconditional contradiction under the hypothesis
    that this star belongs to one unit-edge uniform P. Returning None makes
    NO claim about equality or separation of unexamined/uncertain pairs.
    Only pairs with an endpoint in facet_names are examined when supplied.
    """
    from geometry import encode_ball
    for fi,a in enumerate(star.facets):
        for fj,b in enumerate(star.facets[:fi]):
            if facet_names is not None and a.name not in facet_names and b.name not in facet_names:
                continue
            for i,p in enumerate(a.points):
                for j,q in enumerate(b.points):
                    d=norm2(sub(p,q))
                    if d.is_finite() and d>0 and d<1:
                        return {'facets':[fi,fj],'model_vertices':[i,j],
                                'squared_distance':encode_ball(d),
                                'reason':'separation 0<distance²<1 in full star'}
    return None
