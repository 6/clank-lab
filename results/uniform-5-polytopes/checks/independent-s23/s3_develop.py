"""Exhaustive development: unknowns NEVER become dead branches.

Only a proved candidate-coset anchor reduction shares branches. Finite
all-dead search trees are refutations; any uncertain surviving branch is OPEN.
"""
from flint import arb,arb_mat
from geometry import Undecided, Impossible, sub, norm2,encode_ball
from s3_arith import conditional_same,frobenius_upper,columns,inverse,independent,finite
from s3_stars import (Star,PlacedFacet,candidate_maps,transform_star,contains_known,
                      facet_compatible,star_automorphisms,positive_radius,model_geometry)


def merge_candidate(points,facets,candidate):
    newpoints=list(points)
    for f in candidate.facets:
        for p in f.points:
            matches=[i for i,q in enumerate(newpoints) if conditional_same(p,q)]
            if len(matches)>1: raise Impossible('candidate collapses known vertices')
            if not matches: newpoints.append(p)
    # Duplicates of facets are safe to retain. They cannot prune a branch;
    # do not make any unproved equality decision about candidate maps.
    return newpoints,list(facets)+list(candidate.facets)


def _support_plane(facet,centre,models):
    """Necessary supporting plane of one PROVEN common affine model image.

    reconstruct_star constructs every full facet by one affine map of a
    certified intrinsic (D-1)-dimensional model; transform_star composes a
    common isometry and preserves that provenance. Independent source
    anchors and O outside their plane give D independent ambient vectors.
    Missing provenance/uncertain span/intervals cannot authorize a cut.
    """
    model=models.get(facet.name)
    if model is None or facet.affine_model is not model:return None
    try:
        source,b,ns=model_geometry(model);dimension=len(centre)
        if (len(source)!=len(facet.points) or not source or
                len(source[0])!=dimension-1 or
                any(len(p)!=dimension for p in facet.points)):return None
        ids=independent([sub(source[j],source[b]) for j in ns],dimension-1)
        anchors=tuple([b]+[ns[i] for i in ids])
        if facet.affine_anchors!=anchors:return None
        matrix=columns([sub(facet.points[j],centre) for j in anchors]).transpose()
        normal=inverse(matrix)*arb_mat([[1] for _ in anchors])
        # Rejection guards only. Exact coplanarity follows from the common
        # affine model-image provenance, NEVER from these zero overlaps.
        for p in facet.points:
            value=finite(sum((normal[j,0]*(p[j]-centre[j])
                              for j in range(dimension)),arb(0)))
            if not (value-1).contains(0):return None
        return tuple(normal[j,0] for j in range(dimension)),anchors
    except (Undecided,ValueError,ZeroDivisionError):
        return None


def support_obstruction(points,facets,centre,models,previous=None):
    """Incremental strict convex-support check, with exported interval proof.

    Under ANY actual continuation, branch facets and points belong to one
    convex P and its sphere centre O is interior. Each facet plane is
    normalized to value1 and O has value0. Only finite value>1 rejects.
    previous is private path-local cache (point count, proved facet planes).
    Every new-point/old-plane and every point/new-plane pair is checked.
    """
    old_points,old_planes=(0,()) if previous is None else previous
    planes=list(old_planes)
    for fi in range(len(old_planes),len(facets)):
        proof=_support_plane(facets[fi],centre,models)
        planes.append(proof)
    for fi,proof in enumerate(planes):
        if proof is None:continue
        normal,anchors=proof
        for pi in range(old_points if fi<len(old_planes) else 0,len(points)):
            p=points[pi]
            try:
                value=finite(sum((a*(x-o) for a,x,o in
                                  zip(normal,p,centre,strict=True)),arb(0)))
            except (Undecided,ValueError):continue
            if value>1:
                facet=facets[fi]
                witness={'reason':'convex supporting facet excludes branch vertex',
                         'facet':fi,'facet_type':facet.name,'vertex':pi,
                         'anchor_model_indices':list(anchors),
                         'facet_points':[[encode_ball(x) for x in q] for q in facet.points],
                         'anchor_points':[[encode_ball(x) for x in facet.points[j]] for j in anchors],
                         'point':[encode_ball(x) for x in p],
                         'centre':[encode_ball(x) for x in centre],
                         'normal':[encode_ball(x) for x in normal],
                         'signed_value':encode_ball(value),
                         'affine_provenance':'certified full model affine image from reconstruct_star/transform_star'}
                return witness,(len(points),tuple(planes))
    return None,(len(points),tuple(planes))


def _coset_witness(g,representatives,automorphisms,R):
    """A proved relation to ONE representative, or no reduction.

    The caller derives automorphisms from exact facet correspondences. A
    small norm alone does not assert that candidate vertices belong to P.
    See controls/d4/DEVELOPMENT_COSETS.md for the anchor argument.
    """
    for ci,representative in representatives:
        for ti,tau in enumerate(automorphisms):
            try:
                bound=2*R*frobenius_upper(representative*tau-g)
                if bound<arb(1)/2:
                    return {'representative':ci,'automorphism':ti,
                            'bound_2R':str(bound.upper())}
            except Undecided:
                # An unproved relation leaves the candidate in the search.
                continue
    return None


def develop(star,models,max_depth=3,node_limit=None,root_forced=False,
            coset_reduction=True,support_pruning=True):
    # Only internally proved full-star automorphisms are eligible. Failure
    # to construct them weakens this optimization to exhaustive branching.
    automorphisms=[];R=None
    if coset_reduction:
        try:
            proved=star_automorphisms(star,models,node_limit)
            radius=positive_radius(star)
        except Undecided:
            pass
        else:
            automorphisms=proved;R=radius
    stats={'nodes':0,'candidates':0,'excluded':0,'dead':0,'open':0}
    if coset_reduction:stats['coset_duplicates']=0
    if support_pruning:stats['support_excluded']=0
    reasons=[];witnesses=[];support_witnesses=[]
    points=[]
    def visit(points,facets,done,depth,support_cache=None):
        stats['nodes']+=1
        if node_limit is not None and stats['nodes']>node_limit:
            raise Undecided('development node limit')
        frontier=[(i,p) for i,p in enumerate(points) if i not in done]
        if not frontier:
            raise Undecided('closed development requires separate global model proof')
        if depth>=max_depth: raise Undecided('development depth limit')
        from s3_arith import apart
        # Heuristic ordering only: interval overlap merely counts possible
        # incidences and NEVER removes a vertex/candidate or proves equality.
        distinct_all=[]
        for f in facets:
            if all(any(all(apart(p,q) for q in g.points) for p in f.points) or
                   any(all(apart(q,p) for p in f.points) for q in g.points)
                   for g in distinct_all): distinct_all.append(f)
        wi,w=max(frontier,key=lambda ip:sum(any(not apart(ip[1],p) for p in f.points) for f in distinct_all))
        known=[]
        for f in facets:
            if any(conditional_same(w,p) for p in f.points): known.append(f)
        # A set of known facets may contain duplicate descriptions; using
        # duplicates in the matching would falsely exclude candidates.
        # Choose an inclusion-maximal provably distinct subset. Two facets
        # are provably different if some vertex is apart from every vertex
        # of the other; undecided pairs are simply not both imposed here.
        from s3_arith import apart
        distinct=[]
        for f in known:
            if all(any(all(apart(p,q) for q in g.points) for p in f.points) or
                   any(all(apart(q,p) for p in f.points) for q in g.points)
                   for g in distinct): distinct.append(f)
        known=distinct
        if not known: raise Undecided('no certified known facet through frontier vertex')
        # If the rigorously completed LU coset proof applies at this ROOT
        # neighbour, all root-compatible candidates give the same full star
        # conditional on existence of P. Choosing one representative is a
        # theorem-based reduction, not interval-based competing-star merging.
        forced=root_forced and any(conditional_same(w,q) for q in star.neighbours)
        root_known=[]
        if forced:
            root_known=[f for f in star.facets if any(conditional_same(w,p) for p in f.points)]
        anchor_known=root_known if forced else known
        kept=0;branch_open=False;candidate_count=0;representatives=[];reductions=[]
        for g in candidate_maps(star,w,anchor_known,models):
            stats['candidates']+=1;candidate_count+=1
            try:
                moved=transform_star(star,g)
                if forced and not contains_known(moved,root_known):
                    stats['excluded']+=1;continue
                if not contains_known(moved,known):
                    stats['excluded']+=1
                    if forced: break
                    continue
                # At this frontier known[0] is a genuine facet under every
                # actual continuation of this branch. candidate_maps sends
                # its selected source-facet anchors into that known facet.
                # Hence the coset anchor theorem applies off-root as well.
                relation=(_coset_witness(g,representatives,automorphisms,R)
                          if automorphisms else None)
                if relation is not None:
                    reductions.append(dict(relation,candidate=candidate_count-1))
                    stats['coset_duplicates']+=1
                    continue
                pp,ff=merge_candidate(points,facets,moved)
                next_support=support_cache
                if support_pruning:
                    obstruction,next_support=support_obstruction(pp,ff,star.centre,models,support_cache)
                    if obstruction is not None:
                        support_witnesses.append(dict(obstruction,depth=depth+1,
                                                      candidate=candidate_count-1,
                                                      frontier_vertex=wi))
                        stats['support_excluded']+=1;stats['excluded']+=1
                        if forced:break
                        continue
                representatives.append((candidate_count-1,g))
                kept+=1
                if not visit(pp,ff,done|{wi},depth+1,next_support):
                    branch_open=True
                if forced: break
            except Impossible:
                stats['excluded']+=1
                if forced: break
            except Undecided as e:
                branch_open=True;stats['open']+=1;reasons.append(str(e))
                if forced: break
        witness={'depth':depth,'vertex':wi,'candidates':candidate_count,'kept':kept,
                 'unknown':branch_open}
        if coset_reduction:witness['coset_reductions']=reductions
        witnesses.append(witness)
        if not branch_open:
            stats['dead']+=1
            return True
        return False
    try:
        for f in star.facets:
            for p in f.points:
                if not any(conditional_same(p,q) for q in points): points.append(p)
        base_ids=[i for i,p in enumerate(points) if conditional_same(p,star.base)]
        if len(base_ids)!=1: raise Undecided('development base not uniquely present')
        initial_support=None
        initial_obstruction=None
        if support_pruning:
            initial_obstruction,initial_support=support_obstruction(points,list(star.facets),star.centre,models)
        if initial_obstruction is not None:
            support_witnesses.append(dict(initial_obstruction,depth=0,candidate=None,frontier_vertex=None))
            stats['support_excluded']+=1;refuted=True
        else:
            refuted=visit(points,list(star.facets),{base_ids[0]},0,initial_support)
    except Undecided as e:
        reasons.append(str(e));stats['open']+=1;refuted=False
    except Impossible as e:
        reasons.append(str(e));refuted=True
    result={'status':'REFUTED' if refuted else 'OPEN','statistics':stats,
            'reasons':sorted(set(reasons)),'tree':witnesses}
    if support_pruning:result['support_witnesses']=support_witnesses
    return result
