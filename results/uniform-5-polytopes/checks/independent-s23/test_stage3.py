"""Focused soundness controls; no production classification comparisons."""
def deepcopy(x):
    if isinstance(x,dict): return {k:deepcopy(v) for k,v in x.items()}
    if isinstance(x,list): return [deepcopy(v) for v in x]
    if isinstance(x,tuple): return tuple(deepcopy(v) for v in x)
    return x

from itertools import permutations,product
from flint import arb,arb_mat,ctx
from geometry import Undecided,Impossible,ball_interval
from s3_arith import perfect_matching,conditional_same,apart
from s3_radius import unique_radius,Dual,closure
from s3_stars import reconstruct_star,star_automorphisms,local_uniqueness,PlacedFacet,Star,contains_known,separation_obstruction
from s3_cycles import closure_cycles
from s3_identify import exclude_known,identify_by_elimination
from s3_develop import develop
from s3_orient import coset_representatives,expand_orientations
from s3_controls import FullSimplexFacet,SimplexKnown,Provider,simplex_class
from stage2 import search_class
from stage3 import check_class,group_states
from audit_stage3 import audit


def raises(kind,fn):
    try: fn()
    except kind: return
    raise AssertionError(f'{kind.__name__} not raised')


def test_matching():
    count=0
    for l in range(5):
        for r in range(5):
            for bits in range(1<<(l*r)):
                graph=[[j for j in range(r) if bits&(1<<(i*r+j))] for i in range(l)]
                brute=any(all(p[i] in graph[i] for i in range(l)) for p in permutations(range(r),l))
                if not ((perfect_matching(graph,r) is not None)==brute):
                    raise AssertionError()
                count+=1
    print('PASS complete matching vs brute force:',count,flush=True)


def main():
    ctx.prec=320
    test_matching()
    S3=list(permutations(range(3)));C3=[(0,1,2),(1,2,0),(2,0,1)]
    if not (len(coset_representatives(S3,C3,3))==2):
        raise AssertionError()
    if not (len(coset_representatives(S3,S3,3))==1):
        raise AssertionError()
    raises(ValueError,lambda:coset_representatives(S3,[(0,1,2),(1,2,0)],3))
    raises(Undecided,lambda:conditional_same((arb(0),),(arb(0,2),)))
    raises(Impossible,lambda:conditional_same((arb(0),),(arb('0.5'),)))
    if not (not apart((arb(0),),(arb(0,'1e-30'),))):
        raise AssertionError()
    m=FullSimplexFacet();models={m.name:m};c=simplex_class()
    s2=search_class(c,models)
    if not (not s2.open_reasons and len(s2.states)==1):
        raise AssertionError()
    state=s2.states[0];R=ball_interval(*c['R'])
    cycles=closure_cycles(state,models)
    root=unique_radius(c['R'],cycles)
    if not (root['status']=='UNIQUE'):
        raise AssertionError(root)
    bad=deepcopy(cycles)
    for b in bad: b['cos_alpha']=[arb(0)]*len(b['d2'])
    if not (unique_radius(c['R'],bad)['status']=='OPEN'):
        raise AssertionError()
    if not (unique_radius(['0.60','0.80'],cycles)['status']=='OPEN'):
        raise AssertionError()
    if not (unique_radius(c['R'],[])['status']=='OPEN'):
        raise AssertionError()
    star=reconstruct_star(state,R,models)
    if not (len(star.facets)==5):
        raise AssertionError()
    # Optional separation scan refutes only strict (0,1) distances. An
    # uncertain tiny interval remains unrefuted, with NO identity claim.
    f0=PlacedFacet(m.name,((arb(0),)*5,))
    f1=PlacedFacet(m.name,((arb('0.5'),)+(arb(0),)*4,))
    forged=Star(star.base,star.centre,star.neighbours,(f0,f1))
    if not (separation_obstruction(forged)['squared_distance']):
        raise AssertionError()
    uncertain=PlacedFacet(m.name,((arb(0,2),)+(arb(0),)*4,))
    if not (separation_obstruction(Star(star.base,star.centre,star.neighbours,(f0,uncertain))) is None):
        raise AssertionError()
    automorphisms=star_automorphisms(star,models)
    if not (len(automorphisms)==120):
        raise AssertionError()
    lu=local_uniqueness(star,models)
    if not (lu['status']=='FORCED'):
        raise AssertionError()
    raises(Undecided,lambda:local_uniqueness(star,models,[tuple(range(5))]))
    raises(ValueError,lambda:local_uniqueness(star,models,[(0,0,0,0,0)]))
    Q=SimplexKnown()
    if not (exclude_known(star,Q)['status']=='POSSIBLE'):
        raise AssertionError()
    ident=identify_by_elimination([star],[Q],c['R'],[m.name],True)
    if not (ident['identified'][0]==[Q.name]):
        raise AssertionError()
    if not (ident['known'][0]['checks'][0]['status']=='SOLE-REMAINING'):
        raise AssertionError()
    # Prove the count-only elimination route never asks for a full orbit.
    class LocalOnly(SimplexKnown):
        def __init__(self):
            self.radius2=arb(5)/12;self.exact_neighbours=tuple(range(5))
        @property
        def points5(self):raise AssertionError('unnecessary full orbit expansion')
        @property
        def neighbours(self):raise AssertionError('unnecessary full index expansion')
    local=LocalOnly()
    wrong_count=Star(star.base,star.centre,star.neighbours[:-1],star.facets)
    by_count=identify_by_elimination([wrong_count,star],[local],c['R'],[m.name],True)
    if not (by_count['identified'][1]==[Q.name]):
        raise AssertionError()
    if not (by_count['known'][0]['checks'][0]['reason']=='exact neighbour count'):
        raise AssertionError()
    if not (by_count['known'][0]['checks'][1]['status']=='SOLE-REMAINING'):
        raise AssertionError()
    if not (exclude_known(wrong_count,local)['status']=='NO'):
        raise AssertionError()
    class Uncertified(LocalOnly):
        def certify_known_model(self):return False
    if not (identify_by_elimination([star],[Uncertified()],c['R'],[m.name],True)['status']=='OPEN'):
        raise AssertionError()
    if not (identify_by_elimination([star],[Q],c['R'],[m.name],False)['status']=='OPEN'):
        raise AssertionError()
    # Unknown development must never become REFUTED, even when another
    # branch could survive. An explicit resource bound is also OPEN.
    if not (develop(star,models,max_depth=0)['status']=='OPEN'):
        raise AssertionError()
    corrupted=deepcopy(state);corrupted['facets'][0]['map'][0]=corrupted['facets'][0]['map'][1]
    raises(Impossible,lambda:reconstruct_star(corrupted,R,models))
    # Greedy matching would wrongly reject this graph; complete matching
    # gives 0->1,1->0. Unknown facet pairs remain graph edges.
    if not (perfect_matching([[0,1],[0]],2)==[1,0]):
        raise AssertionError()
    # Cross-state merging requires full correspondence proof, not signature.
    if not (len(group_states([state,deepcopy(state)],models))==1):
        raise AssertionError()
    altered=deepcopy(state);altered['facets'][0]['name']='forged'
    altered['signature']={'facets':['forged'],'cycles':[]}
    if not (len(group_states([state,altered],models))==2):
        raise AssertionError()
    result=check_class(s2.record(include_states=True),Provider(),[Q.name])
    if not (result['status']=='COMPLETE'):
        raise AssertionError(result)
    if not (result['realisations'][0]['status']=='KNOWN'):
        raise AssertionError()
    class TypePreflightProvider(Provider):
        def known_facet_types(self,name):return (m.name,) if name==Q.name else ('outside-library',)
        def known(self,name):
            if name!=Q.name:raise AssertionError('unnecessary outside-library model construction')
            return super().known(name)
    preflight=check_class(s2.record(include_states=True),TypePreflightProvider(),[Q.name,'outside-name'])
    if not (preflight['status']=='COMPLETE'):
        raise AssertionError()
    if not (preflight['identification']['known'][1]['status']=='OUTSIDE-LIBRARY'):
        raise AssertionError()
    rec=s2.record(include_states=True)
    if not (audit([c],[rec],[result],Provider(),[Q.name])['status']=='PASS'):
        raise AssertionError()
    narrow=deepcopy(result);narrow['R'][0]='0.645497224367902814196'
    raises(ValueError,lambda:audit([c],[rec],[narrow],Provider(),[Q.name]))
    absent=deepcopy(result);absent['realisations'][0]['states']=[]
    raises(ValueError,lambda:audit([c],[rec],[absent],Provider(),[Q.name]))
    raises(ValueError,lambda:audit([c,c],[rec],[result],Provider(),[Q.name]))
    dropped=s2.record(include_states=True);dropped['states']=[]
    if not (check_class(dropped,Provider(),[Q.name])['status']=='OPEN'):
        raise AssertionError()
    omitted=s2.record(include_states=True);omitted['vfs']=[]
    if not (check_class(omitted,Provider(),[Q.name])['status']=='OPEN'):
        raise AssertionError()
    print('PASS simplex ROOT/identification/LU and uncertainty, incomplete coverage, radius, correspondence, subgroup corruptions',flush=True)

if __name__=='__main__': main()
