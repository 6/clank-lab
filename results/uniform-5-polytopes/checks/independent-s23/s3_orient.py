"""All full-star orientations over a fixed S2 vertex figure.

S2 may quotient by VF isometries which do not extend to the full facet.
S3 restores the exact right cosets of full-base symmetries in the complete
VF metric group, independently at EVERY facet (including the seed).
"""
from itertools import product
from functools import lru_cache
from geometry import Undecided
from s3_stars import model_geometry,model_symmetries


def coset_representatives(group,subgroup,n):
    group={tuple(g) for g in group};subgroup={tuple(h) for h in subgroup}
    identity=tuple(range(n))
    if identity not in group or identity not in subgroup or not subgroup<=group:
        raise ValueError('invalid VF/full symmetry subgroup')
    if any(sorted(g)!=list(range(n)) for g in group): raise ValueError('invalid VF permutation')
    # Provider proves group membership/completeness. Check subgroup closure
    # independently so the coset quotient cannot silently omit a pattern.
    if any(tuple(g[h[i]] for i in range(n)) not in subgroup for g in subgroup for h in subgroup):
        raise ValueError('full stabilizers do not form a subgroup')
    covered=set();reps=[]
    for g in [identity]+sorted(group-{identity}):
        if g in covered: continue
        orbit={tuple(g[h[i]] for i in range(n)) for h in subgroup}
        if not orbit<=group: raise ValueError('full/VF group mismatch')
        reps.append(g);covered.update(orbit)
    if covered!=group: raise ValueError('incomplete orientation coset coverage')
    return reps


@lru_cache(maxsize=256)
def orientation_options(model):
    completeness=getattr(model,'stabilizers_complete',False)
    if not (completeness() if callable(completeness) else completeness):
        raise Undecided(f'{model.name}: VF isometry completeness unavailable')
    group=[tuple(g) for g in model.stabilizers]
    if any(not model.verify_stabilizer(g) for g in group):
        raise ValueError('uncertified VF isometry in orientation expansion')
    _,b,ns=model_geometry(model);inv={j:i for i,j in enumerate(ns)}
    full=[]
    for p in model_symmetries(model,b):
        try: full.append(tuple(inv[p[j]] for j in ns))
        except KeyError as e: raise ValueError('full symmetry misses neighbour set') from e
    return coset_representatives(group,full,len(ns))


def expand_orientations(state,models,limit=None):
    names={f['name'] for f in state['facets']}
    options={name:orientation_options(models[name]) for name in names}
    count=1
    for f in state['facets']: count*=len(options[f['name']])
    if limit is not None and count>limit: raise Undecided('full-star orientation product limit')
    for choices in product(*(options[f['name']] for f in state['facets'])):
        facets=[]
        for f,p in zip(state['facets'],choices,strict=True):
            facets.append(dict(f,map=[f['map'][p[i]] for i in range(len(p))]))
        yield dict(state,facets=facets,orientation=[list(p) for p in choices])
