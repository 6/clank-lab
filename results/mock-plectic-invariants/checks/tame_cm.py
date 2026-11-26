"""Depth-two evaluation on local segments, for class number one.

This backend covers the repeated tame prime powers. The independent
ring-class evaluator can also use ray_value and stable_lines below.
"""
from itertools import product
from segments import Flags, act, adj, column, direction, label


def stable_lines(mat, q, m):
    stable = []
    for s in range(m + m//q):
        x,y = v = column(s,q,m)
        u,w = act(mat,v)
        if (x*w-y*u) % m == 0:
            stable.append(s)
    if len(stable) != 2:
        raise ArithmeticError(f"expected two split CM eigendirections at {m}")
    return stable


def ray_value(flags, p, index, lines, v, values):
    first = label(v,p,p)
    hits = [e for e in flags.load(p)[index] if direction(e[f"p{p}"],p)==first]
    if len(hits) != 1:
        raise ArithmeticError("first-edge cover")
    e, = hits
    result = []
    for k,(q,m) in enumerate(zip(flags.levels,flags.powers)):
        if q == p:
            x,y = act(adj(e[f"p{p}"]),v)
            if x % p or y % p:
                raise ArithmeticError("nonintegral second edge")
            s = label((x//p,y//p),p,p)
        else:
            s = label(act(adj(e[f"p{q}"]),column(lines[k],q,m)),q,m)
        result.append(s)
    state = (e["index"],*result)
    return values[flags.offset(state)]


def generator(w, p):
    size = p*(p+1)
    # A primitive projective Cartan element has nonscalar reduction and
    # can be scaled into a+omega. Its p lifts cover all first principal units.
    for a in range(p*p):
        mat = (a+w[0],w[1],w[2],a+w[3])
        rays, seen, v = [], set(), (1,0)
        while (s := label(v,p,p*p)) not in seen:
            rays.append(s)
            seen.add(s)
            v = act(mat,column(s,p,p*p))
        if len(rays) == size and s == 0:
            return a,rays
    raise ArithmeticError("no primitive nonsplit Cartan generator")


def evaluate(case, ell, directory):
    from sage.all import ZZ
    if ZZ(case["D"]).class_number(proof=True) != 1:
        raise ValueError("tame_cm requires the class-group evaluator here")
    flags = Flags(case,ell,directory)
    values = flags.read("eigen.json")
    p,D = case["p"],case["D"]
    factor = case["vdelta"] * pow(case["ap"],-2,p)
    variants = []
    for cm in sorted(flags.data["cm"],key=lambda cm:(cm["omega"],cm["index"])):
        i = cm["index"]
        a,rays = generator(cm[f"p{p}"],p)
        choices = [[None] if q==p else stable_lines(cm[f"p{q}"],q,m)
                   for q,m in zip(flags.levels,flags.powers)]
        for lines in product(*choices):
            coeff = [0]*p
            for j,s in enumerate(rays):
                coeff[j%p] += factor*ray_value(flags,p,i,lines,column(s,p,p*p),values)
            coeff = [c%p for c in coeff]
            if sum(coeff)%p:
                raise ArithmeticError("nonzero augmentation")
            moment = sum(j*c for j,c in enumerate(coeff))%p
            variants.append(dict(index=i,omega=cm["omega"],lines=lines,generator=a,
                                 first_moment=moment,coefficients=coeff))
    if not variants or len({bool(v["first_moment"]) for v in variants})!=1:
        raise ArithmeticError("inconsistent CM choices")
    return dict(variants=variants,first_moment=variants[0]["first_moment"],
                coefficients=variants[0]["coefficients"])


def check(case, ell, directory, certificate):
    """Rebuild the depth-two coefficients on full local segments."""
    replay = evaluate(case, ell, directory)
    computed = {
        (v["omega"], tuple(s for s in v["lines"] if s is not None), v["generator"]):
        v["coefficients"] for v in replay["variants"]
    }
    expected = {
        (v["omega"], tuple(v["tame_flags"]), v["generator_shift"]): v["coefficients"]
        for v in certificate["checks"]["variants"]
    }
    if computed != expected:
        raise ArithmeticError("CM coefficients disagree on tame prime-power segments")
