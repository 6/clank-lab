"""Coordinates derived from the paper's definition and diagram table only."""
from fractions import Fraction as F
from functools import cache
from itertools import product
from exact import ZERO, ONE, q, add, sub, scale, dot, solve


def roots(group):
    n=5 if group=='A' else 4
    e=[tuple(ONE if i==j else ZERO for j in range(n)) for i in range(n)]
    # Multiplication by sqrt(2): (e_i-e_j)/sqrt(2).
    def long(i,j,sign=-1):
        return tuple(q(0,F((k==i)+sign*(k==j),2)) for k in range(n))
    if group=='A': return tuple(long(i,i+1) for i in range(4))
    if group=='B': return (long(0,1),long(1,2),long(2,3),e[3])
    if group=='D': return (long(0,1),long(1,2),long(2,3),long(2,3,1))
    if group=='F': return (long(1,2),long(2,3),e[3],tuple(q(F(s,2)) for s in [1,-1,-1,-1]))
    raise ValueError(group)


def validated_roots(group):
    r=roots(group)
    edges={'A':{(0,1):3,(1,2):3,(2,3):3},
           'B':{(0,1):3,(1,2):3,(2,3):4},
           'D':{(0,1):3,(1,2):3,(1,3):3},
           'F':{(0,1):3,(1,2):4,(2,3):3}}[group]
    for i in range(4):
        for j in range(i,4):
            m=edges.get((i,j),2)
            expect=ONE if i==j else {2:ZERO,3:q(F(-1,2)),4:q(0,F(-1,2))}[m]
            if not (dot(r[i],r[j])==expect):
                raise AssertionError('Coxeter Gram mismatch')
    return r


@cache
def vertices(name):
    if name[:2] in ['A4','B4','D4','F4']:
        group=name[0]; rings=tuple(map(int,name[2:]))
        if not (len(rings)==4 and any(rings) and set(rings)<={0,1}):
            raise AssertionError()
        r=validated_roots(group)
        gram=[[dot(a,b) for b in r] for a in r]
        coeff=solve(gram,[q(F(b,2)) for b in rings])
        from exact import mul
        seed=tuple(sum_field(mul(coeff[i],r[i][j]) for i in range(4)) for j in range(len(r[0])))
        if not (all(dot(seed,a)==q(F(b,2)) for a,b in zip(r,rings))):
            raise AssertionError()
        # Exact reflection BFS; termination plus closure is the complete orbit.
        seen={seed}; queue=[seed]
        for p in queue:
            for a in r:
                k=scale(dot(p,a),2)
                v=tuple(sub(x,mul(k,y)) for x,y in zip(p,a))
                if v not in seen: seen.add(v); queue.append(v)
        return tuple(sorted(seen))
    half=q(F(1,2))
    if name=='pr-cube':
        return tuple(tuple(scale(half,s) for s in signs) for signs in product([-1,1],repeat=4))
    if name=='duoprism-4-4':
        # Unit-edge squares on their coordinate axes, radius 1/sqrt(2).
        square=[(q(0,F(s,2)),ZERO) if axis==0 else (ZERO,q(0,F(s,2))) for axis in range(2) for s in [-1,1]]
        return tuple(a+b for a in square for b in square)
    if name=='pr-oct':
        octa=[tuple(q(0,F(s,2)) if j==axis else ZERO for j in range(3)) for axis in range(3) for s in [-1,1]]
        return tuple(v+(scale(half,s),) for v in octa for s in [-1,1])
    if name=='antiprism-prism-3':
        # r=1/sqrt(3); h/2=1/sqrt(6). Two equilateral triangles,
        # angular offset pi/3, on planes z=+-h/2; then a unit segment.
        lower=[(q(0,0,F(1,3)),ZERO),(q(0,0,F(-1,6)),half),(q(0,0,F(-1,6)),scale(half,-1))]
        upper=[(q(0,0,F(1,6)),half),(q(0,0,F(-1,3)),ZERO),(q(0,0,F(1,6)),scale(half,-1))]
        v=[p+(q(0,0,0,F(-1,6)),) for p in lower]+[p+(q(0,0,0,F(1,6)),) for p in upper]
        return tuple(p+(scale(half,s),) for p in v for s in [-1,1])
    raise ValueError('unsupported name '+name)


def sum_field(xs):
    ans=ZERO
    for x in xs: ans=add(ans,x)
    return ans
