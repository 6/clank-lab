#!/usr/bin/env python3
"""Exact Eisenstein-integer root closure and faithful permutation group orders.

Pairs (a,b) mean a+b*omega, omega^2+omega+1=0. No modular reduction.
SymPy's exact Schreier-Sims algorithm computes the three permutation orders.
"""
import argparse, hashlib, itertools, json, pathlib, time
from sympy.combinatorics import Permutation, PermutationGroup

ZERO=(0,0); ONE=(1,0); OMEGAS=[ONE,(0,1),(-1,-1)]; THETA=(1,2)
def mul(x,y):
    a,b=x;c,d=y
    return a*c-b*d,a*d+b*c-b*d
def conj(x):return x[0]-x[1],-x[1]
def scale(v,s):return tuple(mul(x,s) for x in v)
def plus(x,y):return x[0]+y[0],x[1]+y[1]
def minus(x,y):return x[0]-y[0],x[1]-y[1]
UNITS=OMEGAS+[(-a,-b) for a,b in OMEGAS]
def canonical(v):return min(scale(v,s) for s in UNITS)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',type=pathlib.Path,required=True);args=ap.parse_args()
    start=time.perf_counter();cpu=time.process_time();vectors=[]
    for i,j in itertools.combinations(range(6),2):
        for a,b in itertools.product(range(3),repeat=2):
            for sign in [1,-1]:
                v=[ZERO]*6;v[i]=mul((sign,0),mul(THETA,OMEGAS[a]));v[j]=mul((-sign,0),mul(THETA,OMEGAS[b]));vectors.append(tuple(v))
    for a in itertools.product(range(3),repeat=5):
        for sign in [1,-1]:vectors.append(tuple(mul((sign,0),OMEGAS[t]) for t in a+((-sum(a))%3,)))
    assert len(vectors)==len(set(vectors))==756
    vectors=sorted(vectors);index={v:i for i,v in enumerate(vectors)}
    assert all(tuple(conj(x) for x in v) in index for v in vectors)
    normals=sorted(set(map(canonical,vectors)));assert len(normals)==126
    permutations={}
    for n in normals:
        norm=ZERO
        for x in n:norm=plus(norm,mul(conj(x),x))
        assert norm==(6,0)
        perm=[]
        for v in vectors:
            inner=ZERO
            for x,y in zip(n,v):inner=plus(inner,mul(conj(x),y))
            image=[]
            for x,y in zip(v,n):
                numerator=mul(inner,y);assert numerator[0]%3==numerator[1]%3==0
                image.append(minus(x,(numerator[0]//3,numerator[1]//3)))
            perm.append(index[tuple(image)])
        assert len(set(perm))==756 and all(perm[perm[i]]==i for i in range(756))
        permutations[n]=Permutation(perm)
    def normal(i,j,power=0):
        n=[ZERO]*6;n[i]=THETA;n[j]=mul((-1,0),mul(THETA,OMEGAS[power]));return canonical(tuple(n))
    # Oura-Sekiguchi section 2: P1,P2,P3,Q1,R1,R2.
    # R1 has hyperplane x1-omega*x2=0, hence conjugate normal exponent2.
    named=[normal(1,2),normal(2,3),normal(3,4),normal(0,1),normal(0,1,2),canonical((ONE,)*6)]
    gens=[permutations[n] for n in named]
    W=PermutationGroup(gens);K=PermutationGroup([gens[i] for i in [0,1,3,4,5]]);H=PermutationGroup([gens[i] for i in [0,1,3,4]])
    orders={'G34':int(W.order()),'G33':int(K.order()),'G(3,3,4)':int(H.order())}
    assert orders=={'G34':39191040,'G33':51840,'G(3,3,4)':648},orders
    fixed=normal(4,5);point=index[fixed]
    assert all(g(point)==point for g in K.generators)
    orbit=len(W.orbit(point));assert orbit==756 and orders['G34']//orbit==orders['G33']
    # Compute a spanning determinant independently in Z[omega].
    basis=[]
    for i in range(5):
        v=[ZERO]*6;v[i]=THETA;v[5]=(-THETA[0],-THETA[1]);basis.append(tuple(v))
    basis.append((ONE,)*6);assert all(v in index for v in basis)
    determinant=ZERO
    for permutation in itertools.permutations(range(6)):
        sign=(-1)**sum(permutation[i]>permutation[j] for i in range(6) for j in range(i+1,6))
        term=(sign,0)
        for i,j in enumerate(permutation):term=mul(term,basis[i][j])
        determinant=plus(determinant,term)
    determinant_norm=mul(determinant,conj(determinant));assert determinant_norm==(8748,0)
    digest=hashlib.sha256(json.dumps([[list(x) for x in n] for n in named],separators=(',',':')).encode()).hexdigest()
    result={'ring':'Z[omega], omega^2+omega+1=0','vectors':756,'vectors_closed_under_conjugation':True,'reflection_lines':126,'exact_vector_reflection_images_checked':756*126,'reflection_permutations_involutive':True,'orders':orders,'G33_fixes_vector_line_representative':True,'G34_orbit_size':orbit,'stabilizer_order':orders['G34']//orbit,'H_generators_subset_K':True,'K_generators_subset_W':True,'faithful_action_spanning_determinant':determinant,'faithful_action_spanning_determinant_norm':determinant_norm[0],'named_generator_normals_sha256':digest,'group_order_method':'SymPy exact Schreier-Sims on faithful 756-point permutation action','cpu_seconds':time.process_time()-cpu,'wall_seconds':time.perf_counter()-start,'unresolved':0}
    args.out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))

if __name__=='__main__':main()
