#!/usr/bin/env python3
"""Exact simultaneous-feasibility witness from a five-level AAB construction.

Sample each vertex's level independently. Edges have two equal smaller
levels and one larger level. AAB recursion uses x=317/500 and five levels;
its density exceeds 4641/10000. All constraints are checked directly below,
without invoking the unformalised limiting argument or any solver.
"""
import itertools as it
import json,time
from fractions import Fraction
from pathlib import Path

TR=list(it.combinations(range(6),3));TI={t:i for i,t in enumerate(TR)}
def need(b,msg):
    if not b:raise ValueError(msg)

def psd(A):
    # Exact symmetric Schur complements, with zero-pivot row checks.
    B=[[Fraction(v) for v in row] for row in A];n=len(B);rank=0
    need(all(B[i][j]==B[j][i] for i in range(n) for j in range(n)),'symmetry')
    for i in range(n):
        pivot=B[i][i];need(pivot>=0,'PSD pivot')
        if not pivot:
            need(all(B[i][j]==0 for j in range(i+1,n)),'PSD zero pivot');continue
        rank+=1
        for j in range(i+1,n):
            for k in range(j,n):
                B[j][k]-=B[j][i]*B[k][i]/pivot;B[k][j]=B[j][k]
    return rank

def main():
    start=time.time();c=json.loads((Path(__file__).parent/'certificate.json').read_text())
    D=500**5;weights=[317*183**i*500**(4-i) for i in range(5)]+[183**5]
    need(sum(weights)==D,'level masses')
    mass={}
    for levels in it.product(range(6),repeat=6):
        mask=0;v=1
        for i in levels:v*=weights[i]
        for j,t in enumerate(TR):
            a,b,d=sorted(levels[i] for i in t)
            if a==b<d:mask|=1<<j
        mass[mask]=mass.get(mask,0)+v
    need(sum(mass.values())==D**6,'probability normalisation')
    cycles=set()
    for p in it.permutations(range(6),5):
        cycles.add(sum(1<<TI[tuple(sorted((p[i],p[(i+1)%5],p[(i+2)%5])))] for i in range(5)))
    need(all(not any(m&cy==cy for cy in cycles) for m in mass),'C5 freeness')
    # Exact exchangeability, checked on adjacent transposition generators.
    for a in range(5):
        perm=list(range(6));perm[a],perm[a+1]=perm[a+1],perm[a]
        image=[TI[tuple(sorted(perm[v] for v in t))] for t in TR]
        for mask,value in mass.items():
            other=sum(1<<image[i] for i in range(20) if mask>>i&1)
            need(mass.get(other)==value,'exchangeability')
    CL=[[[0]*256 for _ in range(2)] for _ in range(2)]
    C=[[[0]*32 for _ in range(32)] for _ in range(16)]
    matrices=[[[0]*len(b['flags']) for _ in b['flags']] for b in c['blocks']]
    maps=[{v:i for i,v in enumerate(b['flags'])} for b in c['blocks']]
    density=0;dens=[0,0]
    for mask,value in mass.items():
        e=lambda a,b,d:(mask>>TI[tuple(sorted((a,b,d)))])&1
        tau=e(0,1,2);edge=e(3,4,5);density+=tau*value
        pats=[4*e(0,1,z)+2*e(0,2,z)+e(1,2,z) for z in (3,4,5)]
        union=sum(1<<p for p in set(pats))
        K=e(0,3,4)*e(0,3,5)*e(0,4,5)*edge
        ch=e(0,3,4)*e(0,3,5)*(1-e(0,4,5))
        CL[0][tau][union]+=(ch-K)*value;CL[1][tau][union]+=(ch*(1-edge)-K)*value
        pat=lambda z:16*e(0,1,z)+8*e(0,2,z)+4*e(1,2,z)+2*e(3,1,z)+e(3,2,z)
        C[8*tau+pats[0]][pat(4)][pat(5)]+=(ch*(1-edge)-K)*value
        dens[0]+=(10000*tau-4641)*edge*value;dens[1]+=(10000*tau-4641)*(1-edge)*value
        root=sum(e(*t)<<i for i,t in enumerate(it.combinations(range(4),3)))
        if root in (0,1,3,7,15):
            j=(0,1,3,7,15).index(root)
            f=lambda z:sum(e(a,b,z)<<i for i,(a,b) in enumerate(it.combinations(range(4),2)))
            matrices[j][maps[j][f(4)]][maps[j][f(5)]]+=value
        f=lambda a,b:4*(e(0,1,a)+e(0,1,b))+2*e(0,a,b)+e(1,a,b)
        matrices[5][maps[5][f(2,3)]][maps[5][f(4,5)]]+=value
    need(density*10000>=4641*D**6 and min(dens)>=0,'density hypothesis and localisations')
    clmin=[]
    for family in range(2):
        for tau in range(2):
            A=CL[family][tau][:]
            for bit in range(8):
                for pi in range(256):
                    if pi&(1<<bit):A[pi]+=A[pi^(1<<bit)]
            clmin.extend(A[1:])
    need(min(clmin)>=0,'CL rows')
    gmin=[]
    for A in C:
        for s in range(32):
            gmin.append(A[s][s])
            for t in range(s+1,32):gmin.append(A[s][s]+A[s][t]+A[t][s]+A[t][t])
        gmin.append(sum(map(sum,A)))
    need(min(gmin)>=0,'G3 indicator rows')
    cutvalues=[sum(r['w'][s]*r['w'][t]*C[r['k']][s][t] for s in range(32) for t in range(32)) for r in c['cuts']]
    need(min(cutvalues)>=0,'weighted G3 rows')
    ranks=[psd(A) for A in matrices]
    print(json.dumps({'status':'PASS','levels':6,'labelled_support':len(mass),'density':str(Fraction(density,D**6)),
                      'density_decimal':density/D**6,'psd_ranks':ranks,'all_rows_nonnegative':True,'seconds':time.time()-start}),flush=True)
if __name__=='__main__':main()
