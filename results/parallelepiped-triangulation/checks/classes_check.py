import json,sys,itertools,random
from fractions import Fraction
from math import gcd
import numpy as np
from scipy.optimize import linprog

def det_int(M):  # exact Bareiss
    M=[list(map(int,r)) for r in M]; n=len(M); sign=1; prev=1
    for k in range(n-1):
        if M[k][k]==0:
            for i in range(k+1,n):
                if M[i][k]!=0: M[k],M[i]=M[i],M[k]; sign=-sign; break
            else: return 0
        for i in range(k+1,n):
            for j in range(k+1,n):
                M[i][j]=(M[i][j]*M[k][k]-M[i][k]*M[k][j])//prev
        prev=M[k][k]
    return sign*M[n-1][n-1]

def hnf_rows(B):
    """Row-style Hermite normal form (left action of GL4(Z)): upper triangular, positive diagonal,
    entries above a pivot reduced into [0,pivot)."""
    A=[list(map(int,r)) for r in B]; n=4
    for j in range(n):
        while True:
            nz=[i for i in range(j,n) if A[i][j]!=0]
            if len(nz)==0: raise ValueError('singular')
            p=min(nz,key=lambda i:abs(A[i][j]))
            A[j],A[p]=A[p],A[j]
            done=True
            for i in range(j+1,n):
                if A[i][j]!=0:
                    q=A[i][j]//A[j][j]
                    A[i]=[a-q*b for a,b in zip(A[i],A[j])]
                    if A[i][j]!=0: done=False
            if done: break
        if A[j][j]<0: A[j]=[-a for a in A[j]]
        for i in range(j):
            q=A[i][j]//A[j][j]
            A[i]=[a-q*b for a,b in zip(A[i],A[j])]
    return tuple(tuple(r) for r in A)

SP=[]
for perm in itertools.permutations(range(4)):
    for sg in itertools.product([1,-1],repeat=4):
        SP.append((perm,sg))
def canon(B):
    best=None
    for perm,sg in SP:
        # (B S)[:,k] = sg[k]*B[:,perm[k]]
        C=[[sg[k]*B[i][perm[k]] for k in range(4)] for i in range(4)]
        h=hnf_rows(C)
        if best is None or h<best: best=h
    return best

def all_hnf(D):
    out=[]
    for d in itertools.product(range(1,D+1),repeat=4):
        if d[0]*d[1]*d[2]*d[3]!=D: continue
        # entry (i,j), i<j, in [0,d[j])
        pos=[(i,j) for j in range(4) for i in range(j)]
        for vals in itertools.product(*[range(d[j]) for i,j in pos]):
            A=[[0]*4 for _ in range(4)]
            for k in range(4): A[k][k]=d[k]
            for (i,j),v in zip(pos,vals): A[i][j]=v
            out.append(tuple(tuple(r) for r in A))
    return out

def adjugate(B):
    adj=[[0]*4 for _ in range(4)]
    for i in range(4):
        for j in range(4):
            m=[[B[a][b] for b in range(4) if b!=i] for a in range(4) if a!=j]
            adj[i][j]=(-1)**(i+j)*det_int(m)
    return adj

def lattice_points(B):
    d=det_int(B); adj=adjugate(B)
    if d<0: d=-d; adj=[[-x for x in r] for r in adj]
    lo=[0]*4; hi=[0]*4
    for m in range(16):
        for i in range(4):
            s=sum(B[i][j] for j in range(4) if m>>j&1); lo[i]=min(lo[i],s); hi[i]=max(hi[i],s)
    pts=[]
    for x in itertools.product(*[range(lo[i],hi[i]+1) for i in range(4)]):
        if all(0<=sum(adj[i][k]*x[k] for k in range(4))<=d for i in range(4)): pts.append(x)
    return d,pts

def sep_exact(h,A,Bv,common):
    w=h[:4]; c=h[4]
    f=lambda p: sum(Fraction(w[i])*p[i] for i in range(4))+Fraction(c)
    return all(f(p)==0 for p in common) and all(f(p)<0 for p in A if p not in common) and all(f(p)>0 for p in Bv if p not in common)

def separate(A,Bv):
    """Exact certificate h (affine, rational) with h<0 on A\\B, h>0 on B\\A, h=0 on A&B; or None."""
    common=[p for p in A if p in Bv]
    Ao=[p for p in A if p not in common]; Bo=[p for p in Bv if p not in common]
    Aub=[list(p)+[1] for p in Ao]; bub=[-1]*len(Ao)
    Aub+= [[-x for x in p]+[-1] for p in Bo]; bub+=[-1]*len(Bo)
    Aeq=[list(p)+[1] for p in common] or None; beq=[0]*len(common) if common else None
    r=linprog(np.zeros(5),A_ub=np.array(Aub,float),b_ub=bub,A_eq=np.array(Aeq,float) if Aeq else None,b_eq=beq,bounds=[(None,None)]*5,method='highs')
    if r.status!=0: return None
    for den in (1,10,100,1000,10**4,10**6):
        h=[Fraction(x).limit_denominator(den) for x in r.x]
        if sep_exact(h,A,Bv,common): return h
    # exact repair: project onto equalities via integer least squares is not needed in practice
    return 'FLOAT_ONLY'

def check_tri(B,tri):
    d,pts=lattice_points(B); ps=set(pts)
    n=len(tri)
    if n!=24*d: return False,'count %d != %d'%(n,24*d)
    S=[]
    for s in tri:
        s=[tuple(p) for p in s]
        if len(set(s))!=5: return False,'repeated vertex'
        if any(p not in ps for p in s): return False,'vertex not lattice point of P(B)'
        if abs(det_int([[s[i][j]-s[0][j] for j in range(4)] for i in range(1,5)]))!=1: return False,'not unimodular'
        S.append(frozenset(s))
    if len(set(S))!=n: return False,'duplicate simplex'
    bb=[(min(p[i] for p in s),max(p[i] for p in s)) for s in S for i in [0]]
    npairs=0
    for a in range(n):
        for b in range(a+1,n):
            h=separate(sorted(S[a]),S[b]) if False else separate(list(S[a]),S[b])
            if h is None: return False,'pair %d,%d intersect improperly (LP infeasible)'%(a,b)
            if h=='FLOAT_ONLY': return False,'pair %d,%d: separation not exactly certified'%(a,b)
            npairs+=1
    # n unimodular simplices, pairwise interiors disjoint, inside P(B): total normalized volume = 24 d = vol P(B) => union=P(B)
    return True,'ok (%d pairs certified, %d points)'%(npairs,len(pts))

def do_line(args):
    D,li,line=args
    r=json.loads(line); B=r['B']
    if abs(det_int(B))!=D or r['det']!=D: return (li,B,r['status'],False,'det mismatch')
    if r['status']=='TRIANGULATION':
        ok,msg=check_tri(B,r['triangulation'])
    else: ok,msg=None,'UNSAT (not checked here)'
    return (li,B,r['status'],ok,msg)

if __name__=='__main__':
    from multiprocessing import Pool
    D=int(sys.argv[1]); path=sys.argv[2]
    lines=open(path).read().splitlines()
    allh=all_hnf(D); cl={}
    for h in allh: cl.setdefault(canon(h),[]).append(h)
    print('D=%d HNFs=%d classes_expected=%d lines=%d'%(D,len(allh),len(cl),len(lines)))
    seen={}
    for li,l in enumerate(lines):
        c=canon(json.loads(l)['B']); seen.setdefault(c,[]).append(li)
    comp = set(seen)==set(cl) and all(len(v)==1 for v in seen.values())
    print('completeness/uniqueness:',comp,'missing',len(set(cl)-set(seen)),'extra',len(set(seen)-set(cl)),'dups',sum(len(v)>1 for v in seen.values()))
    with Pool(12) as p: res=p.map(do_line,[(D,i,l) for i,l in enumerate(lines)],chunksize=1)
    nv=0
    for li,B,st,ok,msg in res:
        if st=='TRIANGULATION':
            nv+=ok is True
            if ok is not True: print('  FAIL line',li,B,msg)
        else: print('  UNSAT line',li,B)
    print('D=%d classes=%d verified_triangulations=%d unsat=%d'%(D,len(lines),nv,sum(r[2]=='UNSAT' for r in res)))
