#!/usr/bin/env python3
"""Usage: localfan.py P.meta [VERTEX] [--out FILE] (P.meta from enc.py --meta; VERTEX like 1,1,1,0,
default the origin); env CADICAL (a SAT solver binary), PROPER (proper.cpp compiled).
The search for Proposition 1.5: finds a unimodular triangulation of the vertex cone of P at VERTEX
with rays through lattice points of P, tests it in the cross-section h(x) = 1 (pairwise proper;
volumes add up), and with --out appends it to FILE as one JSON line {"vertex", "cones"}, each cone
given by the 4 lattice points of P on its rays. check_fans.py and fans_check.py check these files."""
# Is there a unimodular triangulation of the cone of P at vertex 0 using rays through lattice points of P?
import json, sys, os, itertools, subprocess
from fractions import Fraction as Fr
from math import gcd
OUT=None
if '--out' in sys.argv:
    k=sys.argv.index('--out'); OUT=sys.argv[k+1]; del sys.argv[k:k+2]
m=json.load(open(sys.argv[1])); pts=[tuple(p) for p in m['points']]; d=4
VTX=v=(0,0,0,0)
if len(sys.argv)>2:  # move the vertex to the origin: P - v is spanned by the generators e_i b_i, e_i = -1 if v uses b_i
    VTX=v=tuple(int(c) for c in sys.argv[2].split(","))
    B0=m['B']
    S=next(S for S in itertools.product((0,1),repeat=d) if tuple(sum(B0[i][j]*S[j] for j in range(d)) for i in range(d))==v)
    m['B']=[[B0[i][j]*(-1 if S[j] else 1) for j in range(d)] for i in range(d)]
    pts=[tuple(a-b for a,b in zip(p,v)) for p in pts]
z=pts.index((0,0,0,0))
S0=[tuple(s) for s in m['simplices'] if z in s]
print('simplices at 0:',len(S0))
def prim(p):
    g=0
    for x in p: g=gcd(g,abs(x))
    return tuple(x//g for x in p)
rays={i:prim(pts[i]) for i in range(len(pts)) if i!=z}
print('distinct rays',len(set(rays.values())),'of',len(rays))
def det(M):
    M=[[Fr(x) for x in r] for r in M]; n=len(M); s=Fr(1)
    for c in range(n):
        p=next((r for r in range(c,n) if M[r][c]!=0),None)
        if p is None: return 0
        if p!=c: M[c],M[p]=M[p],M[c]; s=-s
        s*=M[c][c]
        for r in range(c+1,n):
            f=M[r][c]/M[c][c]
            for k in range(c,n): M[r][k]-=f*M[c][k]
    return s
# cone cells: 4 rays; unimodular cone iff |det| = 1 of the ray points
cells=set()
for s in S0:
    R=tuple(sorted(i for i in s if i!=z)); cells.add(R)
cells=sorted(cells); print('unimodular cones from simplices at 0:',len(cells))
# boundary of cone: all ray points have t_i = 0 for some i (coordinates t = B^-1 x)
B=m['B']
DB=det(B)
# exact inverse by Cramer's rule: Bi[k][r] = det(B with column k replaced by e_r) / det B
Bi=[[det([[int(i==r) if j==k else B[i][j] for j in range(d)] for i in range(d)])/DB for r in range(d)] for k in range(d)]
T={i:[sum(Bi[k][r]*pts[i][r] for r in range(d)) for k in range(d)] for i in rays}
def bnd(F): return any(all(T[v][k]==0 for v in F) for k in range(d))
def side(F,q):
    v=det([list(pts[f]) for f in F]+[list(pts[q])])  # cone facet hyperplane through 0
    return 1 if v>0 else -1
var={c:i+1 for i,c in enumerate(cells)}
fac={}
for c in cells:
    for q in c:
        F=tuple(x for x in c if x!=q); fac.setdefault(F,{1:[],-1:[]})[side(F,q)].append(var[c])
cl=[]
for F,sd in fac.items():
    for g in sd.values():
        for a,b in itertools.combinations(g,2): cl.append([-a,-b])
    if not bnd(F):
        for sg in (1,-1):
            for a in sd[sg]: cl.append([-a]+sd[-sg])
cl.append(list(var.values()))  # nonempty
def solve(cl):
    open('lf.cnf','w').write('p cnf %d %d\n'%(len(cells),len(cl))+''.join(' '.join(map(str,c))+' 0\n' for c in cl))
    r=subprocess.run([os.environ.get('CADICAL','cadical'),'-q','lf.cnf'],capture_output=True,text=True)
    if r.returncode==20: return None
    return sorted(int(x) for l in r.stdout.splitlines() if l.startswith('v') for x in l.split()[1:] if int(x)>0)
# CEGAR with proper intersection of cones = proper intersection of simplices conv(0, rays) scaled? use proper on the simplices {0}+rays
rounds=0
while True:
    rounds+=1
    mdl=solve(cl)
    if mdl is None: print('UNSAT after',rounds); break
    ch=[cells[v-1] for v in mdl]
    # cone over each cell intersected with a hyperplane: test proper intersection of simplices (0, k*rays) is equivalent for cones meeting only at 0
    inp='4 %d\n'%len(pts)+''.join(' '.join(map(str,p))+'\n' for p in pts)+'%d\n'%len(ch)+''.join('%d '%z+' '.join(map(str,c))+'\n' for c in ch)+'-1\n'
    out=subprocess.run([os.environ.get('PROPER','proper')],input=inp,capture_output=True,text=True).stdout.split()
    bad=[(mdl[int(a)],mdl[int(b)]) for a,b in zip(out[::2],out[1::2])]
    if not bad:
        vol=sum(1 for c in ch); print('fan found: cones',len(ch),'rounds',rounds); 
        used=sorted(set(v for c in ch for v in c)); print('rays used',[pts[v] for v in used]); break
    cl+=[[-a,-b] for a,b in bad]

# exact verification in the cross-section h(x) = 5*sum(B^{-1} x) = H
Bi5=[[abs(DB)*Bi[i][j] for j in range(d)] for i in range(d)]  # |det B| * B^{-1}: the adjugate up to sign, integral
assert all(v.denominator==1 for r in Bi5 for v in r)
Bi5=[[int(v) for v in r] for r in Bi5]
h=lambda p: sum(Bi5[i][j]*p[j] for i in range(d) for j in range(d))
from math import lcm
used=sorted(set(v for c in ch for v in c)|{pts.index(tuple(b)) for b in [tuple(B[i][j] for i in range(d)) for j in range(d)]})
H=1
for v in used: H=lcm(H,h(pts[v]))
sec={v:[pts[v][i]*H//h(pts[v]) for i in range(d)] for v in used}
# project: drop coordinate 3 (h has nonzero coefficient on x4?) check
coef=[sum(Bi5[i][j] for i in range(d)) for j in range(d)]; print('h coefficients',coef)
k=[j for j in range(d) if coef[j]!=0][-1]
proj={v:[sec[v][i] for i in range(d) if i!=k] for v in used}
idx={v:i for i,v in enumerate(used)}
inp='3 %d\n'%len(used)+''.join(' '.join(map(str,proj[v]))+'\n' for v in used)+'%d\n'%len(ch)+''.join(' '.join(str(idx[x]) for x in c)+'\n' for c in ch)+'-1\n'
out=subprocess.run([os.environ.get('PROPER','proper')],input=inp,capture_output=True,text=True).stdout.split()
print('improper pairs in section:',len(out)//2)
def adet(c): return abs(det([[proj[c[i]][j]-proj[c[0]][j] for j in range(3)] for i in range(1,4)]))
tot=sum(adet(c) for c in ch)
big=tuple(pts.index(tuple(b)) for b in [tuple(B[i][j] for i in range(d)) for j in range(d)])
print('sum of section volumes',tot,'section of sigma',adet(big))

# Hilbert basis of the cone: its elements lie in P, and x in P is reducible iff x - y lies in
# the cone for some nonzero lattice point y != x of P (then y and x - y lie in P)
tc=lambda x: [sum(Bi[k][r]*x[r] for r in range(d)) for k in range(d)]
nz=[i for i in range(len(pts)) if i!=z]
red=[i for i in nz if any(j!=i and all(c>=0 for c in tc([pts[i][r]-pts[j][r] for r in range(d)])) for j in nz)]
hb=[i for i in nz if i not in red]
usedR=sorted(set(v for c in ch for v in c))
print('Hilbert basis elements',len(hb),'; rays of the fan',len(usedR),'of which reducible',len([u for u in usedR if u in red]))
if OUT:
    with open(OUT,'a') as f:
        f.write(json.dumps({'vertex':list(VTX),'cones':[[[a+b for a,b in zip(pts[i],VTX)] for i in c] for c in ch]})+'\n')
