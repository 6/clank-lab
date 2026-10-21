import itertools
from pathlib import Path
# Q = C3^3, cell 9x+3y+z.  Projective forms: first nonzero coeff = 1.
pts=[(x,y,z) for x in range(3) for y in range(3) for z in range(3)]
idx=lambda p:9*p[0]+3*p[1]+p[2]
forms=[f for f in pts if f!=(0,0,0) and [c for c in f if c][0]==1]
assert len(forms)==13
M=24909666
Hpts=[(b//9,b//3%3,b%3) for b in range(27) if M>>b&1]
layers=[sum(1 for p in Hpts if p[0]==x) for x in range(3)]
print('S layers',layers)
# check zero coset of every form contains count ≡1 mod 3 of singletons
for f in forms:
    c=sum(1 for (x,u,w) in Hpts if (f[0]*x)%3==0)  # H points map to (x,0,0) in Q
    assert c%3==1, f
imgs=set()
for signs in itertools.product((0,1),repeat=13):
    t=[(40,36,45) if s==0 else (40,45,36) for s in signs]
    r=[]
    ok=True
    for q in pts:
        s=sum(t[i][sum(a*b for a,b in zip(f,q))%3] for i,f in enumerate(forms))
        v=s-484
        if v%9: ok=False;break
        r.append(v//9)
    if not ok: continue
    if any(c<0 or c>9 for c in r): continue
    if (r[0],r[9],r[18])!=tuple(layers): continue
    if any(r[i]%3 for i in range(27) if i not in (0,9,18)): continue
    imgs.add(tuple(r))
print('images',len(imgs))
def sub(p,q): return tuple((a-b)%3 for a,b in zip(p,q))
for r in imgs:
    ac={}
    for p in pts:
        for q in pts: ac[sub(p,q)]=ac.get(sub(p,q),0)+r[idx(p)]*r[idx(q)]
    assert ac[(0,0,0)]==601 and all(v==540 for k,v in ac.items() if k!=(0,0,0))
    assert sum(r)==121
from collections import Counter
print('coef dist', Counter(tuple(sorted(Counter(r[i] for i in range(27) if i not in (0,9,18)).items())) for r in imgs).most_common(3))
# alternative enumeration: assign {0,3,6,9} to 24 cells via line sums? -> verify via brute force over index-3 forms instead:
# Q-maps from S-stabilizer: (x,y,z)->(a x+b y+c z+t0, B(y,z)); stabilizer has a=1,t0=0, B in {I, [[2,2],[1,0]], [[0,1],[2,2]]}
Bs=[((1,0),(0,1)),((2,2),(1,0)),((0,1),(2,2))]
qmaps=[]
for B in Bs:
    for b in range(3):
        for c in range(3):
            def F(p,B=B,b=b,c=c):
                x,y,z=p
                return ((x+b*y+c*z)%3,(B[0][0]*y+B[0][1]*z)%3,(B[1][0]*y+B[1][1]*z)%3)
            qmaps.append(F)
def act(F,r):
    s=[0]*27
    for p in pts: s[idx(F(p))]=r[idx(p)]
    return tuple(s)
assert all(act(F,r) in imgs for F in qmaps for r in imgs)
seen=set();orbs=[]
for r in sorted(imgs):
    if r in seen: continue
    o={act(F,r) for F in qmaps}; seen|=o; orbs.append(o)
print('orbits',len(orbs),[len(o) for o in orbs])
cases=[list(map(int,l.split())) for l in open(Path(__file__).resolve().parent.parent/'data/cases.txt')]
hit=[0]*len(orbs)
for c in cases:
    w,r=c[0],tuple(c[1:])
    assert len(r)==27
    k=[i for i,o in enumerate(orbs) if r in o]; assert len(k)==1,('case not an image',c)
    assert len(orbs[k[0]])==w,(w,len(orbs[k[0]]))
    hit[k[0]]+=1
print('cases hit each orbit once:',hit==[1]*len(orbs), 'weights ok')
