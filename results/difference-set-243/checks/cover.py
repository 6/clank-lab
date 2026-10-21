# Independent coverage checks. Uses only definitions,
# the pinned cases.txt, p243.txt (for orbit indices of the production table) and the
# TEST_ONLY --dump-choices output of the frozen campaign.cpp (both kernels).
import json, random, itertools, sys
from pathlib import Path
random.seed(int(sys.argv[1]) if len(sys.argv)>1 else 1)
P=str(Path(__file__).resolve().parent.parent/'data')
enc=lambda x,y,z:81*(x%3)+9*(y%9)+(z%9)
dec=lambda a:(a//81,a//9%9,a%9)
G=list(range(243))
add=lambda a,b:enc(*(p+q for p,q in zip(dec(a),dec(b))))
neg=lambda a:enc(*(-p for p in dec(a)))
smul=lambda k,a:enc(*(k*p for p in dec(a)))
H=[g for g in G if smul(61,g)==g]; assert len(H)==27 and set(H)=={enc(x,3*u,3*w) for x in range(3) for u in range(3) for w in range(3)}
orbit=lambda g:frozenset({g,smul(61,g),smul(61*61,g)})
ORB={orbit(g) for g in G}; assert len(ORB)==99
cellof=lambda a:9*(a//81)+3*(a//9%9%3)+(a%9%3)
MASK=24909666
hbit=lambda a:9*(a//81)+3*((a//9%9)//3)+((a%9)//3)
S=frozenset(h for h in H if MASK>>hbit(h)&1); assert len(S)==13
def gmap(a,b,c,d,e,f,g_,h,i,t):
    # F(x,y,z) = (a x + b y + c z, 3d x + e y + f z, 3g x + h y + i z) + t
    def F(p):
        x,y,z=dec(p); return add(enc(a*x+b*y+c*z, 3*d*x+e*y+f*z, 3*g_*x+h*y+i*z),t)
    return F
def legal_check(F,t):
    img=[F(p) for p in G]; assert sorted(img)==G, 'bijective'
    A=lambda p:add(F(p),neg(t))
    for gen in (enc(1,0,0),enc(0,1,0),enc(0,0,1)):
        for p in G: assert A(add(gen,p))==add(A(gen),A(p)), 'additive'
    assert t in H, 'translation in H'
    for p in G: assert F(smul(61,p))==smul(61,F(p)), 'commutes with 61 (fixed sets stay fixed)'
# ---- T1: all 23,328 H-actions are restrictions of legal G-maps; recompute singleton orbit
hmaps=[]
for a in (1,2):
  for t0 in range(3):
    for e,f,h,i in itertools.product(range(3),repeat=4):
      if (e*i-f*h)%3==0: continue
      for d,g_,t1,t2 in itertools.product(range(3),repeat=4):
        hmaps.append((a,0,0,d,e,f,g_,h,i,enc(t0,3*t1,3*t2)))
assert len(hmaps)==23328
checked=0
for k,prm in enumerate(hmaps):
    F=gmap(*prm)
    legal_check(F,prm[-1]); checked+=1
    assert all(F(h) in H for h in H)
print('T1: 23328 maps; full legality (bijection, additivity, t in H, commutes with 61) checked on',checked,'maps; all preserve H')
# all 13-subsets of H passing necessary conditions were enumerated in sing.cpp (7776, one orbit). Re-derive orbit here via real G-maps:
orbS={frozenset(gmap(*p)(s) for s in S) for p in hmaps}
print('T1: orbit of S under real G-maps restricted to H:',len(orbS))
assert len(orbS)==7776
stab=[p for p in hmaps if frozenset(gmap(*p)(s) for s in S)==S]
print('T1: stabilizer of S:',len(stab))
# ---- T2: stabilizer G-maps with all (b,c); each legal, preserves S; induced Q permutation recorded
smaps=[]
for p in stab:
    for b,c in itertools.product(range(3),repeat=2):
        q=list(p); q[1]=b; q[2]=c; F=gmap(*q); legal_check(F,q[-1])
        assert frozenset(F(s) for s in S)==S
        # Q-action well-defined: cell of F(p) depends only on cell of p
        qp={}
        for g in G: qp.setdefault(cellof(g),set()).add(cellof(F(g)))
        assert all(len(v)==1 for v in qp.values())
        smaps.append((tuple(q),{k:v.pop() for k,v in qp.items()}))
print('T2:',len(smaps),'S-stabilizing legal G-maps, all checked in full; Q-action well defined')
# ---- quotient images (from quot.py logic, recomputed) and orbit reps
cases=[list(map(int,l.split())) for l in open(P+'/cases.txt')]
reps=[tuple(c[1:]) for c in cases]
def qimg(D):
    r=[0]*27
    for x in D: r[cellof(x)]+=1
    return tuple(r)
# ---- T4: production option tables vs definitions
p243=[list(map(int,l.split()))[1:] for l in open(P+'/p243.txt').read().split('\n')[2:] if l.strip()]
tabs={k:json.load(open(str(Path(sys.argv[3])/f'choices_{k}.json'))) for k in ('DIRECT','FAST')}
assert tabs['DIRECT']==tabs['FAST']
tab=tabs['DIRECT']; assert len(tab)==8
ptab=[]
for ci,r in enumerate(reps):
    rows=tab[ci]; assert len(rows)==24
    cells=[]; prow=[]
    for row in rows:
        assert len(row)==3
        sets=[frozenset(x for j in opt for x in p243[j]) for opt in row]
        cl={cellof(x) for s in sets for x in s}; assert len(cl)==1; c=cl.pop(); cells.append(c)
        assert c not in (0,9,18)
        mine={frozenset().union(*cmb) for cmb in itertools.combinations([o for o in ORB if cellof(next(iter(o)))==c and len(o)==3], r[c]//3)}
        assert len(mine)==3 and set(sets)==mine, ('option set differs',ci,c)
        prow.append(sets)
    assert sorted(cells)==[c for c in range(27) if c not in (0,9,18)]
    # order: six-cells first then three-cells, each ascending
    assert cells==[c for c in range(27) if c not in (0,9,18) and r[c]==6]+[c for c in range(27) if c not in (0,9,18) and r[c]==3]
    ptab.append(prow)
print('T4: both kernels\' option tables = all C(3,r/3) orbit choices per nonspecial cell, 24 distinct cells, frozen order')
W=3**12; N=8*W
iv=[(4096*k, min(4096*(k+1),N)) for k in range(1038)]
assert iv[0][0]==0 and iv[-1][1]==N and all(iv[k][1]==iv[k+1][0] and iv[k][0]<iv[k][1] for k in range(1037))
print('T4: ranges [4096r,min(4096(r+1),8*3^12)), r<1038, partition [0,',N,')')
# ---- T5: end-to-end round trip of random disguised leaves
def leaf(ci,digits):
    D=set(S)
    for pos,dg in enumerate(digits): D|=ptab[ci][pos][dg]
    return frozenset(D)
def anymap():
    a=random.choice((1,2)); b,c,d,g_,t1,t2=(random.randrange(3) for _ in range(6))
    while True:
        e,f,h,i=(random.randrange(9) for _ in range(4))
        if (e*i-f*h)%3: break
    return gmap(a,b,c,d,e,f,g_,h,i,0)
hm_by_img={}
for p in hmaps:
    im=frozenset(gmap(*p)(s) for s in S)  # maps S -> im ; need inverse direction: from pattern X to S
    hm_by_img.setdefault(im,p)
trials=int(sys.argv[2]) if len(sys.argv)>2 else 300
for trial in range(trials):
    ci=random.randrange(8); digits=[random.randrange(3) for _ in range(24)]
    L=leaf(ci,digits); assert len(L)==121
    A=anymap(); tr=random.choice(G)
    D=frozenset(add(A(x),tr) for x in L)               # arbitrary automorphism + arbitrary translation in G
    # normalizer (does not know A, tr, ci, digits)
    s=0
    for x in D: s=add(s,x)
    u=smul(7,s)                                        # 121^{-1} = 7 on exponent-9 group
    D0=frozenset(add(x,neg(u)) for x in D)
    assert frozenset(smul(61,x) for x in D0)==D0, 'centering'
    X=frozenset(D0&set(H)); assert len(X)==13
    # find legal map phi with phi(X)=S: search maps p with p(S)=X, then invert by search among hmaps (group): use direct search
    phi=None
    for p in hmaps:
        F=gmap(*p)
        if frozenset(F(x) for x in X)==S: phi=F; break
    assert phi is not None, 'no singleton normalization'
    D1=frozenset(phi(x) for x in D0)
    r1=qimg(D1)
    hit=None
    for q,qp in smaps:
        F=gmap(*q); D2=frozenset(F(x) for x in D1)
        if qimg(D2) in reps: hit=(reps.index(qimg(D2)),D2); break
    assert hit, 'no rep reached'
    c2,D2=hit
    dg=[]
    for pos in range(24):
        cell=ptab[c2][pos][0]; c=cellof(next(iter(cell)))
        part=frozenset(x for x in D2 if cellof(x)==c)
        m=[k for k in range(3) if ptab[c2][pos][k]==part]; assert len(m)==1, 'leaf not in table'
        dg.append(m[0])
    assert leaf(c2,dg)==D2
    pid=c2*W+int(''.join(map(str,dg[:12])),3); assert 0<=pid<N
print('T5:',trials,'random disguised leaves normalized to (case, depth-12 ID, tail) and reproduced exactly from the production table')
