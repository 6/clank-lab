#!/usr/bin/env python3
"""Independent exact b1 checker: grouped samples and uncoloured-orbit cover.

No other local modules, solver, search, or stored product tables imported.
All coefficient arithmetic uses Python/GMP integers. NumPy handles only
finite bit masks and arrays of arbitrary-precision integer objects.
"""
import argparse,hashlib,itertools as it,json,time
from fractions import Fraction
from pathlib import Path
import numpy as np
try:
    from gmpy2 import mpq as rational
except ImportError:
    rational=Fraction


def need(ok,message):
    if not ok:raise ValueError(message)


TR={n:list(it.combinations(range(n),3)) for n in range(7)}
TI={n:{t:j for j,t in enumerate(TR[n])} for n in range(7)}


def relabel(e,c,n,order):
    newe=sum(((e>>TI[n][tuple(sorted(order[v] for v in t))])&1)<<j for j,t in enumerate(TR[len(order)]))
    newc=sum(((c>>v)&1)<<j for j,v in enumerate(order))
    return (newe<<len(order))|newc


def flagcanon(code,n,k):
    e,c=code>>n,code&((1<<n)-1)
    return min(relabel(e,c,n,list(range(k))+list(p)) for p in it.permutations(range(k,n)))


def cycles(n):
    return {sum(1<<TI[n][tuple(sorted((p[j],p[(j+1)%5],p[(j+2)%5])))] for j in range(5))
            for p in it.permutations(range(n),5)} if n>=5 else set()


def psd_rational(Q):
    n=len(Q);need(all(len(row)==n for row in Q),'PSD dimensions')
    need(all(isinstance(x,int) for row in Q for x in row),'PSD integers')
    need(all(Q[i][j]==Q[j][i] for i in range(n) for j in range(i)),'PSD symmetry')
    A=[[rational(v) for v in row] for row in Q];live=list(range(n));rank=0
    while live:
        need(all(A[i][i]>=0 for i in live),'negative PSD Schur diagonal')
        pivot=next((i for i in live if A[i][i]>0),None)
        if pivot is None:
            need(all(A[i][j]==0 for i in live for j in live),'indefinite zero diagonal');break
        remaining=[i for i in live if i!=pivot];d=A[pivot][pivot]
        for at,i in enumerate(remaining):
            for j in remaining[at:]:
                A[i][j]-=A[i][pivot]*A[pivot][j]/d;A[j][i]=A[i][j]
        live=remaining;rank+=1
    return rank


def cover(classpairs,plant=False):
    ps=list(it.permutations(range(6)))
    images=[[TI[6][tuple(sorted(p[v] for v in t))] for t in TR[6]] for p in ps]
    forbidden=cycles(6);seen=bytearray(1<<20);expected=set();labelled=0;uncoloured=0
    for e in range(1<<20):
        if seen[e] or any(e&f==f for f in forbidden):continue
        bits=[i for i in range(20) if e>>i&1]
        transformed=[sum(1<<row[i] for i in bits) for row in images]
        orbit=set(transformed);need(e==min(orbit),'uncoloured representative');uncoloured+=1;labelled+=len(orbit)
        for v in orbit:seen[v]=1
        aut=[p for p,v in zip(ps,transformed) if v==e];colseen=set()
        for c in range(64):
            if c in colseen:continue
            expected.add((e,c))
            colseen.update(sum(((c>>v)&1)<<i for i,v in enumerate(p)) for p in aut)
    actual=set(classpairs)
    if plant:actual.discard((0,0))
    need(actual==expected,'coloured class cover gap or duplicate orbit')
    need((uncoloured,labelled,len(expected))==(835,371229,40547),'cover totals')
    return labelled*64


def main():
    parser=argparse.ArgumentParser();parser.add_argument('directory',type=Path);parser.add_argument('--plant-cover-gap',action='store_true')
    parser.add_argument('--allow-control-bound',action='store_true',help='positive bound rehearsal; not a zero-bound claim')
    args=parser.parse_args();start=time.monotonic();root=args.directory
    cert=json.loads((root/'certificate.json').read_text())
    sos=cert['schema']=='p33-b1-sos-v1'
    need(cert['schema'] in ('p33-b1-v1','p33-b1-sos-v1') and cert['coefficient'] in ([1,1],[3999,4000]),'statement')
    boundnum,boundden=cert['bound'];need(type(boundnum)==int and type(boundden)==int and boundnum>=0 and boundden>0,'bound')
    need((cert['bound']==[0,1] or args.allow_control_bound) and cert['cut_bound']==[2,5] and cert['density_bound']==[464101615,1000000000],'bound and hypotheses')
    S,D=cert['scale'],cert['class_denominator'];need(type(S)==int and S>0 and D==180000000000,'denominators')
    data={}
    for f in cert['files']:
        name=f['file'];need('/' not in name and name not in data,'file naming')
        raw=(root/name).read_bytes();need(len(raw)==f['bytes'] and hashlib.sha256(raw).hexdigest()==f['sha256'],'manifest')
        data[name]=json.loads(raw)
    blocks=[data[f'block-{i:02d}.json'] for i in range(38)];ranks=[]
    # Independently enumerate the complete rooted flag bases on 4 and 5 vertices.
    groups={};f5=cycles(5)
    for n,k in [(4,1),(4,2),(5,4)]:
        for e in range(1<<len(TR[n])):
            if n==5 and any(e&f==f for f in f5):continue
            for c in range(1<<n):
                typ=relabel(e,c,n,list(range(k)));key=flagcanon((e<<n)|c,n,k)
                groups.setdefault((n,k,typ),set()).add(key)
    U=720000000000;need(U%D==0 and U%boundden==0,'sampling denominator')
    Q4=np.zeros((256,128,128),dtype=object);Q2=np.zeros((4,256,256),dtype=object);E2=np.zeros((4,256),dtype=object)
    y=cert['inequality_multipliers'];eq=cert['equality_multipliers']
    need(len(y)==12847 and all(type(v)==int and v>=0 for v in y),'negative multiplier')
    need(len(eq)==120 and all(type(v)==int for v in eq),'free multipliers')
    eqoff=0;types=set();canonical2=[flagcanon(v,4,2) for v in range(256)]
    for bi,b in enumerate(blocks):
        n,k,typ,flags=[b[key] for key in ('n','k','type','flags')]
        if sos:
            dimension=len(flags);Q=[[0 for _ in flags] for _ in flags]
            for term in b['terms']:
                weight=term['weight'];need(type(weight)==int and weight>=0,'PSD SOS coefficient')
                need(set(term)=={'weight','vector'} or set(term)=={'weight','matrix'},'SOS shape')
                if 'matrix' in term:
                    seed=term['matrix'];need(len(seed)==dimension,'seed dimension');psd_rational(seed)
                    for row in range(dimension):
                        for col in range(dimension):Q[row][col]+=weight*seed[row][col]
                else:
                    vec=term['vector'];need(len(vec)==dimension and all(type(x)==int for x in vec),'SOS vector dimension')
                    nonzero=[j for j,x in enumerate(vec) if x]
                    for row in nonzero:
                        for col in nonzero:Q[row][col]+=weight*vec[row]*vec[col]
        else:Q=b['matrix']
        need((n,k,typ) not in types and (n,k) in [(4,2),(5,4)],'PSD type');types.add((n,k,typ))
        need(flags==sorted(groups[(n,k,typ)]),'complete PSD flag basis');ranks.append(None if sos else psd_rational(Q));ids={v:i for i,v in enumerate(flags)}
        if k==2:
            need((bi,typ) in [(0,0),(1,2),(2,3)],'degree block order')
            raw=[v for v in range(256) if v&3==typ]
            for a in raw:
                i=ids[canonical2[a]];E2[typ,a]=eq[eqoff+i]*(U//720)
                for bcode in raw:Q2[typ,a,bcode]=Q[i][ids[canonical2[bcode]]]*(U//720)
            eqoff+=len(flags)
        else:
            extension=[2,4,5,7,8,9]
            codes=[((f>>4)&1)*64+sum(((f>>5>>j)&1)<<at for at,j in enumerate(extension)) for f in flags]
            for i,a in enumerate(codes):
                for j,bcode in enumerate(codes):Q4[typ,a,bcode]=Q[i][j]*(U//720)
    need(eqoff==120,'degree multiplier count')
    L=np.zeros((2,256),dtype=object);loff=0
    for colour,b in enumerate(cert['local_bases']):
        need((b['n'],b['k'],b['type'])==(4,1,colour),'local type');flags=b['flags'];need(flags==sorted(groups[(4,1,colour)]),'local basis')
        ids={v:i for i,v in enumerate(flags)}
        for raw in range(256):
            if raw&1==colour:L[colour,raw]=y[loff+ids[flagcanon(raw,4,1)]]*(U//720)
        loff+=len(flags)
    need(loff==80 and len(cert['local_bases'])==2,'local count')
    globalflags=cert['global_basis']['flags'];need(globalflags==[0,1,3,7,8,9,11,15],'global basis')
    cut=np.zeros(16,dtype=object);density=np.zeros(16,dtype=object)
    for j,f in enumerate(globalflags):cut[f]=y[80+j]*(U//3600);density[f]=y[88+j]
    # Descriptor semantics reconstructed by nested quantifiers, independently
    # of the first checker's flat-index division formula.
    descriptors=[]
    for tau in range(2):
        for pi in range(1,256):descriptors.append([len(descriptors),tau,-1,3,pi])
    for tau in range(2):
        for rc in range(8):
            for C in range(1,4):
                for pi in range(1,256):descriptors.append([len(descriptors),tau,rc,C,pi])
    need(cert['cl_predicates']==descriptors,'CL predicate mismatch')
    upper=np.zeros((50,256),dtype=object)
    for row in range(50):upper[row,1:]=y[97+row*255:97+(row+1)*255]
    for bit in range(8):
        for mask in range(256):
            if not(mask>>bit&1):upper[:,mask]+=upper[:,mask|(1<<bit)]
    CL=np.zeros((2,8,4,256),dtype=object)
    for tau in range(2):
        for rc in range(8):
            for used in range(1,4):
                CL[tau,rc,used]=upper[tau].copy()
                for C in range(1,4):
                    if C&used==used:CL[tau,rc,used]+=upper[2+(tau*8+rc)*3+C-1]
                CL[tau,rc,used]*=U//720
    classes=[]
    for j in range(20):classes+=data[f'classes-{j:02d}.json']
    need(all(len(v)==(3 if sos else 4) and all(type(x)==int for x in v) for v in classes),'class record')
    need(len(classes)==40547 and len({(v[0],v[1]) for v in classes})==40547,'class count')
    masks=np.array([v[0] for v in classes],dtype=np.uint32);colours=np.array([v[1] for v in classes],dtype=np.uint16)
    need(all(0<=int(e)<1<<20 and 0<=int(c)<64 for e,c in zip(masks,colours)),'mask range')
    edges=[((masks>>j)&1).astype(np.int16) for j in range(20)];cols=[((colours>>j)&1).astype(np.int16) for j in range(6)]
    def edge(a,b,c):return edges[TI[6][tuple(sorted((a,b,c)))]]
    def raw4(order):
        c=sum(cols[v]<<i for i,v in enumerate(order));e=sum(edge(*(order[v] for v in t))<<j for j,t in enumerate(TR[4]));return (e<<4)|c
    def type4(root):return raw4(root)
    def extension(root,z):return (cols[z]<<6)+sum(edge(root[a],root[b],z)<<j for j,(a,b) in enumerate(it.combinations(range(4),2)))
    bad=np.zeros(len(classes),dtype=np.int16);missing=bad.copy()
    for t in TR[6]:
        count=sum(cols[v] for v in t);present=edge(*t);bad+=present*((count==0)|(count==2));missing+=(1-present)*(count==1)
    cn,cd=cert['coefficient'];targets=(bad.astype(object)*cd-missing.astype(object)*cn)*(D//(20*cd))
    need(all(int(t)==v[2] for t,v in zip(targets,classes)),'wrong class coefficient')
    total=np.zeros(len(classes),dtype=object)
    # Four-root PSD blocks: 360 root orders, two interchangeable free orders.
    for root in it.permutations(range(6),4):
        a,b=sorted(set(range(6))-set(root));total+=2*Q4[type4(root),extension(root,a),extension(root,b)]
    # Two-root PSD and regularity: 30 root orders, six unordered splits,
    # four internal free permutations in each split.
    for x,u in it.permutations(range(6),2):
        rest=sorted(set(range(6))-{x,u});typ=cols[x]+2*cols[u]
        for pair in it.combinations(rest,2):
            others=sorted(set(rest)-set(pair));fa=raw4((x,u)+pair);fb=raw4((x,u,*others))
            total+=4*Q2[typ,fa,fb]
            total+=4*(edge(x,*pair)-edge(u,*pair))*E2[typ,fb]
    # Local assumptions: six roots, ten pairs, multiplicity twelve.
    for x in range(6):
        rest=sorted(set(range(6))-{x})
        for pair in it.combinations(rest,2):
            others=sorted(set(rest)-set(pair));count=sum(cols[v] for v in pair)
            sign=edge(x,*pair)*((count==1).astype(np.int16)-(count==0).astype(np.int16))*(1-2*cols[x])
            total+=12*sign*L[cols[x],raw4((x,*others))]
    # Global assumptions: twenty triples, multiplicity thirty-six.
    for A in it.combinations(range(6),3):
        B=sorted(set(range(6))-set(A));count=sum(cols[v] for v in B);flag=(edge(*B)<<3)+(1<<count)-1
        good=edge(*A)*(sum(cols[v] for v in A)==1)
        total+=36*(5*good-2)*cut[flag]
        # Cast before multiplication: these coefficients exceed int16.
        coefficient=edge(*A).astype(object)*1000000000-464101615
        total+=36*coefficient*(density[flag]+y[96])
    # CL-3: 120 root orders, sum six free orders analytically.
    for x,u,v in it.permutations(range(6),3):
        a,b,d=sorted(set(range(6))-{x,u,v});ab,ad,bd=edge(x,a,b),edge(x,a,d),edge(x,b,d)
        val=2*(ab*ad*(1-bd)+ab*bd*(1-ad)+ad*bd*(1-ab))-6*ab*ad*bd*edge(a,b,d)
        mask=np.zeros(len(classes),dtype=np.int16);used=mask.copy()
        for z in (a,b,d):
            pattern=4*edge(x,u,z)+2*edge(x,v,z)+edge(u,v,z);mask|=1<<pattern;used|=1<<cols[z]
        rc=cols[x]+2*cols[u]+4*cols[v];total+=val*CL[edge(x,u,v),rc,used,mask]
    gap=S*(U//boundden)*boundnum-targets*S*(U//D)-total
    if sos:need(all(v>=0 for v in gap),'negative exact class slack')
    else:
        slacks=np.array([v[3] for v in classes],dtype=object);need(all(type(v)==int and v>=0 for v in slacks),'negative slack')
        need(np.all(gap==slacks*(U//D)),'exact class identity mismatch')
    labelled=cover([(v[0],v[1]) for v in classes],args.plant_cover_gap)
    print(json.dumps({'status':'POSITIVE_BOUND_CONTROL_B' if boundnum else 'EXACT_B1_CHECKER_B','classes':40547,'labelled':labelled,'coefficient':[cn,cd],
                      'bound':[boundnum,boundden],'psd_ranks':ranks,'wall_seconds':time.monotonic()-start}),flush=True)

if __name__=='__main__':
    try:main()
    except (ValueError,KeyError,TypeError,AssertionError,IndexError) as ex:
        print('REJECT:',ex,flush=True);raise SystemExit(1)
