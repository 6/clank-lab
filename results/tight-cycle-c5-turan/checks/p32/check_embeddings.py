#!/usr/bin/env python3
"""Independent exact verifier using edge sets and ordered root embeddings.

No imports from the numerical writer, mask checker or solver. Completeness
uses recursive edge-set enumeration with incremental forbidden-cycle tests;
coefficients average all 720 root embeddings (including automorphisms).
"""
from itertools import combinations, permutations, product
from pathlib import Path
import sys, json, time

V=tuple(range(6));TRIPLES=tuple(combinations(V,3))
ROOTS=tuple(permutations(V,3))

def insist(b,msg):
    if not b:raise ValueError(msg)

def prepare(c):
    insist(c['format']=='p32-exact-v1' and c['rho']==[2,5],'statement')
    p,w,f,L=[c[k] for k in ['prob_scale','weight_scale','factor_scale','scale']]
    insist(all(type(x)==int and x>0 for x in [p,w,f,L]),'scale')
    y=c['multipliers']
    insist(len(y)==9511 and all(type(x)==int and x>=0 for x in y),'multipliers')
    sels=c['selectors'];insist(sum(s['weight'] for s in sels)==w,'lambda sum')
    for s in sels:
        insist(s['tau'] in [0,1] and type(s['weight'])==int and s['weight']>=0,'lambda')
        insist(len(s['pi'])==8 and all(type(a)==int and 0<=a<=p for a in s['pi']),'pi domain')
    blocks=c['blocks'];insist(len(blocks)==6,'block count')
    bmaps=[]
    for number,b in enumerate(blocks):
        insist(b['name']==('k4e'+str(number) if number<5 else 'k2'),'block name')
        flags=b['flags'];insist(flags==sorted(set(flags)),'flag coordinates')
        m=b['matrix'];u=b['factor'];n=len(flags)
        insist(len(m)==len(u)==n and all(len(row)==n for row in m+u),'matrix dimensions')
        insist(all(type(v)==int for row in m+u for v in row),'matrix scalars')
        # Accumulate rank-one outer products, rather than testing entries
        # through row dot products as in the other implementation.
        gram=[[0]*n for _ in range(n)]
        for k in range(n):
            for a in range(n):
                for bidx in range(a,n):gram[a][bidx]+=u[a][k]*u[bidx][k]
        for a in range(n):
            insist(m[a][a]>=0,'PSD diagonal')
            for bidx in range(a,n):
                insist(m[a][bidx]==m[bidx][a]==gram[a][bidx],'PSD witness')
        bmaps.append(dict(zip(flags,range(n))))
    denominators=[5*p**3*w,w,w*p**2,10000*w,f**2]
    insist(all(L%d==0 for d in denominators),'denominator divisibility')
    ss,cs,gs,ds,qs=[L//d for d in denominators]
    # Superset zeta transform, independently summing CL restrictions.
    CL=[]
    for family in range(2):
        per=[]
        for tau in range(2):
            a=[0]+y[family*510+tau*255:family*510+(tau+1)*255]
            for bit in range(8):
                for subset in range(256):
                    if not subset&(1<<bit):a[subset]+=a[subset|(1<<bit)]
            per.append([v*cs for v in a])
        CL.append(per)
    G=[[[0 for _ in range(32)] for _ in range(32)] for _ in range(16)]
    at=1020
    for k in range(16):
        sets=[]
        for a in range(32):
            sets.append((a,))
            sets.extend((a,b) for b in range(a+1,32))
        sets.append(tuple(range(32)))
        insist(len(sets)==529,'restriction enumeration')
        for S in sets:
            value=y[at]*p*p*gs;at+=1
            for a,b in product(S,repeat=2):G[k][a][b]+=value
    insist(at==9484 and len(c['cuts'])==25,'G3 layout')
    for r in c['cuts']:
        k=r['k'];beta=r['w']
        insist(type(k)==int and 0<=k<16 and len(beta)==32,'G3 root')
        insist(all(type(v)==int and v>=0 for v in beta),'G3 nonnegative weight')
        for a,b in product(range(32),repeat=2):G[k][a][b]+=y[at]*beta[a]*beta[b]*gs
        at+=1
    # Expand the random selector by the three possible missing vertices.
    S={}
    for tau in [0,1]:
        for pat in product(range(8),repeat=3):
            numerator=0
            for s in sels:
                if s['tau']!=tau:continue
                probs=[s['pi'][v] for v in pat]
                poly=sum((p-probs[j])*probs[(j+1)%3]*probs[(j+2)%3] for j in range(3))
                numerator+=s['weight']*5*poly*ss
            S[tau,pat]=numerator
    subtract=[2*p**3*ss*sum(s['weight'] for s in sels if s['tau']==t) for t in [0,1]]
    def coefficient(edges,embedding):
        def e(a,b,d):return int(tuple(sorted((embedding[a],embedding[b],embedding[d]))) in edges)
        tau=e(0,1,2);target=e(3,4,5)
        patterns=tuple(sum(mult*e(a,b,z) for mult,(a,b) in zip((4,2,1),((0,1),(0,2),(1,2)))) for z in (3,4,5))
        left=target*S[tau,patterns]-subtract[tau]
        union=sum(1<<i for i in set(patterns))
        k4=all(e(*t) for t in ((0,3,4),(0,3,5),(0,4,5),(3,4,5)))
        ch=bool(e(0,3,4) and e(0,3,5) and not e(0,4,5))
        row3=int(ch)-int(k4);row4=int(ch and not target)-int(k4)
        right=CL[0][tau][union]*row3+CL[1][tau][union]*row4
        code=lambda z:sum(mult*e(a,b,z) for mult,(a,b) in zip((16,8,4,2,1),((0,1),(0,2),(1,2),(3,1),(3,2))))
        right+=G[8*tau+patterns[0]][code(4)][code(5)]*row4
        right+=(10000*tau-4641)*(y[-2] if target else y[-1])*ds
        rootbits=tuple(e(*t) for t in combinations(range(4),3))
        if rootbits in [(1,)*ne+(0,)*(4-ne) for ne in range(5)]:
            ne=sum(rootbits)
            flag=lambda z:sum((1<<i)*e(a,b,z) for i,(a,b) in enumerate(combinations(range(4),2)))
            a,b=flag(4),flag(5)
            insist(a in bmaps[ne] and b in bmaps[ne],'four-root flag support')
            right+=qs*blocks[ne]['matrix'][bmaps[ne][a]][bmaps[ne][b]]
        flag2=lambda a,b:4*(e(0,1,a)+e(0,1,b))+2*e(0,a,b)+e(1,a,b)
        a,b=flag2(2,3),flag2(4,5)
        insist(a in bmaps[5] and b in bmaps[5],'two-root flag support')
        right+=qs*blocks[5]['matrix'][bmaps[5][a]][bmaps[5][b]]
        return left,right
    return coefficient

def forbidden_cycles():
    cycles=set()
    for missing in V:
        vertices=tuple(v for v in V if v!=missing)
        first=vertices[0]
        for rest in permutations(vertices[1:]):
            if rest[0]>rest[-1]:continue
            order=(first,)+rest
            cycles.add(frozenset(tuple(sorted(order[j] for j in (i%5,(i+1)%5,(i+2)%5))) for i in range(5)))
    return cycles

def labelled_histogram(cycles):
    # Branch on absence/presence of each triple; only inspect cycles whose
    # final triple has just been added. This is a different cover enumeration.
    last=[[] for _ in TRIPLES];position={e:i for i,e in enumerate(TRIPLES)}
    for cycle in cycles:last[max(position[e] for e in cycle)].append(cycle)
    counts=[0]*21;edges=set()
    def visit(i):
        if i==20:counts[len(edges)]+=1;return
        visit(i+1)
        edges.add(TRIPLES[i])
        if not any(cycle<=edges for cycle in last[i]):visit(i+1)
        edges.remove(TRIPLES[i])
    visit(0)
    return counts

def check(c,plant_cover_gap=False):
    begin=time.time();coefficient=prepare(c);cycles=forbidden_cycles()
    insist(len(c['classes'])==len(c['coefficients'])==len(c['slacks'])==835,'class counts')
    canon=set();counts=[0]*21
    for j,mask in enumerate(c['classes']):
        insist(type(mask)==int and 0<=mask<2**20,'class encoding')
        edges=frozenset(e for i,e in enumerate(TRIPLES) if mask&(1<<i))
        insist(not any(cycle<=edges for cycle in cycles),'forbidden cycle')
        left=right=0;images=set()
        for root in ROOTS:
            remaining=tuple(v for v in V if v not in root)
            for outside in permutations(remaining):
                emb=root+outside
                a,b=coefficient(edges,emb);left+=a;right+=b
                # Canonical edge-set keys prove distinct orbits, independent
                # of the minimum-bitmask convention of the first checker.
                images.add(tuple(sorted(tuple(sorted(emb[v] for v in e)) for e in edges)))
        key=min(images);insist(key not in canon,'duplicate orbit');canon.add(key)
        counts[len(edges)]+=len(images)
        insist(left==c['coefficients'][j],'class coefficient')
        insist(type(c['slacks'][j])==int and c['slacks'][j]>=0,'class slack')
        insist(left-right-720*c['margin']==c['slacks'][j],'coefficient identity')
    if plant_cover_gap:counts[0]-=1
    insist(counts==labelled_histogram(cycles),'independent cover histogram')
    insist(type(c['margin'])==int and c['margin']>=0,'certificate value')
    print(json.dumps({'checker':'embeddings','classes':len(canon),'labelled':sum(counts),
                     'rho':[2,5],'margin_numerator':c['margin'],'margin_denominator':c['scale'],
                     'min_slack_numerator':min(c['slacks']),'seconds':time.time()-begin}),flush=True)

if __name__=='__main__':
    try:check(json.loads(Path(sys.argv[1]).read_text()),plant_cover_gap='--plant-cover-gap' in sys.argv[2:])
    except (ValueError,KeyError,IndexError,TypeError,AssertionError) as ex:
        print('REJECT:',ex);sys.exit(1)
