#!/usr/bin/env python3
"""Standalone exact mask checker. No search or solver imports.

Enumerates labelled masks, takes distinct isomorphism orbits, and averages
the exact integer coefficient expression on each orbit. The common class
denominator is 720*scale. All certificate entries are integers.
"""
import itertools as it
import json, sys, time
from pathlib import Path

TR = list(it.combinations(range(6),3)); TI={t:i for i,t in enumerate(TR)}
PAIRS=list(it.combinations(range(4),2))
PERMS=list(it.permutations(range(6)))
IMAGES=[[TI[tuple(sorted(p[v] for v in t))] for t in TR] for p in PERMS]
CYCLES=set()
for p in it.permutations(range(6),5):
    CYCLES.add(sum(1<<TI[tuple(sorted((p[i],p[(i+1)%5],p[(i+2)%5])))] for i in range(5)))

def require(test, message):
    if not test: raise ValueError(message)

def compile_certificate(c):
    require(c['rho']==[2,5], 'rho')
    P,W,F=c['prob_scale'],c['weight_scale'],c['factor_scale']
    scale=c['scale']
    require(all(isinstance(v,int) and v>0 for v in [P,W,F,scale]),'scales')
    require(sum(s['weight'] for s in c['selectors'])==W,'selector weight sum')
    for s in c['selectors']:
        require(s['tau'] in (0,1) and s['weight']>=0 and len(s['pi'])==8,'selector data')
        require(all(isinstance(v,int) and 0<=v<=P for v in s['pi']),'selector probability')
    y=c['multipliers']; require(len(y)==9511,'row count')
    require(all(isinstance(v,int) and v>=0 for v in y),'negative multiplier')
    require(len(c['cuts'])==25,'cut count')
    for r in c['cuts']:
        require(0<=r['k']<16 and len(r['w'])==32 and all(isinstance(v,int) and v>=0 for v in r['w']),'G3 weighting')
    # Gram witnesses prove rational PSD without floating point.
    for j,b in enumerate(c['blocks']):
        Q,U,used=b['matrix'],b['factor'],b['flags']; f=len(used)
        require(b['name']==(['k4e'+str(e) for e in range(5)]+['k2'])[j],'block order')
        require(len(set(used))==f and used==sorted(used),'block flags')
        require(len(Q)==len(U)==f and all(len(r)==f for r in Q+U),'block shape')
        require(all(isinstance(v,int) for r in Q+U for v in r),'block integer')
        for a in range(f):
            require(Q[a][a]>=0,'non-PSD diagonal')
            for bidx in range(f):
                require(Q[a][bidx]==sum(U[a][k]*U[bidx][k] for k in range(f)),'PSD Gram mismatch')
    require(len(c['blocks'])==6,'six PSD blocks')
    denoms=[5*P**3*W,W,W*P*P,10000*W,F*F]
    require(all(scale%d==0 for d in denoms),'common denominator')
    sl,cl,gr,de,ps=[scale//d for d in denoms]
    # Aggregate all CL subset restrictions by their union of observed patterns.
    cltab=[[[0]*256 for _ in range(2)] for _ in range(2)]
    for family in range(2):
        for tau in range(2):
            off=family*510+tau*255
            for seen in range(256):
                cltab[family][tau][seen]=cl*sum(y[off+pi-1] for pi in range(1,256) if pi&seen==seen)
    # Aggregate quadratic G3 forms; indicator restrictions use weights P.
    G=[[[0]*32 for _ in range(32)] for _ in range(16)]
    idx=1020
    for k in range(16):
        for s in range(32):
            G[k][s][s]+=y[idx]*P*P;idx+=1
            for t in range(s+1,32):
                v=y[idx]*P*P;idx+=1
                for a,b in [(s,s),(s,t),(t,s),(t,t)]:G[k][a][b]+=v
        v=y[idx]*P*P;idx+=1
        for s in range(32):
            for t in range(32):G[k][s][t]+=v
    require(idx==9484,'G3 index')
    for r in c['cuts']:
        v=y[idx];idx+=1;k=r['k'];w=r['w']
        for s in range(32):
            for t in range(32):G[k][s][t]+=v*w[s]*w[t]
    for k in range(16):
        for s in range(32):
            for t in range(32):G[k][s][t]*=gr
    stab=[[[[0]*8 for _ in range(8)] for _ in range(8)] for _ in range(2)]
    for tau in range(2):
        for a,b,d in it.product(range(8),repeat=3):
            val=0
            for s in c['selectors']:
                if s['tau']!=tau:continue
                x,z,v=[s['pi'][p] for p in (a,b,d)]
                poly=x*z*(P-v)+x*(P-z)*v+(P-x)*z*v
                val+=s['weight']*5*poly*sl
            stab[tau][a][b][d]=val
    dsub=[2*P**3*sl*sum(s['weight'] for s in c['selectors'] if s['tau']==tau) for tau in range(2)]
    block_maps=[{v:i for i,v in enumerate(b['flags'])} for b in c['blocks']]
    def evaluate(mask):
        e=lambda a,b,d:(mask>>TI[tuple(sorted((a,b,d)))])&1
        tau=e(0,1,2);edge=e(3,4,5)
        patterns=[4*e(0,1,z)+2*e(0,2,z)+e(1,2,z) for z in (3,4,5)]
        a,b,d=patterns
        left=stab[tau][a][b][d]*edge-dsub[tau]
        seen=(1<<a)|(1<<b)|(1<<d)
        K=e(0,3,4)*e(0,3,5)*e(0,4,5)*edge
        cherry=e(0,3,4)*e(0,3,5)*(1-e(0,4,5))
        right=cltab[0][tau][seen]*(cherry-K)+cltab[1][tau][seen]*(cherry*(1-edge)-K)
        pat=lambda z:16*e(0,1,z)+8*e(0,2,z)+4*e(1,2,z)+2*e(3,1,z)+e(3,2,z)
        right+=G[tau*8+patterns[0]][pat(4)][pat(5)]*(cherry*(1-edge)-K)
        right+=de*(10000*tau-4641)*(y[-2]*edge+y[-1]*(1-edge))
        root=sum(e(*t)<<i for i,t in enumerate(it.combinations(range(4),3)))
        if root in (0,1,3,7,15):
            j=(0,1,3,7,15).index(root)
            fa=sum(e(a,b,4)<<i for i,(a,b) in enumerate(PAIRS));fb=sum(e(a,b,5)<<i for i,(a,b) in enumerate(PAIRS))
            require(fa in block_maps[j] and fb in block_maps[j],'missing flag')
            right+=ps*c['blocks'][j]['matrix'][block_maps[j][fa]][block_maps[j][fb]]
        f2=lambda a,b:4*(e(0,1,a)+e(0,1,b))+2*e(0,a,b)+e(1,a,b)
        fa,fb=f2(2,3),f2(4,5)
        require(fa in block_maps[5] and fb in block_maps[5],'missing two-root flag')
        right+=ps*c['blocks'][5]['matrix'][block_maps[5][fa]][block_maps[5][fb]]
        return left,right
    return evaluate

def orbit(mask):
    bits=[i for i in range(20) if mask>>i&1]
    return {sum(1<<img[i] for i in bits) for img in IMAGES}

def check(c, emit=True, plant_cover_gap=False):
    start=time.time(); evaluate=compile_certificate(c)
    reps=c['classes'];require(reps==sorted(set(reps)) and len(reps)==835,'class list')
    require(len(c['coefficients'])==len(c['slacks'])==835,'coefficient count')
    all_masks=set();mins=[]
    for j,rep in enumerate(reps):
        orb=orbit(rep);require(rep==min(orb),'class canonical form')
        require(not any(rep&cy==cy for cy in CYCLES),'C5 class')
        require(not (orb&all_masks),'overlapping classes');all_masks.update(orb)
        left=right=0
        for mask in orb:
            a,b=evaluate(mask);left+=a;right+=b
        require(720%len(orb)==0,'orbit size')
        left*=720//len(orb);right*=720//len(orb)
        require(left==c['coefficients'][j],'wrong class coefficient')
        require(left-right==720*c['margin']+c['slacks'][j],'class identity')
        require(c['slacks'][j]>=0,'negative slack');mins.append(c['slacks'][j])
    # Exhaustive labelled cover, independently of the certificate class list.
    if plant_cover_gap:all_masks.discard(0)
    for mask in range(1<<20):
        if mask not in all_masks:
            require(any(mask&cy==cy for cy in CYCLES),'cover gap')
    require(c['margin']>=0,'negative margin')
    result={'checker':'masks','classes':len(reps),'labelled':len(all_masks),'rho':[2,5],
            'margin_numerator':c['margin'],'margin_denominator':c['scale'],
            'min_slack_numerator':min(mins),'seconds':time.time()-start}
    if emit:print(json.dumps(result),flush=True)
    return result

if __name__=='__main__':
    try: check(json.loads(Path(sys.argv[1]).read_text()),plant_cover_gap='--plant-cover-gap' in sys.argv[2:])
    except (ValueError,KeyError,IndexError,TypeError,AssertionError) as ex:
        print('REJECT:',ex);sys.exit(1)
