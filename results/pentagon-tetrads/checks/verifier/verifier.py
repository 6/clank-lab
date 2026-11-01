#!/usr/bin/env python3
"""Independent verifier, derived from the three supplied specifications.
No producer code is imported or consulted. All proof decisions are exact.
"""
import argparse, collections, concurrent.futures, copy, itertools, json, math, os, re, time, traceback
from fractions import Fraction as F
from functools import lru_cache
os.environ['SYMPY_GROUND_TYPES']='python'
import sympy as S
Z,W=S.symbols('Z W'); I=S.I
ANGLES=S.symbols('a0:5')
P,Q=S.symbols('p q')
class Failure(Exception):pass
def require(ok,msg):
    if not ok:raise Failure(msg)
def rat(x):return S.Rational(str(x))
def frac(x):return F(str(x))
def primitive(v):
    den=math.lcm(*[int(x.q) for x in v]);out=[int(x*den) for x in v];g=math.gcd(*out)
    return tuple(x//g for x in out)
def cycles(perm):
    seen=set();out=[]
    for d in sorted(perm):
        if d in seen:continue
        v=[];k=d
        while k not in seen:seen.add(k);v.append(k);k=perm[k]
        require(k==d,'map permutation cycle');out.append(v)
    return out

def derive_linear(d):
    edges=d['map']['edges'];rot={int(k):v for k,v in d['map']['rot'].items()};nd=2*len(edges)
    require(set(rot)==set(range(5)) and all(rot.values()), 'map must have four tiles and outer face 4')
    require(d['map'].get('nholes',0)==0,'map has holes')
    require(len(d['labs'])==4 and len(d['pattern'])==5 and all(type(x)==bool for x in d['pattern']),'labels or reflex pattern shape')
    require(sum(d['pattern'])<=2,'reflex pattern size')
    require(sorted(x for a in rot.values() for x in a)==list(range(nd)),'rotation darts')
    for f,ds in rot.items():
        require(all(edges[x//2][x%2]==f for x in ds),'dart origins')
    require(all(a!=b and 0<=a<5 and 0<=b<5 for a,b in edges),'dual edge faces')
    require(all(any(set(e)=={a,b} for e in edges) for a in range(4) for b in range(a+1,4)),'tile adjacencies')
    nxt={x:ds[(i+1)%len(ds)] for ds in rot.values() for i,x in enumerate(ds)}
    vs=cycles({x:nxt[x^1] for x in nxt})
    require(len(vs)-len(edges)+5==2,'map Euler characteristic')
    cs={int(k):v for k,v in d['placement']['cs'].items()};bends=d['placement']['bends']
    require(set(cs)==set(x for f in range(4) for x in rot[f]),'sector keys')
    require(len(bends)==len(edges) and all(type(b)==int and b>=0 for b in bends),'bend counts')
    for v in vs:
        fs=[edges[x//2][x%2] for x in v]
        require(len(v)>=3 and all(fs.count(f)<=1 for f in range(4)),'primal vertex conditions')
        require(sum(cs.get(x)=='S' for x in v)<=1,'multiple straight sectors')
    segs={};si=0
    for e,b in enumerate(bends):
        for k in range(b+1):segs[e,k]=si;si+=1
    corner={};bendcorner={};sides=[]
    for f in range(4):
        proper,shift=d['labs'][f];require(type(proper)==bool and 0<=shift<5,'label identification')
        seq=[]
        for dart in rot[f]:
            require(cs[dart] in ('C','S'),'sector type')
            seq.append(('v',dart,cs[dart]=='C'))
            e=dart//2;b=bends[e]
            for k in (range(b+1) if dart%2==0 else range(b,-1,-1)):
                seq.append(('s',segs[e,k],False))
                if (dart%2==0 and k<b) or (dart%2==1 and k>0):seq.append(('b',(e,k if dart%2==0 else k-1),True))
        cidx=[i for i,item in enumerate(seq) if item[2]]
        require(len(cidx)==5,'tile corner count')
        for k,idx in enumerate(cidx):
            typ,key,_=seq[idx];lab=(shift+(k if proper else -k))%5
            if typ=='v':corner[key]=lab
            else:bendcorner[f,key]=lab
            j=cidx[(k+1)%5];run=[];z=(idx+1)%len(seq)
            while z!=j:
                if seq[z][0]=='s':run.append(seq[z][1])
                z=(z+1)%len(seq)
            sides.append((lab if proper else (lab-1)%5,run))
    eq=[sum(ANGLES)-540];ineq=[]
    for v in vs:
        expr=sum(ANGLES[corner[x]] if cs.get(x)=='C' else 180 for x in v if x in cs)-360
        if any(edges[x//2][x%2]==4 for x in v):ineq.append(expr)
        else:eq.append(expr)
    for e,(f,g) in enumerate(edges):
        if f<4 and g<4:
            for k in range(bends[e]):eq.append(ANGLES[bendcorner[f,(e,k)]]+ANGLES[bendcorner[g,(e,k)]]-360)
    A,b=S.linear_eq_to_matrix(eq,ANGLES)
    require(A.rank()==3 and A.row_join(b).rank()==3,'angle family not two-dimensional or inconsistent')
    free=[ANGLES.index(S.Symbol(x)) for x in d['free']]
    require(len(free)==2 and len(set(free))==2,'free angle names')
    sol=S.solve(eq+[ANGLES[free[0]]-P,ANGLES[free[1]]-Q],ANGLES)
    require(len(sol)==5,'free angles do not parameterise family')
    named={ANGLES[free[0]]:P,ANGLES[free[1]]:Q}
    require(set(d['sol'])==set(str(x) for x in ANGLES if x not in named),'solution keys')
    for a in ANGLES:
        val=named[a] if a in named else S.sympify(d['sol'][str(a)],locals={str(x):x for x in ANGLES}).subs(named)
        require(S.expand(sol[a]-val)==0,'angle formula '+str(a))
        require(all(c.is_Integer for c in S.Poly(sol[a],P,Q).coeffs()),'noninteger angle formula')
    rows=[]
    for i,a in enumerate(ANGLES):
        for ex in [-a,a-360,180-a if d['pattern'][i] else a-180]:
            ex=S.expand(ex.subs(sol));rows.append((ex.coeff(P),ex.coeff(Q),-ex.subs({P:0,Q:0})))
    for ex in dict.fromkeys(ineq):
        ex=S.expand(ex.subs(sol));rows.append((ex.coeff(P),ex.coeff(Q),-ex.subs({P:0,Q:0})))
    require(collections.Counter(rows)==collections.Counter(tuple(map(rat,x)) for x in d['cert']['rows']),'region rows differ')
    LM=S.zeros(20,5+si)
    for j,(lab,run) in enumerate(sides):
        LM[j,lab]=-1
        for x in run:LM[j,5+x]+=1
    return sol,rows,LM,{'vertices':vs,'angle_equations':[str(x) for x in eq],'segment_count':si,'total_angle_rank':A.rank(),'rank_beyond_polygon_sum':A.rank()-1,'raw_outer_inequalities':len(ineq),'distinct_outer_inequalities':len(set(ineq))}

def cone_rays(LM):
    # Every positive vector in ker LM is a conical combination of orthant
    # extreme rays. In dimension k, each such ray has k-1 independent
    # active coordinate hyperplanes. Enumerate all, then project exactly.
    ns=LM.nullspace();N=S.Matrix.hstack(*ns);k=N.cols
    constraints=list(dict.fromkeys(primitive(list(N.row(i))) for i in range(N.rows) if any(N.row(i))))
    out=set();allr=[]
    for inds in itertools.combinations(range(len(constraints)),k-1):
        M=S.Matrix([constraints[i] for i in inds]) if k>1 else S.zeros(0,k)
        if M.rank()!=k-1:continue
        nv=M.nullspace()[0];v=N*nv
        if all(x<=0 for x in v):v=-v
        if not all(x>=0 for x in v):continue
        vv=primitive(list(v));allr.append(vv)
        if any(vv[:5]):out.add(primitive([S.Rational(x) for x in vv[:5]]))
    require(all(any(v[i]>0 for v in allr) for i in range(LM.cols)),'no strictly positive full length solution')
    return sorted(out),k,sorted(set(allr))

def incone(v,rr):
    # Caratheodory: a representation uses an independent subset.
    for k in range(1,min(5,len(rr))+1):
        for ids in itertools.combinations(range(len(rr)),k):
            M=S.Matrix.hstack(*[S.Matrix(rr[i]) for i in ids])
            if M.rank()!=k:continue
            try:x=M.gauss_jordan_solve(S.Matrix(v))[0]
            except ValueError:continue
            if all(t>=0 for t in x):return True
    return False

def star(f):return S.Add(*[S.conjugate(c)*Z**(-a)*W**(-b) for (a,b),c in lterms(f).items()])
def dot(f,g):return S.expand((star(f)*g+star(g)*f)/2)
def cross(f,g):return S.expand((star(f)*g-star(g)*f)/(2*I))
def lterms(f):
    out={}
    for term in S.Add.make_args(S.expand(f)):
        pd=term.as_powers_dict();a=pd.get(Z,S.Integer(0));b=pd.get(W,S.Integer(0));c=S.simplify(term/Z**a/W**b)
        out[a,b]=out.get((a,b),0)+c
    return {k:S.simplify(v) for k,v in out.items() if v!=0}

def realify(f,paired):
    if paired:return S.expand(f*star(f))
    tt=lterms(f);az=[a for a,b in tt];bw=[b for a,b in tt];sz=min(az)+max(az);sw=min(bw)+max(bw)
    a,b=next(iter(tt));unit=S.simplify(S.conjugate(tt[sz-a,sw-b])/tt[a,b])
    require(unit in [1,-1,I,-I],'factor has unsupported conjugation unit')
    root={S.Integer(1):S.Integer(1),S.Integer(-1):I,I:(1+I)/S.sqrt(2),-I:(1-I)/S.sqrt(2)}[unit]
    g=S.expand(root*Z**(-S.Rational(sz,2))*W**(-S.Rational(sw,2))*f)
    require(S.expand(star(g)-g)==0,'factor not real on torus')
    return g

def derive_quantities(d,sol):
    th=0;u=[S.Integer(1)]
    for i in range(1,5):
        th=S.expand(th+180-sol[ANGLES[i]])
        a,b,c=th.coeff(P),th.coeff(Q),th.subs({P:0,Q:0})
        require(c%180==0,'direction constant')
        u.append(S.Integer(-1)**int(c/180)*Z**(2*a)*W**(2*b))
    rays=d['rays'];m=len(rays);v=[S.expand(sum(r[i]*u[i] for i in range(5))) for r in rays]
    qs={}
    if m<=2:
        for j in range(m):qs['N'+str(j+1)]=dot(v[j],v[j])
    if m>=2:qs['c12']=cross(v[0],v[1]);qs['d12']=dot(v[0],v[1])
    if m==3:
        qs.update(c23=cross(v[1],v[2]),c31=cross(v[2],v[0]),d13=dot(v[0],v[2]),d23=dot(v[1],v[2]))
        mu=[qs['c23'],qs['c31'],qs['c12']]
    elif m==2:mu=[-qs['d12'],qs['N1']]
    else:mu=[S.Integer(1)]
    ll=[S.expand(sum(mu[j]*rays[j][i] for j in range(m))) for i in range(5)]
    for i in range(5):
        for j in range(i+2,5):
            if i==0 and j==4:continue
            cr=cross(u[i],u[j])
            if cr==0:continue
            dp=sum(ll[k]*u[k] for k in range(i,j))
            a,b,c,e=cross(dp,u[j]),S.expand(ll[i]*cr),cross(dp,u[i]),S.expand(ll[j]*cr)
            for name,val in [('A',a),('B',b),('BA',b-a),('C',c),('E',e),('EC',e-c)]:qs[name+str(i)+str(j)]=S.expand(val)
    require(not any(x.has(S.Float) for x in [*u,*qs.values()]),'inexact symbolic direction or quantity')
    return qs,u

def check_factors(d,qs):
    cc=d['cert']['quantities'];require(set(cc)==set(qs),'quantity names differ: '+str(set(cc)^set(qs)))
    factors={};qfac={}
    for name,(k,ff) in cc.items():
        k=rat(k);require(k!=0,'zero factorisation constant '+name);prod=k;entries=[]
        for fs,ex,paired in ff:
            require(type(ex)==int and ex>0 and type(paired)==bool,'factor metadata '+name)
            key=(fs,paired)
            if key not in factors:
                f=S.sympify(fs,locals={'Z':Z,'W':W,'I':I});require(f.free_symbols<={Z,W},'factor symbols')
                require(all(a.is_Integer and b.is_Integer and S.re(c).is_Rational and S.im(c).is_Rational for (a,b),c in lterms(f).items()),'Gaussian rational Laurent factor')
                factors[key]=realify(f,paired)
            prod*=factors[key]**ex;entries.append((key,ex))
        require(S.expand(prod-qs[name])==0,'factorisation identity '+name)
        qfac[name]=(1 if k>0 else -1,entries)
    return factors,qfac


from rigorous import Factor,JointZeros,hull,cliprows,feasible,contained,polygonrows,polyarea,centroid

def qposs(qfac,domains,name):
    sg,entries=qfac[name];out={sg}
    for key,ex in entries:
        vv={s**ex for s in domains[key]};out={a*b for a in out for b in vv}
    return out

def sign_close(m,qfac,domains,poly,rows,joint,kind,node_limit=100000):
    names=list(qfac) if kind=='generic' else (['N1','N2'] if m==2 else ['c12','c23','c31','d12','d13','d23'])
    keys=set(k for n in names for k,e in qfac[n][1]);dd={k:set(domains[k]) for k in keys}
    frequency=collections.Counter(k for n in names for k,e in qfac[n][1])
    cnames=['N1'] if m==1 else ['c12','d12'] if m==2 else ['c12','c23','c31']
    for n in cnames:
        for k,e in qfac[n][1]:frequency[k]+=100
    pairs=sorted(n[1:] for n in qfac if re.fullmatch('B[0-4][0-4]',n))
    forbidden=set();nodes=0;joint_rejections=0
    def recurse():
        nonlocal nodes,joint_rejections
        nodes+=1
        if nodes>node_limit:return {'reason':'finite sign enumeration node limit','nodes':nodes}
        for a,b in forbidden:
            if dd[a]=={0} and dd[b]=={0}:return None
        qq={n:qposs(qfac,dd,n) for n in names}
        if kind=='generic':
            if m==1:possible=0 in qq['N1']
            elif m==2:possible=0 in qq['c12'] and -1 in qq['d12']
            else:possible=any(all(s in qq[n] for n in ['c12','c23','c31']) for s in [-1,1])
            if not possible:return None
            for ij in pairs:
                bb=qq['B'+ij];ee=qq['E'+ij]
                if 0 in bb or 0 in ee:continue
                if all(qq[n+ij]<={0,b} for b in bb for n in ['A','BA']) and all(qq[n+ij]<={0,e} for e in ee for n in ['C','EC']):return None
        else:
            if m==2:possible=all(0 in qq[n] for n in ['N1','N2'])
            else:possible=all(0 in qq[n] for n in ['c12','c23','c31']) and any(qq[n]&{-1,0} for n in ['d12','d13','d23'])
            if not possible:return None
        remaining=[k for k in keys if len(dd[k])>1]
        # On any branch, impossible simultaneous factor zeros refute the entire
        # sign assignment. Test eagerly once all closure factors are assigned.
        if not remaining:
            zeros=[k for k in keys if dd[k]=={0}]
            for a,b in itertools.combinations(sorted(zeros),2):
                if joint.excludes(a,b,poly,rows):
                    forbidden.add((a,b));joint_rejections+=1;return None
            return {'reason':'a sign assignment survives the sound necessary conditions','signs':{str(k):next(iter(dd[k])) for k in sorted(keys)},'quantity_signs':{n:list(vv) for n,vv in qq.items()}}
        key=max(remaining,key=lambda k:(frequency[k],str(k)));old=dd[key]
        for s in sorted(old,key=lambda s:(s!=0,s)):
            dd[key]={s};res=recurse()
            if res is not None:dd[key]=old;return res
        dd[key]=old;return None
    witness=recurse()
    return witness,{'sign_nodes':nodes,'joint_zero_rejections':joint_rejections}

class Replayer:
    def __init__(self,d,rows,factors,qfac):
        self.d=d;self.rows=[tuple(map(F,row)) for row in rows];self.qfac=qfac
        self.factors={k:Factor(k) for k in factors};self.joint=JointZeros(self.factors)
        self.region=cliprows([(F(-1),F(-1)),(F(361),F(-1)),(F(361),F(361)),(F(-1),F(361))],self.rows)
        require(feasible(self.region,self.rows),'angle region empty')
        self.logs=[];self.failures=[];self.stats=collections.Counter();self.exclusion_polys=[]
    def close(self,poly,where,polar=None):
        t=time.monotonic();domains={};evidence={}
        for k,f in self.factors.items():
            ss,why=f.signs(poly,self.rows,self.region,polar)
            require(bool(ss),'empty sign domain for '+str(k))
            domains[k]=ss;evidence[str(k)]=[sorted(ss),why];self.stats['rule '+why]+=1
        m=len(self.d['rays']);proof={};failure=None
        for branch in (['generic'] if m==1 else ['generic','degenerate']):
            witness,stats=sign_close(m,self.qfac,domains,poly,self.rows,self.joint,branch)
            proof[branch]=stats
            if witness is not None:
                failure={'where':where,'cell':poly,'branch':branch,'witness':witness};self.failures.append(failure)
                break
        rec={'where':where,'cell':poly,'status':'CLOSED' if failure is None else 'UNRESOLVED','proof':proof,'signs':evidence,'seconds':time.monotonic()-t}
        self.logs.append(rec);self.stats['C']+=1
        return failure is None
    def tree(self,tokens,where,root,makepoly,rho=None,polar_info=None):
        tok=re.findall(r'\(X\d+\)|[SOC?]',tokens)
        require(''.join(tok)==tokens,'invalid token syntax '+where)
        stack=[root]
        for idx,token in enumerate(tok):
            require(bool(stack),'extra token '+where+' index '+str(idx))
            box=stack.pop();poly=cliprows(makepoly(box),self.rows);here={'tree':where,'token_index':idx,'box':box}
            if token=='S':
                x0,x1,y0,y1=box;dx=(x1-x0)/(rho if rho else 1);dy=y1-y0
                if dx>=dy:
                    mid=(x0+x1)/2;stack.extend([(x0,mid,y0,y1),(mid,x1,y0,y1)])
                else:
                    mid=(y0+y1)/2;stack.extend([(x0,x1,y0,mid),(x0,x1,mid,y1)])
                self.stats['S']+=1
            elif token=='O':
                require(not feasible(poly,self.rows),'O cell nonempty '+str(here));self.stats['O']+=1
            elif token=='C':
                if not feasible(poly,self.rows):
                    self.logs.append({'where':here,'cell':poly,'status':'EMPTY'});self.stats['C empty']+=1;continue
                polar=None
                if polar_info:
                    c,da,db=polar_info;s0,s1,t0,t1=box
                    wp=[tuple((1-t)*a+t*b for a,b in zip(da,db)) for t in [t0,t1]]
                    polar=(c,wp,s1)
                self.close(poly,here,polar)
            elif token.startswith('(X'):
                ex=int(token[2:-1]);require(0<=ex<len(self.exclusion_polys),'exclusion index '+str(here))
                require(contained(poly,self.exclusion_polys[ex]),'exclusion containment '+str(here));self.stats['X']+=1
            else:raise Failure('open ? leaf '+str(here))
        require(not stack,'missing leaf tokens '+where+' remaining cells '+str(stack[-3:]))
    def exclusions(self):
        for ei,ex in enumerate(self.d['cert']['exclusions']):
            c=tuple(map(frac,ex['c']));rho=frac(ex['rho']);require(rho>0,'exclusion rho')
            original=[tuple(map(frac,p)) for p in ex['U']];U=hull(original)
            require(polyarea(U)>0 and len(set(original))==len(original),'exclusion polygon invalid')
            # Input is an ordered convex polygon, possibly with collinear points.
            require(abs(polyarea(original))==polyarea(U),'exclusion U not convex or not ordered')
            oriented=original if polyarea(original)>0 else list(reversed(original))
            require(contained(original,oriented),'exclusion U violates convex edge halfplanes')
            triangles=[];pieces=[]
            for pi,pc in enumerate(ex['pieces']):
                da=tuple(map(frac,pc['dA']));db=tuple(map(frac,pc['dB']))
                tri=hull([c,tuple(c[k]+rho*da[k] for k in range(2)),tuple(c[k]+rho*db[k] for k in range(2))])
                require(polyarea(tri)>0 and contained(tri,U),'exclusion piece outside U or degenerate')
                for prev in triangles:require(polyarea(cliprows(tri,polygonrows(prev)))==0,'exclusion pieces overlap')
                triangles.append(tri);pieces.append((pi,pc,da,db))
                # Supplied zero-factor hints are assertions, not trusted input.
                for fs in pc.get('zero_factors',[]):
                    ks=[k for k in self.factors if k[0]==fs];require(ks,'unknown zero factor hint')
                    require(all(self.factors[k].zero(c) for k in ks),'false zero-factor hint '+fs)
            require(sum(map(polyarea,triangles))==polyarea(U),'pieces do not cover U exactly')
            self.exclusion_polys.append(U)
            if feasible([c],self.rows):self.close([c],{'exclusion':ei,'center':True})
            for pi,pc,da,db in pieces:
                def makepoly(box,c=c,da=da,db=db):
                    s0,s1,t0,t1=box
                    return hull([tuple(c[k]+s*((1-t)*da[k]+t*db[k]) for k in range(2)) for s,t in [(s0,t0),(s1,t0),(s1,t1),(s0,t1)]])
                self.tree(pc['tokens'],f'exclusion {ei} piece {pi}',(F(0),rho,F(0),F(1)),makepoly,rho,(c,da,db))
    def run(self):
        self.exclusions()
        self.tree(self.d['cert']['main_tokens'],'main',(F(-1),F(361),F(-1),F(361)),lambda b:[(b[0],b[2]),(b[1],b[2]),(b[1],b[3]),(b[0],b[3])])
        self.stats['resultants']=self.joint.calls
        return self.failures

def jsondefault(x):
    if isinstance(x,(F,S.Rational)):return str(x)
    if isinstance(x,set):return sorted(x)
    if isinstance(x,S.Basic):return str(x)
    raise TypeError(type(x).__name__)
def writejson(path,d):
    with open(path,'w') as f:json.dump(d,f,default=jsondefault,indent=2)
def verify_case(d,outdir=None):
    t=time.monotonic();cpu0=time.process_time();result={'case':d['case'],'status':'FAILED','timings':{}};replay=None
    try:
        tt=time.monotonic();sol,rows,LM,meta=derive_linear(d);result['timings']['linear']=time.monotonic()-tt
        tt=time.monotonic();rr,k,fullr=cone_rays(LM)
        require(1<=len(d['rays'])<=3 and d['cert']['m']==len(d['rays']),'length cone ray count')
        require(all(len(r)==5 and all(type(x)==int and x>=0 for x in r) and any(r) for r in d['rays']),'invalid nonnegative integer ray')
        require(all(incone(r,d['rays']) for r in rr) and all(incone(r,rr) for r in d['rays']),'length cone mismatch')
        result['timings']['length_cone']=time.monotonic()-tt
        tt=time.monotonic();qs,u=derive_quantities(d,sol);factors,qfac=check_factors(d,qs);result['timings']['symbolic']=time.monotonic()-tt
        result['derived']={'angles':{str(a):str(v) for a,v in sol.items()},'region_rows':rows,'directions':list(map(str,u)),'length_cone_generators':rr,'full_cone_dimension':k,'quantity_count':len(qs),'factor_count':len(factors),'length_equalities':LM.tolist(),'full_length_cone_generators':fullr,'quantities':{name:str(q) for name,q in qs.items()},**meta}
        tt=time.monotonic();replay=Replayer(d,rows,factors,qfac);failures=replay.run();result['timings']['replay']=time.monotonic()-tt
        result['stats']=dict(replay.stats);result['unresolved_leaves']=failures;result['joint_zero_proofs']=replay.joint.proofs
        if failures:result['first_failing_check']='leaf sign closure '+str(failures[0]['where'])
        else:result['status']='VERIFIED'
    except Exception as e:
        result['first_failing_check']=str(e);result['exception']=type(e).__name__
        if not isinstance(e,Failure):result['traceback']=traceback.format_exc()
    result['timings']['total']=time.monotonic()-t;result['timings']['cpu']=time.process_time()-cpu0
    if outdir:
        os.makedirs(outdir,exist_ok=True);writejson(os.path.join(outdir,f"case-{d['case']}.json"),result)
        if replay:writejson(os.path.join(outdir,f"case-{d['case']}-leaves.json"),replay.logs)
    return result

def available_cpus():
    count=len(os.sched_getaffinity(0)) if hasattr(os,'sched_getaffinity') else os.cpu_count() or 1
    try:
        with open('/sys/fs/cgroup/cpu.max') as f:quota,period=f.read().split()
        if quota!='max':count=min(count,max(1,math.ceil(int(quota)/int(period))))
    except (OSError,ValueError):pass
    return count

def main():
    ap=argparse.ArgumentParser();ap.add_argument('input');ap.add_argument('--output',default='results');ap.add_argument('--workers',type=int,default=available_cpus());ap.add_argument('--cases',nargs='*',type=int);args=ap.parse_args()
    with open(args.input) as f:data=[json.loads(l) for l in f if l.strip()]
    if args.cases is not None:data=[d for d in data if d['case'] in args.cases]
    os.makedirs(args.output,exist_ok=True);t=time.monotonic();results=[]
    with concurrent.futures.ProcessPoolExecutor(max_workers=args.workers) as pool:
        fs={pool.submit(verify_case,d,args.output):d['case'] for d in data}
        for future in concurrent.futures.as_completed(fs):
            r=future.result();results.append(r);print(f"case {r['case']}: {r['status']} ({r['timings']['total']:.3f}s) "+r.get('first_failing_check',''),flush=True)
    results.sort(key=lambda r:r['case']);writejson(os.path.join(args.output,'summary.json'),{'wall_seconds':time.monotonic()-t,'workers':args.workers,'cases':results})
    return 0 if all(r['status']=='VERIFIED' for r in results) else 1
if __name__=='__main__':raise SystemExit(main())
