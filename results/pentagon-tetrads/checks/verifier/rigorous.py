"""Exact convex geometry, cyclotomic tests, and outward interval sign rules.
mpmath.iv is the only interval engine; no Arb/python-flint is used.
"""
from fractions import Fraction as F
from functools import lru_cache
import math, itertools, os
os.environ['SYMPY_GROUND_TYPES']='python'
import sympy as S
from mpmath import iv
iv.dps=40
Z,W=S.symbols('Z W');I=S.I

def iq(q):
    q=F(q);return iv.mpf(q.numerator)/q.denominator

def endpoint(t):
    sign,man,ex,bc=t
    if bc<0:raise ValueError('nonfinite interval endpoint')
    return (-1 if sign else 1)*F(int(man))*(F(2)**int(ex))
def bounds(x):return tuple(endpoint(t) for t in x._mpi_)
def positive(x):return x.a>0
def negative(x):return x.b<0
def containszero(x):return not positive(x) and not negative(x)
def signset(x):
    lo,hi=bounds(x);return ({-1} if lo<0 else set())|({0} if lo<=0<=hi else set())|({1} if hi>0 else set())
def interval(a,b):
    la=bounds(iq(a))[0];hb=bounds(iq(b))[1]
    return iv.mpf([iq(la).a,iq(hb).b])
def polyarea(poly):return sum(a[0]*b[1]-a[1]*b[0] for a,b in zip(poly,poly[1:]+poly[:1]))/2 if len(poly)>2 else F(0)
def hull(points):
    pts=sorted(set(points))
    if len(pts)<=1:return pts
    def cr(o,a,b):return (a[0]-o[0])*(b[1]-o[1])-(a[1]-o[1])*(b[0]-o[0])
    low=[];up=[]
    for p in pts:
        while len(low)>1 and cr(low[-2],low[-1],p)<=0:low.pop()
        low.append(p)
    for p in reversed(pts):
        while len(up)>1 and cr(up[-2],up[-1],p)<=0:up.pop()
        up.append(p)
    return low[:-1]+up[:-1]
def clip(poly,row):
    if not poly:return []
    a,b,c=row;out=[]
    for x,y in zip(poly,poly[1:]+poly[:1]):
        fx=a*x[0]+b*x[1]-c;fy=a*y[0]+b*y[1]-c
        if fx<=0:out.append(x)
        if (fx<0<fy) or (fy<0<fx):
            r=fx/(fx-fy);out.append((x[0]+r*(y[0]-x[0]),x[1]+r*(y[1]-x[1])))
    return hull(out)
def cliprows(poly,rows):
    for row in rows:
        poly=clip(poly,row)
        if not poly:break
    return poly
def centroid(poly):return tuple(sum(p[k] for p in poly)/len(poly) for k in range(2))
def feasible(poly,rows):
    if not poly:return False
    x,y=centroid(poly);return all(a*x+b*y<c for a,b,c in rows)
def polygonrows(poly):
    return [(b[1]-a[1],a[0]-b[0],(b[1]-a[1])*a[0]+(a[0]-b[0])*a[1]) for a,b in zip(poly,poly[1:]+poly[:1])]
def contained(poly,U):return all(a*x+b*y<=c for x,y in poly for a,b,c in polygonrows(U))
def phase_range(poly,a,b,c=0):
    vals=[a*x+b*y+c for x,y in poly];return min(vals),max(vals)
def line_possible(poly,rows,a,b,c):
    section=clip(clip(poly,(a,b,c)),(-a,-b,-c));return feasible(section,rows)
def ivphase(poly,a,b,c=0):
    lo,hi=phase_range(poly,a,b,c);return interval(lo,hi)*iv.pi/180

def cosine_signs(poly,rows,a,b,c):
    """Exact signs of cos(pi*(a p+b q+c)/180), respecting open R."""
    lo,hi=phase_range(poly,a,b,c);out=set()
    # A constant phase at a zero is handled exactly, avoiding numeric pi.
    if lo==hi:
        if (lo-90)%180==0:return {0}
        return {1 if (lo+90)%360<180 else -1}
    first=math.floor((lo-90)/180)-1;last=math.ceil((hi-90)/180)+1
    for k in range(first,last+1):
        r=F(90+180*k)
        if lo<=r<=hi and line_possible(poly,rows,a,b,r-c):out.add(0)
    # Every interval between consecutive zeros has a constant known sign.
    cuts=sorted(set([lo,hi]+[F(90+180*k) for k in range(first,last+1) if lo<90+180*k<hi]))
    for l,h in zip(cuts,cuts[1:]):
        t=(l+h)/2;out.add(1 if (t+90)%360<180 else -1)
    return out

def raw_terms(f):
    out={}
    for term in S.Add.make_args(S.expand(f)):
        pd=term.as_powers_dict();a=pd.get(Z,S.Integer(0));b=pd.get(W,S.Integer(0));c=S.simplify(term/Z**a/W**b)
        out[a,b]=out.get((a,b),0)+c
    return [(F(a),F(b),F(S.re(c)),F(S.im(c))) for (a,b),c in out.items() if c!=0]

class Factor:
    def __init__(self,key):
        self.key=key;self.text,self.paired=key
        self.f=S.sympify(self.text,locals={'Z':Z,'W':W,'I':I})
        tt=raw_terms(self.f);self.delta=F(0)
        if not self.paired:
            sz=min(t[0] for t in tt)+max(t[0] for t in tt);sw=min(t[1] for t in tt)+max(t[1] for t in tt)
            dd={(a,b):S.Rational(r)+I*S.Rational(i) for a,b,r,i in tt};a,b,r,i=tt[0]
            unit=S.simplify(S.conjugate(dd[sz-a,sw-b])/dd[a,b]);self.delta={S.Integer(1):F(0),S.Integer(-1):F(90),I:F(45),-I:F(-45)}[unit]
            tt=[(a-sz/2,b-sw/2,r,i) for a,b,r,i in tt]
        # Frequencies below are in degrees, including the 1/2 in Z,W.
        self.terms=[(a/2,b/2,r,i) for a,b,r,i in tt]
        self.rterms=self.terms if self.paired else [(a,b,r*(1 if a==b==0 else 2),i*(1 if a==b==0 else 2)) for a,b,r,i in self.terms if a>0 or (a==0 and b>=0)]
        self.binomial=(not self.paired and len(self.terms)==2 and len(self.rterms)==1 and self.rterms[0][:2]!=(0,0))
        self.zero_cache={};self.order_cache={}
    def evaluate(self,poly):
        re=iv.mpf(0);im=iv.mpf(0)
        for a,b,r,i in self.rterms:
            ph=ivphase(poly,a,b,self.delta);co=iv.cos(ph);sn=iv.sin(ph)
            re+=iq(r)*co-iq(i)*sn
            if self.paired:im+=iq(r)*sn+iq(i)*co
        return re,im
    def zero(self,c,dp=0,dq=0):
        key=(tuple(c),dp,dq)
        if key in self.zero_cache:return self.zero_cache[key]
        data=[];N=4
        for a,b,r,i in self.terms:
            phase=(a*c[0]+b*c[1]+self.delta)/360
            N=math.lcm(N,phase.denominator);data.append((phase,r*a**dp*b**dq,i*a**dp*b**dq))
        zz=S.Symbol('z');coeff={}
        for ph,r,i in data:
            e=int(ph*N)%N
            coeff[e]=coeff.get(e,F(0))+r
            e=(e+N//4)%N;coeff[e]=coeff.get(e,F(0))+i
        poly=S.Poly.from_dict({(e,):S.Rational(v) for e,v in coeff.items() if v},zz,domain=S.QQ)
        result=poly.rem(S.Poly(S.cyclotomic_poly(N,zz),zz)).is_zero
        self.zero_cache[key]=result;return result
    def order(self,c,maxorder=5):
        c=tuple(c)
        if c in self.order_cache:return self.order_cache[c]
        for k in range(maxorder+1):
            if any(not self.zero(c,i,k-i) for i in range(k+1)):
                self.order_cache[c]=k;return k
        self.order_cache[c]=None;return None
    def taylor(self,c,wp,poly_smax,k):
        """F(c+s*w)/s^k, w in convex wp, 0<s<=poly_smax.
        The homogeneous leading term uses rectangular w intervals; order 1
        instead takes the convex hull of endpoint values, retaining direction
        correlation. The remainder follows the real exponential Taylor bound.
        """
        lam=iv.pi/180;maxs=iq(poly_smax)
        if k==1:
            vals_re=[];vals_im=[]
            for x,y in wp:
                rr=iv.mpf(0);ii=iv.mpf(0)
                for a,b,r,i in self.terms:
                    phase=iq(a*c[0]+b*c[1]+self.delta)*lam;co=iv.cos(phase);sn=iv.sin(phase)
                    vr=iq(r)*co-iq(i)*sn;vi=iq(r)*sn+iq(i)*co
                    ph=iq(a*x+b*y);rr-=vi*ph;ii+=vr*ph
                vals_re.append(rr*lam);vals_im.append(ii*lam)
            re=interval(min(bounds(t)[0] for t in vals_re),max(bounds(t)[1] for t in vals_re))
            im=interval(min(bounds(t)[0] for t in vals_im),max(bounds(t)[1] for t in vals_im))
        else:
            wx=interval(min(x for x,y in wp),max(x for x,y in wp));wy=interval(min(y for x,y in wp),max(y for x,y in wp))
            re=iv.mpf(0);im=iv.mpf(0)
            for a,b,r,i in self.terms:
                phase=iq(a*c[0]+b*c[1]+self.delta)*lam;co=iv.cos(phase);sn=iv.sin(phase)
                vr=iq(r)*co-iq(i)*sn;vi=iq(r)*sn+iq(i)*co
                ph=(iq(a)*wx+iq(b)*wy)**k*lam**k/math.factorial(k)
                kk=k%4
                re+=(vr if kk==0 else -vi if kk==1 else -vr if kk==2 else vi)*ph
                im+=(vi if kk==0 else vr if kk==1 else -vi if kk==2 else -vr)*ph
        B=iv.mpf(0)
        for a,b,r,i in self.terms:
            amp=iv.sqrt(iq(r*r+i*i));ph=max(abs(a*x+b*y) for x,y in wp)
            B+=amp*iq(ph)**(k+1)
        rem=maxs*lam**(k+1)*B/math.factorial(k+1)
        rb=bounds(rem)[1];return re+interval(-rb,rb),im+interval(-rb,rb)
    def signs(self,poly,rows,vertices,polar=None):
        if self.binomial:
            a,b,r,i=self.rterms[0]
            if r and not i:delta=0 if r>0 else 180
            elif i and not r:delta=90 if i>0 else -90
            else:raise ValueError('nonaxial binomial coefficient')
            return cosine_signs(poly,rows,a,b,self.delta+delta),'exact phase'
        # Exact point evaluation at cyclotomic centers.
        if len(poly)==1 and self.zero(poly[0]):return ({0} if not self.paired else {0}),'exact cyclotomic zero'
        re,im=self.evaluate(poly)
        if self.paired:
            if not containszero(re) or not containszero(im):return {1},'complex interval'
            ss={0,1}
        else:
            ss=signset(re)
            if len(ss)==1:return ss,'real interval'
        if polar is not None:
            c,wp,smax=polar;k=self.order(c)
            if k is not None and k>0:
                tr,ti=self.taylor(c,wp,smax,k)
                if self.paired:
                    if not containszero(tr) or not containszero(ti):return {1},'polar Taylor order '+str(k)
                else:
                    ts=signset(tr)
                    if len(ts)==1:return ts,'polar Taylor order '+str(k)
        # A cell is in the cone generated by its vertex displacements at c.
        # Normalising those displacements by L1 norm yields w in their convex
        # hull, with radial s at most the maximum vertex L1 norm.
        for c in vertices:
            if not self.zero(c):continue
            dirs=[];smax=F(0)
            for x,y in poly:
                dx=x-c[0];dy=y-c[1];norm=abs(dx)+abs(dy)
                if norm:dirs.append((dx/norm,dy/norm));smax=max(smax,norm)
            if not dirs:continue
            # If c itself belongs to the domain its zero cannot be discarded.
            if feasible([c],rows) and (contained([c],poly) if len(poly)>=3 else c in poly):continue
            tr,ti=self.taylor(c,dirs,smax,1)
            if self.paired:
                if not containszero(tr) or not containszero(ti):return {1},'vertex Taylor'
            else:
                ts=signset(tr)
                if len(ts)==1:return ts,'vertex Taylor'
        return ss,'undetermined interval'

class JointZeros:
    def __init__(self,factors):self.factors=factors;self.calls=0;self.algebra={};self.proofs=[]
    @lru_cache(maxsize=None)
    def transformed(self,k1,k2,axis):
        f=self.factors[k1].f;g=self.factors[k2].f
        # Shift Laurent monomials. Such shifts are units on the torus.
        for symbol in [Z,W]:
            for which in [0,1]:
                h=f if which==0 else g
                mn=min(S.expand(t).as_powers_dict().get(symbol,0) for t in S.Add.make_args(S.expand(h)))
                h=S.expand(h*symbol**(-mn))
                if which==0:f=h
                else:g=h
        elim=W if axis==0 else Z;x=Z if axis==0 else W
        res=S.resultant(f,g,elim)
        if res==0:return None
        self.algebra[k1,k2,axis]=str(res)
        self.calls+=1
        rp=S.Poly(res,x);deg=rp.degree();t=S.Symbol('t',real=True)
        expr=S.expand(sum(c*(1+I*t)**e[0]*(1-I*t)**(deg-e[0]) for e,c in rp.terms()))
        re=S.Poly(S.re(expr).expand(),t,domain=S.QQ);im=S.Poly(S.im(expr).expand(),t,domain=S.QQ)
        return S.gcd(re,im)
    def excludes(self,k1,k2,poly,rows):
        if k1==k2:return False
        k1,k2=sorted([k1,k2])
        for axis in [0,1]:
            lo=min(p[axis] for p in poly);hi=max(p[axis] for p in poly)
            # All p,q are strict interior angles. This chart covers 0<=angle<360.
            if lo<0 or hi>360:continue
            pp=self.transformed(k1,k2,axis)
            if pp is None:continue
            if pp.degree()==0:
                self.proofs.append({'factors':[k1,k2],'axis':axis,'angle_range':[lo,hi],'resultant':self.algebra[k1,k2,axis],'tangent_polynomial':str(pp.as_expr()),'root_count':0})
                return True
            # Chart pole Z=-1 is possible only at angle 360, forbidden by R.
            if hi==360 and line_possible(poly,rows,1-axis,axis,F(360)):continue
            low=F(0) if lo==0 else bounds(iv.tan(iq(lo)*iv.pi/720))[0]
            high=S.oo if hi==360 else S.Rational(bounds(iv.tan(iq(hi)*iv.pi/720))[1])
            qq=pp;dropped=[]
            # Drop exact endpoint roots only when that coordinate line misses R.
            for angle,val in [(F(0),F(0)),(F(180),F(1))]:
                if lo<=angle<=hi and (angle==lo or angle==hi) and not line_possible(poly,rows,1-axis,axis,angle):
                    linear=S.Poly(qq.gens[0]-S.Rational(val),qq.gens[0])
                    while qq.degree()>0 and qq.eval(S.Rational(val))==0:
                        qq=qq.exquo(linear);dropped.append(angle)
            root_count=qq.count_roots(S.Rational(low),high)
            if root_count==0:
                self.proofs.append({'factors':[k1,k2],'axis':axis,'angle_range':[lo,hi],'resultant':self.algebra[k1,k2,axis],'tangent_polynomial':str(pp.as_expr()),'excluded_endpoint_angles':dropped,'reduced_tangent_polynomial':str(qq.as_expr()),'rational_tangent_interval':[low,str(high)],'root_count':0})
                return True
        return False
