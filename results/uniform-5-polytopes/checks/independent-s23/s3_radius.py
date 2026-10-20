"""Paper closure lemma: unique zero on the WHOLE exported class."""
from dataclasses import dataclass
from flint import arb
from geometry import ball_interval, Undecided, Impossible, positive_sqrt, encode_ball
from s3_arith import finite, square

@dataclass
class Dual:
    x: object
    d: object=0
    def __post_init__(self): self.x=arb(self.x);self.d=arb(self.d)
    def __add__(self,b):
        b=lift(b);return Dual(self.x+b.x,self.d+b.d)
    __radd__=__add__
    def __neg__(self): return Dual(-self.x,-self.d)
    def __sub__(self,b): return self+-lift(b)
    def __rsub__(self,b): return lift(b)+-self
    def __mul__(self,b):
        b=lift(b);return Dual(self.x*b.x,self.d*b.x+self.x*b.d)
    __rmul__=__mul__
    def __truediv__(self,b):
        b=lift(b)
        if b.x.contains(0): raise Undecided('closure division permits zero')
        return Dual(self.x/b.x,(self.d*b.x-self.x*b.d)/(b.x*b.x))
    def __rtruediv__(self,b): return lift(b)/self
    def sqrt(self):
        y=positive_sqrt(self.x);return Dual(y,self.d/(2*y))
    def acos(self):
        if not self.x>-1 or not self.x<1:
            raise Undecided('acos derivative domain not strictly inside (-1,1)')
        y=finite(self.x.acos(),'Arb acos failed')
        return Dual(y,-self.d/positive_sqrt(1-self.x*self.x))

def lift(x): return x if isinstance(x,Dual) else Dual(x)


def closure(s,cycle):
    """cycle={rho2, d2:[...], cos_alpha:[...]}; d2 cyclic cell order.

    cos_alpha[i] is angle between cells i-1 and i. Constants must be
    certified model enclosures, never rounded table values.
    """
    d2=cycle['d2'];ca=cycle['cos_alpha']
    if len(d2)!=len(ca) or len(d2)<3: raise ValueError('invalid cycle')
    den=(1-cycle['rho2']*s*s).sqrt()
    c=[positive_sqrt(arb(d))*s/den for d in d2]
    t=[(1-z*z).sqrt() for z in c]
    total=Dual(-2*arb.pi())
    for i,alpha in enumerate(ca):
        z=(alpha-c[i-1]*c[i])/(t[i-1]*t[i])
        total+=z.acos()
    finite(total.x);finite(total.d)
    return total


def unique_radius(interval,cycles):
    """Return explicit endpoint/derivative witness, or OPEN with reasons."""
    R=ball_interval(*interval)
    if not R>0: return {'status':'OPEN','reasons':['radius domain not positive']}
    reasons=[]
    for ci,c in enumerate(cycles):
        try:
            # Endpoints stay exact exported decimals; no narrowing to a root box.
            lo=closure(Dual(1/arb(interval[1])),c).x
            hi=closure(Dual(1/arb(interval[0])),c).x
            d=closure(Dual(1/R,1),c).d
            if ((lo>0 and hi<0) or (lo<0 and hi>0)) and (d>0 or d<0):
                return {'status':'UNIQUE','cycle':ci,'R':list(interval),
                        's_left_value':encode_ball(lo),'s_right_value':encode_ball(hi),
                        'whole_s_derivative':encode_ball(d)}
            reasons.append(f'cycle {ci}: endpoint sign or whole-class derivative unresolved')
        except (Undecided,Impossible,ValueError,ZeroDivisionError) as e:
            reasons.append(f'cycle {ci}: {e}')
    return {'status':'OPEN','R':list(interval),'reasons':reasons or ['no certified cycle supplied']}
