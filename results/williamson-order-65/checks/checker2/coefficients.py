"""Certified integer spectral coefficients; Python integers only.

All intervals use units of 2^-192, with outward rounding at each operation.
Machin's pi identity and alternating arctangent series bound pi. Taylor's
cosine polynomial has remainder at most pi^142/142! < 2^-500.
"""
from math import isqrt
from pathlib import Path
Q = 1 << 192
def add(a,b): return a[0]+b[0], a[1]+b[1]
def neg(a): return -a[1], -a[0]
def mul(a,b):
    z=[x*y for x in a for y in b]
    return min(z)//Q, -((-max(z))//Q)
def div(a,n): return a[0]//n, -((-a[1])//n)
def atan(q,n):
    s=(0,0)
    for k in range(n):
        d=(2*k+1)*q**(2*k+1)
        t=(Q//d,-((-Q)//d))
        s=add(s,t if k%2==0 else neg(t))
    # Absolute remainder is less than the next term, at most one unit here.
    assert (2*n+1)*q**(2*n+1)>Q
    return s[0]-1,s[1]+1
p=add(mul((16*Q,16*Q),atan(5,160)),neg(mul((4*Q,4*Q),atan(239,50))))
def coeff(k):
    k=min(k%65,(-k)%65)
    x=div(mul(p,(2*k*Q,2*k*Q)),65)
    xx=mul(x,x); term=(Q,Q); s=term
    for j in range(1,71):
        term=neg(div(mul(term,xx),(2*j-1)*(2*j)))
        s=add(s,term)
    # Lagrange remainder after degree 140 is bounded by pi^142/142!.
    from math import factorial
    assert 4**142*Q < factorial(142)
    s=(s[0]-1,s[1]+1)
    c=neg(mul((4*Q,4*Q),s)); shift=192-40
    v=((c[0]+c[1])//2+(1<<(shift-1)))>>shift
    assert c[0] >= (v-1)<<shift and c[1] <= (v+1)<<shift
    return v
if __name__=='__main__':
    values=[coeff(k) for k in range(65)]
    Path('coefficients.h').write_text('#pragma once\n#include <cstdint>\nstatic constexpr int64_t COEFF[65]={'+','.join(map(str,values))+'};\nstatic constexpr int64_t LIMIT='+str(isqrt(260*(1<<80))+33)+';\n')
