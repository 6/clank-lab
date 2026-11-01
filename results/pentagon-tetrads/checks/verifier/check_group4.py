#!/usr/bin/env python3
"""Exact independent closure check from the angles and ray in the request."""
import os
os.environ['SYMPY_GROUND_TYPES'] = 'python'
import sympy as s

p, q = s.symbols('p q', real=True)
Z, W = s.symbols('Z W')
a = [180-p-q, 180+q, 180-q, p, q]
reflex = [False, True, False, False, False]
r = [1, 2, 1, 2, 1]

def check(condition, reason):
    if not condition:
        raise RuntimeError('FAILED: ' + reason)

def star(expr):
    # Literal complex conjugate on |Z|=|W|=1.
    return s.expand(s.conjugate(expr).xreplace({s.conjugate(Z):1/Z,
                                              s.conjugate(W):1/W}))

check(s.expand(sum(a)-540) == 0, 'polygon angle sum')
# The angular region is exactly p>0, q>0, t=180-p-q>0.
t = 180-p-q
strict = []
for angle, is_reflex in zip(a, reflex):
    strict += [angle-180, 360-angle] if is_reflex else [angle, 180-angle]
check(all(x in strict for x in [p, q, t]), 'triangle constraints follow')
# Conversely each strict angular bound is a nonzero nonnegative combination
# of p, q, t, so positivity of these three implies every angular bound.
region_witnesses = []
for expr in strict:
    expr = s.expand(expr)
    ct = expr.subs({p:0, q:0}) / s.Integer(180)
    cp, cq = expr.coeff(p)+ct, expr.coeff(q)+ct
    check(all(c >= 0 for c in [cp,cq,ct]) and cp+cq+ct > 0,
          'positive triangle witness')
    check(s.expand(expr-cp*p-cq*q-ct*t) == 0, 'region witness identity')
    region_witnesses.append((expr, (cp,cq,ct)))

# Derive directions using the recurrence, without a pre-entered polynomial.
theta = [s.Integer(0)]
for angle in a[1:]:
    theta.append(s.expand(theta[-1]+180-angle))
u = []
for th in theta:
    A, B, C = th.coeff(p), th.coeff(q), th.subs({p:0,q:0})
    check(A.is_Integer and B.is_Integer and C % 180 == 0,
          'direction exponents/constants')
    u.append(s.Integer(-1)**(C/180) * Z**(2*A) * W**(2*B))
v = s.expand(sum(ri*ui for ri,ui in zip(r,u)))
check(not v.has(s.Float), 'exact symbolic coefficients')
# Clear the Laurent denominators, deriving the multiplying monomial.
terms = s.Add.make_args(v)
M = s.prod(x**(-min(term.as_powers_dict().get(x,0) for term in terms))
           for x in [Z,W])
f = s.expand(M*v)
f_star_literal = star(f)
f_reciprocal = s.expand(M*f_star_literal)
check(s.expand(M*star(M)-1) == 0, 'M is a torus unit')
check(s.expand(f+f_reciprocal-3*(M+1)) == 0,
      'reciprocal-conjugate polynomial identity')
# A separate direct separating-half-plane proof of nonvanishing.
h = s.expand(Z*W*v)
real_h = s.expand((h+star(h))/2)
check(s.expand(real_h-s.Rational(3,2)*(Z*W+1/(Z*W))) == 0,
      'direct real-part identity')

print('Angles:', a)
print('Strict region: p>0, q>0, 180-p-q>0; exact angular witnesses:', region_witnesses)
print('Theta (degrees):', theta)
print('Directions:', u)
print('v1 =', v)
print('Denominator-clearing torus unit M =', M)
print('f = M*v1 =', f)
print('Literal conjugate f_bar =', f_star_literal)
print('Reciprocal conjugate f# = M*f_bar =', f_reciprocal)
print('f + f# =', s.expand(f+f_reciprocal))
print('Re(Z*W*v1) =', real_h)
print('On the torus this equals 3*cos(pi*(p+q)/360).')
print('VERIFIED: 0<p+q<180 makes that real part strictly positive, hence v1 cannot vanish.')
print('Equivalently, a zero would force M=-1, i.e. p+q=180 mod 360, outside the open region.')
