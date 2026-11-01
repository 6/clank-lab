"""Group 4 of the closure stage (m = 1; representative: case 8 of cls.json).

Claim: the ray vector v1 = sum_i r_i u_i never vanishes on the open region,
so the prototile cannot close. Checked here from the case data alone:
angles a = (180 - p - q, 180 + q, 180 - q, p, q) with reflex pattern
(F, T, F, F, F), ray r = (1, 2, 1, 2, 1); the region forces 0 < a_0 < 180,
i.e. 0 < p + q < 180.
"""
import sympy as sp

p, q = sp.symbols('p q', real=True)
Z, W = sp.symbols('Z W')  # Z = exp(i p/2), W = exp(i q/2), p, q in degrees
a = [180 - p - q, 180 + q, 180 - q, p, q]
r = [1, 2, 1, 2, 1]
th = [sp.Integer(0)]
for i in range(1, 5):
    th.append(sp.expand(th[-1] + 180 - a[i]))
# u_i = exp(i th_i) = (-1)^(c/180) Z^(2 A) W^(2 B)
u = []
for t in th:
    P = sp.Poly(t, p, q)
    A, B, C = P.coeff_monomial(p), P.coeff_monomial(q), P.coeff_monomial(1)
    assert C % 180 == 0
    u.append((-1) ** int(C / 180) * Z ** (2 * int(A)) * W ** (2 * int(B)))
v1 = sp.expand(sum(ri * ui for ri, ui in zip(r, u)))
f = sp.expand(v1 * Z ** 2 * W ** 2)          # polynomial, same zeros on the torus
# reciprocal conjugate: on the torus f* = Z^2 W^2 conj(f); f = 0 iff f* = 0
fstar = sp.expand(Z ** 2 * W ** 2 * sp.conjugate(f).subs(
    {sp.conjugate(Z): 1 / Z, sp.conjugate(W): 1 / W}, simultaneous=True))
comb = sp.expand(f + fstar)
print('f      =', f)
print('f*     =', fstar)
print('f + f* =', sp.factor(comb))
assert sp.expand(comb - 3 * (Z ** 2 * W ** 2 + 1)) == 0
# A common zero on the torus needs Z^2 W^2 = exp(i (p + q)) = -1, i.e.
# p + q = 180 (mod 360); the region has 0 < p + q < 180 strictly.
print('group 4: v1 != 0 on the region (closure impossible): VERIFIED')
