"""First anticyclotomic layer via exact proper binary quadratic forms."""
from math import gcd
from sage.all import BinaryQF, pari, ZZ


def project(D, p, a, forms):
    """Return logs of the ray action a+omega and prime-to-p ideal lifts.

    forms is a full set of proper class representatives (A,B,C) of D,
    representing the ideals <A,(-B+sqrt(D))/2>. omega=(tr+sqrt(D))/2
    with tr = D mod 2. The caller checks a+omega generates the projective
    nonsplit Cartan at p². Its order there implies generation at every
    higher depth by the binomial theorem (p odd).
    """
    forms = [BinaryQF(list(v)) for v in forms]
    h = len(forms)
    if (h != ZZ(D).class_number(proof=True) or
            len({tuple(v.reduced_form()) for v in forms}) != h):
        raise ValueError("incomplete ordinary class group")
    d = 2 + int(ZZ(h).valuation(p))
    f = p**d
    tr = D % 2
    norm = a*a + a*tr + (tr*tr-D)//4
    gen = BinaryQF([norm, f*(2*a+tr), f*f])
    lifts = []
    for v in forms:
        A,B,C = v
        if v.discriminant() != D or gcd(A,p) != 1 or A <= 0:
            raise ValueError("improper or non-coprime class representative")
        lifts.append(BinaryQF([A,f*B,f*f*C]))
    order = h*(p+1)*p**(d-1)
    prime_to_p = order // p**int(ZZ(order).valuation(p))
    identity = tuple(BinaryQF([1,f*tr,(f*f*(tr*tr-D))//4]).reduced_form())

    def power(v, n):
        return tuple(BinaryQF(pari(v).qfbpow(int(n))).reduced_form())

    # These classes generate: the local generator spans the kernel over
    # Pic(O_K), and the h lifts cover its quotient. Find the p-exponent.
    basis = [gen,*lifts]
    exponent = prime_to_p
    while any(power(v, exponent) != identity for v in basis):
        exponent *= p
        if order % exponent:
            raise ArithmeticError("form order contradicts class number")
    top = [power(v,exponent//p) for v in basis]
    pivot = next((t for t in top if t != identity), None)
    if pivot is None:
        raise ArithmeticError("missing degree-p layer")
    logs = {power(BinaryQF(list(pivot)),j):j for j in range(p)}
    if len(logs) != p or any(t not in logs for t in top):
        raise ArithmeticError("largest p-invariant factor is ambiguous")
    return logs[top[0]], [logs[t] for t in top[1:]]
