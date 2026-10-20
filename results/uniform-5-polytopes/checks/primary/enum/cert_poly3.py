"""Rigorous data of uniform polyhedra from their vertex configurations (arb balls).

For vertex configuration (q_1..q_k) with unit edges, the neighbours of a
vertex v lie on a circle of radius rho in a plane at height h below v,
h^2 + rho^2 = 1, with consecutive chords 2 cos(pi/q_i); rho solves
sum_i 2 asin(cos(pi/q_i)/rho) = 2 pi.  From the resulting coordinates:
circumradius R = 1/(2 h) and the dihedral angle at each edge v-x_i between
faces (v, x_{i-1}, x_i) and (v, x_i, x_{i+1}).  No construction of the
whole polyhedron is used.
"""
from flint import arb, ctx
ctx.prec = 200
PI = arb.pi()

def chord(q):
    return 2 * (PI / q).cos()

def solve_rho(conf):
    """Certified root of F(rho) = sum 2 asin(c_i / rho) - 2 pi on (max c_i, 1) (F decreasing)."""
    cs = [chord(q) / 2 for q in conf]
    lo = max((c.upper() for c in cs))
    lo = arb(lo) + arb(1) * 1e-30
    hi = arb(1)

    def F(r):
        return sum((2 * (c / r).asin() for c in cs)) - 2 * PI
    a, b = (lo.mid(), hi.mid())
    fa, fb = (F(arb(a)), F(arb(b)))
    if not (fa > 0 and fb < 0):
        raise AssertionError((conf, fa, fb))
    for _ in range(400):
        m = (a + b) / 2
        fm = F(arb(m))
        if fm > 0:
            a = m
        elif fm < 0:
            b = m
        else:
            break
        if b - a < arb(2) ** (-180):
            break
    return arb(a).union(arb(b))

def data(conf):
    rho = solve_rho(conf)
    h = (1 - rho * rho).sqrt()
    R = 1 / (2 * h)
    angs, t = ([], arb(0))
    for q in conf:
        angs.append(t)
        t = t + 2 * (chord(q) / 2 / rho).asin()
    X = [(rho * a.cos(), rho * a.sin(), arb(0)) for a in angs]
    v = (arb(0), arb(0), h)

    def sub(a, b):
        return tuple((x - y for x, y in zip(a, b)))

    def cross(a, b):
        return (a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0])

    def dot(a, b):
        return sum((x * y for x, y in zip(a, b)))
    k = len(conf)
    edges = []
    for i in range(k):
        e = sub(X[i], v)
        a = sub(X[i - 1], v)
        b = sub(X[(i + 1) % k], v)
        ee = dot(e, e)
        ap = tuple((x - dot(a, e) / ee * y for x, y in zip(a, e)))
        bp = tuple((x - dot(b, e) / ee * y for x, y in zip(b, e)))
        cosang = dot(ap, bp) / (dot(ap, ap) * dot(bp, bp)).sqrt()
        edges.append((conf[i - 1], conf[i], cosang.acos()))
    return dict(R=R, rho=rho, edges=edges)
if __name__ == '__main__':
    for conf in ([3, 3, 3], [4, 4, 4], [3, 4, 3, 4], [3, 3, 3, 3, 4], [4, 6, 8], [3, 3, 3, 3, 5]):
        d = data(conf)
        print(conf, d['R'].str(15), [(a, b, al.str(12)) for a, b, al in d['edges']])
