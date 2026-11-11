"""Check a certificate that mu(G) >= 6 (Colin de Verdiere invariant).

Certificate (JSON): graph6 of G on vertices 0..n-1; a split S + T with |S| = 6;
the T x T block C as exact rationals; exact rationals for all S-T entries of B
except q "unknown" positions; a box u_mid +- r for the unknowns.  The matrix is
M = [[A, B], [B^T, C]] with A = B C^{-1} B^T (so the Schur complement is zero).

What is checked, from the certificate alone:
 1. pattern: C_ab < 0 on edges, 0 on non-edges (a != b in T); every S-T edge is a
    fixed entry (< 0) or an unknown; S-T non-edges carry nothing (entry 0);
 2. Krawczyk: the q equations f_ij(u) = b_i C^{-1} b_j^T = 0, one for each
    non-adjacent pair i < j in S (recomputed from G here), have a unique zero
    u* in the box (interval arithmetic, mpmath iv, 300 bits);
 3. over the box: every unknown < 0, and A_ij < 0 for every edge ij inside S;
    so M* (at u*) has the Colin de Verdiere sign pattern of G;
 4. inertia of C, exactly from its characteristic polynomial (Descartes'
    rule; all roots real): one negative, no zero, n-7 positive eigenvalues.
    Hence rank M* = rank C = n-6 and M* has exactly one negative eigenvalue,
    so corank M* = 6;
 5. Strong Arnold Property for M*: at a rational point M0 of the box the
    exact Gram matrix of X -> M0 X (X symmetric, supported on the non-edges)
    minus eps*I is positive definite (exact characteristic polynomial), so
    sigma_min(X -> M0 X) > sqrt(eps) on that basis; since ||D X||_F <=
    ||D||_F ||X||_F = sqrt(2) ||D||_F |x|, SAP holds at M* once
    ||M* - M0||_F, bounded from the box, is below sqrt(eps)/2.
Exit 0 and print PASS only if every check holds.
Usage: check_cert.py CERT.json
"""
import itertools, json, sys
from fractions import Fraction as Fr
import flint
import mpmath
from mpmath import mp, iv

mp.prec = 300
iv.prec = 300

def graph6_edges(s):
    data = [ord(c) - 63 for c in s]
    n = data[0]; bits = []
    for d in data[1:]:
        bits.extend((d >> (5 - k)) & 1 for k in range(6))
    E = set(); k = 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]: E.add((i, j))
            k += 1
    return n, E

def fq(x): return flint.fmpq(x.numerator, x.denominator)

def inertia(rows):
    p = flint.fmpq_mat([[fq(x) for x in r] for r in rows]).charpoly()
    c = [p[k] for k in range(p.degree() + 1)]
    zeros = 0
    while c and c[0] == 0:
        zeros += 1; c = c[1:]
    def changes(seq):
        s = [x for x in seq if x != 0]
        return sum(1 for a, b in zip(s, s[1:]) if (a > 0) != (b > 0))
    pos = changes(c[::-1])
    neg = changes([x * (-1) ** k for k, x in enumerate(c)][::-1])
    return neg, zeros, pos

def sap_eps(M0, NE):
    """Largest eps in 1e-6, 1e-8, ..., 1e-30 with Gram(L) - eps*I positive definite,
    L: x -> M0 X(x), X = sum x_ij (E_ij + E_ji) over the pairs NE; None if none."""
    n = len(M0)
    cols = []
    for (i, j) in NE:     # M0 X for X = E_ij + E_ji, flattened
        col = [Fr(0)] * (n * n)
        for k in range(n):
            col[k * n + j] += M0[k][i]; col[k * n + i] += M0[k][j]
        cols.append(col)
    L = flint.fmpq_mat([[fq(cols[c][k]) for c in range(len(cols))] for k in range(n * n)])
    Gram = L.transpose() * L
    gm = [[Fr(int(Gram[a, b].p), int(Gram[a, b].q)) for b in range(Gram.ncols())] for a in range(Gram.nrows())]
    eps = Fr(1, 10 ** 6)
    while eps >= Fr(1, 10 ** 30):
        sh = [[gm[a][b] - (eps if a == b else 0) for b in range(len(gm))] for a in range(len(gm))]
        ng, zr, _ = inertia(sh)
        if ng == 0 and zr == 0: return eps
        eps /= 100
    return None

def fail(msg):
    print("FAIL:", msg); sys.exit(1)

def main(path):
    cert = json.load(open(path))
    n, E = graph6_edges(cert["graph6"])
    adj = lambda a, b: (min(a, b), max(a, b)) in E
    S, T = cert["S"], cert["T"]
    if sorted(S + T) != list(range(n)) or len(S) != 6: fail("bad split")
    r = len(T); ti = {t: k for k, t in enumerate(T)}
    C = [[Fr(x) for x in row] for row in cert["C_rows_T_order"]]
    for a in range(r):
        for b in range(r):
            if C[a][b] != C[b][a]: fail("C not symmetric")
            if a != b:
                if adj(T[a], T[b]) and not C[a][b] < 0: fail("C edge entry not negative")
                if not adj(T[a], T[b]) and C[a][b] != 0: fail("C non-edge entry nonzero")
    fixed = {}
    for key, v in cert["B_fixed"].items():
        i, t = map(int, key.split(","))
        fixed[(i, t)] = Fr(v)
    unk = [tuple(p) for p in cert["unknowns"]]
    st_edges = {(i, t) for i in S for t in T if adj(i, t)}
    if set(fixed) | set(unk) != st_edges or set(fixed) & set(unk): fail("B positions do not match the S-T edges")
    if any(v >= 0 for v in fixed.values()): fail("fixed B entry not negative")
    pairs = [(i, j) for i, j in itertools.combinations(S, 2) if not adj(i, j)]
    q = len(pairs)
    if len(unk) != q: fail("number of unknowns differs from number of equations")
    neg, zer, pos = inertia(C)
    if (neg, zer, pos) != (1, 0, r - 1): fail("inertia of C is %s" % ((neg, zer, pos),))
    Cinv = flint.fmpq_mat([[fq(x) for x in row] for row in C]).inv()
    Ci = [[Fr(int(Cinv[a, b].p), int(Cinv[a, b].q)) for b in range(r)] for a in range(r)]
    rad = mp.mpf(cert["box_radius"])
    umid = [mp.mpf(x) for x in cert["u_mid"]]
    X = [iv.mpf([x - rad, x + rad]) for x in umid]

    def rows_of(u):
        rows = {i: [iv.mpf(0)] * r for i in S}
        for (i, t), v in fixed.items():
            rows[i][ti[t]] = iv.mpf(v.numerator) / v.denominator
        for (i, t), v in zip(unk, u):
            rows[i][ti[t]] = v
        return rows
    CiI = [[iv.mpf(x.numerator) / x.denominator for x in row] for row in Ci]
    def Cvec(row):
        return [iv.fsum(CiI[a][b] * row[b] for b in range(r)) for a in range(r)]
    def F(u):
        rows = rows_of(u); cv = {i: Cvec(rows[i]) for i in S}
        f = [iv.fsum(rows[a][x] * cv[b][x] for x in range(r)) for a, b in pairs]
        J = []
        for a, b in pairs:
            J.append([(cv[b][ti[t]] if k == a else iv.mpf(0)) + (cv[a][ti[t]] if k == b else iv.mpf(0)) for (k, t) in unk])
        return f, J, rows, cv
    # Krawczyk operator K(X) = y - Y f(y) + (I - Y J(X)) (X - y), valid for any real Y.
    # y is the 300-bit rounding of u_mid (a point of X); f(y) and J(X) are evaluated in
    # interval arithmetic, with C^{-1} and the fixed B entries enclosed from exact rationals.
    y = [iv.mpf(x) for x in umid]
    fy, Jy, _, _ = F(y)
    Ymat = mp.inverse(mp.matrix([[mp.mpf(e.mid) for e in row] for row in Jy]))
    _, JX, rowsX, cvX = F(X)
    for a in range(q):
        k = y[a] - iv.fsum(iv.mpf(Ymat[a, b]) * fy[b] for b in range(q))
        for b in range(q):
            coeff = (1 if a == b else 0) - iv.fsum(iv.mpf(Ymat[a, c]) * JX[c][b] for c in range(q))
            k += coeff * (X[b] - y[b])
        if not (k.a > X[a].a and k.b < X[a].b): fail("Krawczyk inclusion fails for unknown %d" % a)
    if not all(x.b < 0 for x in X): fail("unknown entry not negative over the box")
    A = {}
    for a, b in itertools.combinations_with_replacement(S, 2):
        A[(a, b)] = iv.fsum(rowsX[a][x] * cvX[b][x] for x in range(r))
    for a, b in itertools.combinations(S, 2):
        if adj(a, b) and not A[(a, b)].b < 0: fail("A edge entry not negative over the box")
    # SAP at the rational box midpoint M0, then a perturbation bound
    Bmid = dict(fixed)
    for p, x in zip(unk, cert["u_mid"]): Bmid[p] = Fr(x)
    Bm = flint.fmpq_mat([[fq(Bmid.get((i, t), Fr(0))) for t in T] for i in S])
    Am = Bm * Cinv * Bm.transpose()
    M0 = [[Fr(0)] * n for _ in range(n)]
    for a, i in enumerate(S):
        for b, j in enumerate(S): M0[i][j] = Fr(int(Am[a, b].p), int(Am[a, b].q))
        for t in T: M0[i][t] = M0[t][i] = Bmid.get((i, t), Fr(0))
    for a in range(r):
        for b in range(r): M0[T[a]][T[b]] = C[a][b]
    NE = [(i, j) for i, j in itertools.combinations(range(n), 2) if not adj(i, j)]
    eps = sap_eps(M0, NE)
    if eps is None: fail("SAP: Gram matrix not shown positive definite")
    # ||M* - M0||_F: M0 uses the exact decimal u_mid, within 1e-85 of the binary centre of X,
    # so it lies in X and each unknown moves by at most 2r (twice each, symmetric); A at u*
    # and at u_mid both lie in the interval A over X, so A entries move within its widths.
    def width(z): return (mp.mpf(z.b) - mp.mpf(z.a)) * (1 + mp.mpf(10) ** -30) + mp.mpf(10) ** -250
    pert2 = mp.mpf(0)
    for x in X: pert2 += 2 * (2 * rad) ** 2
    for (a, b), z in A.items(): pert2 += (2 if a != b else 1) * width(z) ** 2
    pert = mp.sqrt(pert2) * (1 + mp.mpf(10) ** -20)
    # sigma_min(L(M*)) >= sigma_min(L(M0)) - ||M* - M0||_2 * ||X -> X||, with ||(M*-M0)X||_F <= ||M*-M0||_F ||X||_F
    # and ||X||_F = sqrt(2) |x| for the basis normalisation used; require a wide margin.
    if not pert * 2 < mp.sqrt(mp.mpf(eps.numerator) / eps.denominator): fail("SAP perturbation bound too large")
    print("PASS %s: n=%d, |E|=%d, q=%d equations, Krawczyk inclusion, signs, inertia(C)=%s, SAP eps=%s, perturbation<=%s"
          % (cert.get("name", path), n, len(E), q, (neg, zer, pos), eps, mpmath.nstr(pert, 3)))

if __name__ == "__main__":
    main(sys.argv[1])
