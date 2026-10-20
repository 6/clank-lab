"""Interval linear algebra on mpmath.iv (independent of the producer's arb).

All vectors are Python lists of iv.mpf, matrices lists of rows.  Every
decision taken from an interval is either certified (the interval excludes
the alternative) or reported as undecided by the caller.
"""
from mpmath import iv, mp

PREC = 160
iv.prec = PREC
mp.prec = PREC

ZERO = iv.mpf(0)
ONE = iv.mpf(1)
HALF = iv.mpf(1) / 2


def setprec(bits):
    global PREC
    PREC = bits
    iv.prec = bits
    mp.prec = bits


def I(x):
    """Interval from a number or a pair of decimal strings."""
    if isinstance(x, (list, tuple)):
        return iv.mpf([x[0], x[1]])
    return iv.mpf(x)


def mid(x):
    return float(x.mid)


def lo(x):
    return x.a


def hi(x):
    return x.b


def pos(x):
    """certified > 0"""
    return x.a > 0


def neg(x):
    return x.b < 0


def width(x):
    return float(x.delta)


def hull(a, b):
    return iv.mpf([min(a.a, b.a), max(a.b, b.b)])


# ---------------------------------------------------------------- vectors
def vadd(u, v):
    return [a + b for a, b in zip(u, v)]


def vsub(u, v):
    return [a - b for a, b in zip(u, v)]


def vscale(c, u):
    return [c * a for a in u]


def dot(u, v):
    s = ZERO
    for a, b in zip(u, v):
        s += a * b
    return s


def norm2(u):
    s = ZERO
    for a in u:
        s += a * a
    return s


def dist2(u, v):
    s = ZERO
    for a, b in zip(u, v):
        d = a - b
        s += d * d
    return s


def vmid(u):
    return [float(a.mid) for a in u]


def vwidth(u):
    return max(float(a.delta) for a in u)


# ---------------------------------------------------------------- matrices
def matvec(M, u):
    return [dot(row, u) for row in M]


def transpose(M):
    return [list(r) for r in zip(*M)]


def matmul(A, B):
    Bt = transpose(B)
    return [[dot(r, c) for c in Bt] for r in A]


def ident(n):
    return [[ONE if i == j else ZERO for j in range(n)] for i in range(n)]


def solve(A, B):
    """Solve A X = B (A square, B a matrix) by Gaussian elimination with
    pivoting on the largest midpoint.  Raises if a pivot contains 0."""
    n = len(A)
    M = [list(A[i]) + list(B[i]) for i in range(n)]
    m = len(M[0])
    for c in range(n):
        p = max(range(c, n), key=lambda r: abs(float(M[r][c].mid)))
        piv = M[p][c]
        if piv.a <= 0 <= piv.b:
            raise ZeroDivisionError("pivot contains zero")
        M[c], M[p] = M[p], M[c]
        inv = ONE / M[c][c]
        M[c] = [x * inv for x in M[c]]
        for r in range(n):
            if r != c:
                f = M[r][c]
                if f.a == 0 and f.b == 0:
                    continue
                M[r] = [x - f * y for x, y in zip(M[r], M[c])]
    return [row[n:] for row in M]


def inverse(A):
    return solve(A, ident(len(A)))


def cholesky(G):
    n = len(G)
    L = [[ZERO] * n for _ in range(n)]
    for i in range(n):
        for j in range(i + 1):
            s = G[i][j]
            for k in range(j):
                s -= L[i][k] * L[j][k]
            if i == j:
                if not s.a > 0:
                    raise ValueError("not positive definite")
                L[i][i] = iv.sqrt(s)
            else:
                L[i][j] = s / L[j][j]
    return L


def orth_complement_vector(rows):
    """A unit vector orthogonal to the given n-1 vectors in R^n
    (generalised cross product via cofactors), as intervals."""
    n = len(rows) + 1
    v = []
    for i in range(n):
        minor = [[r[j] for j in range(n) if j != i] for r in rows]
        v.append((-1) ** i * det(minor))
    nv = iv.sqrt(norm2(v))
    return [x / nv for x in v]


def det(M):
    n = len(M)
    if n == 0:
        return ONE
    if n == 1:
        return M[0][0]
    if n == 2:
        return M[0][0] * M[1][1] - M[0][1] * M[1][0]
    A = [list(r) for r in M]
    d = ONE
    for c in range(n):
        p = max(range(c, n), key=lambda r: abs(float(A[r][c].mid)))
        if A[p][c].a <= 0 <= A[p][c].b and abs(float(A[p][c].mid)) < 1e-30:
            # singular up to rounding: fall back to cofactor expansion
            return _det_cof(M)
        if p != c:
            A[c], A[p] = A[p], A[c]
            d = -d
        d *= A[c][c]
        for r in range(c + 1, n):
            f = A[r][c] / A[c][c]
            A[r] = [x - f * y for x, y in zip(A[r], A[c])]
    return d


def _det_cof(M):
    n = len(M)
    if n == 1:
        return M[0][0]
    s = ZERO
    for j in range(n):
        minor = [r[:j] + r[j + 1:] for r in M[1:]]
        s += (-1) ** j * M[0][j] * _det_cof(minor)
    return s


def gram_schmidt(vecs):
    """Orthonormalise (intervals); returns list of unit vectors."""
    out = []
    for v in vecs:
        w = list(v)
        for u in out:
            c = dot(w, u)
            w = vsub(w, vscale(c, u))
        nw = iv.sqrt(norm2(w))
        out.append([x / nw for x in w])
    return out


def iacos(x):
    """Enclose acos(x) by certified cosine brackets and monotonicity.

    Ordinary mp.acos only proposes endpoints. Each non-boundary endpoint
    is accepted by an outward-rounded iv.cos inequality on [0, pi].
    See ACOS_REPAIR.md for the proof and deliberate corruption controls.
    """
    if not (x.a >= -1 and x.b <= 1):
        raise ValueError("acos argument outside [-1, 1]")
    lower = _acos_endpoint(x.b, lower=True)
    upper = _acos_endpoint(x.a, lower=False)
    return iv.mpf([lower.a, upper.b])


def _acos_endpoint(x, lower):
    """One bound for acos at the exact binary endpoint x (a point interval).

    A failed proposal is widened; exhaustion returns the safe domain bound.
    Neither proposal accuracy nor the number of guard bits is a premise.
    """
    if x == 1:
        return ZERO
    if x == -1:
        return iv.pi.a if lower else iv.pi.b
    with mp.workprec(iv.prec + 30):
        proposal = mp.acos(mp.mpf(x))
        eps = mp.ldexp(1, 4 - iv.prec)
        # Near +/-1, cos(t) may require a much wider angle bracket before
        # its interval can separate x. Uncertified proposals never escape.
        for _ in range(max(16, iv.prec // 8 + 16)):
            t = iv.mpf(proposal - eps if lower else proposal + eps)
            if lower:
                if t.b <= 0:
                    return ZERO
                if t.a >= 0 and t.b <= iv.pi.a and iv.cos(t).a >= x:
                    return t.a
            else:
                if t.a >= iv.pi.a:
                    return iv.pi.b
                if t.a >= 0 and t.b <= iv.pi.a and iv.cos(t).b <= x:
                    return t.b
            eps *= 16
    return ZERO if lower else iv.pi.b
