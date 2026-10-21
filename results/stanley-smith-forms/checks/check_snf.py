"""Checker A: verify a Smith-form certificate for X_k on the integral Specht module.

Usage: python3 check_snf.py CERT.json      (exit 0 = accepted, nonzero = rejected)

From the definitions alone (standard library, imports no other project file):
  1. 'basis' is exactly the set of standard Young tableaux of shape lambda;
  2. the standard polytabloids are linearly independent and every polytabloid
     e_T (T over all n! fillings) is an integer combination of them, so they are
     a Z-basis of the integral Specht module S^lambda = Z-span of all e_T;
  3. A is the matrix of X_k = (1,k)+...+(k-1,k) in that basis (column j = X_k e_{T_j});
  4. U A V = diag(snf) with det U, det V = +-1 and snf a divisibility chain
     (zeros last), so snf is the Smith normal form of X_k on S^lambda;
  5. Stanley's Conjecture 7.4 list, recomputed here, differs from snf.

With "weak_form": true the certificate also claims that Stanley's weaker remark
fails (every Smith entry is a product of eigenvalues of X_k).  Then, in addition:
  6. the eigenvalues are the contents j - i of the cells holding k in the SYT,
     one per tableau: prod over the distinct contents c of (A - cI) is 0, and
     trace(A^j) equals the j-th power sum of these contents for j < number of
     distinct contents, which fixes every multiplicity;
  7. some entry of snf is not |product| of a sub-multiset of these eigenvalues
     (the empty product is 1).
"""
import itertools, json, sys
from fractions import Fraction


def fail(msg):
    print("REJECT:", msg); sys.exit(1)


def cells(lam):
    return [(i, j) for i, l in enumerate(lam) for j in range(l)]


def standard_tableaux(lam):
    n = sum(lam); cs = cells(lam); out = []
    for perm in itertools.permutations(range(1, n + 1)):
        F = dict(zip(cs, perm))
        if all(F[(i, j)] < F[(i, j + 1)] for (i, j) in cs if (i, j + 1) in F) and \
           all(F[(i, j)] < F[(i + 1, j)] for (i, j) in cs if (i + 1, j) in F):
            out.append([[F[(i, j)] for j in range(lam[i])] for i in range(len(lam))])
    return out


def poly(lam, F):
    """Polytabloid of the filling F (dict cell -> entry) as dict tabloid -> coefficient.
    A tabloid is the tuple of row sets."""
    cols = [[(i, j) for i in range(len(lam)) if lam[i] > j] for j in range(lam[0])]
    res = {}
    for choice in itertools.product(*[list(itertools.permutations(c)) for c in cols]):
        # choice[c] is a rearrangement of the cells of column c: entry of cell col[c][r] moves to choice[c][r]
        G = {}; sgn = 1
        for col, new in zip(cols, choice):
            idx = [col.index(x) for x in new]
            inv = sum(1 for a in range(len(idx)) for b in range(a + 1, len(idx)) if idx[a] > idx[b])
            sgn *= -1 if inv % 2 else 1
            for old, nw in zip(col, new):
                G[nw] = F[old]
        t = tuple(frozenset(G[(i, j)] for j in range(lam[i])) for i in range(len(lam)))
        res[t] = res.get(t, 0) + sgn
    return {t: c for t, c in res.items() if c}


def apply_X(k, v):
    out = {}
    for a in range(1, k):
        for t, c in v.items():
            t2 = tuple(frozenset(k if x == a else a if x == k else x for x in r) for r in t)
            out[t2] = out.get(t2, 0) + c
    return {t: c for t, c in out.items() if c}


def det(M):
    M = [[Fraction(x) for x in r] for r in M]; n = len(M); d = Fraction(1)
    for c in range(n):
        p = next((i for i in range(c, n) if M[i][c] != 0), None)
        if p is None: return 0
        if p != c: M[c], M[p] = M[p], M[c]; d = -d
        d *= M[c][c]
        for i in range(c + 1, n):
            q = M[i][c] / M[c][c]
            if q: M[i] = [x - q * y for x, y in zip(M[i], M[c])]
    return d


def matmul(X, Y):
    return [[sum(X[i][t] * Y[t][j] for t in range(len(Y))) for j in range(len(Y[0]))] for i in range(len(X))]


def main(path):
    C = json.load(open(path))
    n, lam, k = C["n"], C["lambda"], C["k"]
    if sum(lam) != n or any(lam[i] < lam[i + 1] for i in range(len(lam) - 1)) or min(lam) < 1: fail("bad partition")
    if not 1 <= k <= n: fail("bad k")
    B = C["basis"]; S = standard_tableaux(lam)
    if sorted(map(json.dumps, B)) != sorted(map(json.dumps, S)) or len(B) != len(S): fail("basis is not the set of SYT")
    f = len(B)
    E = [poly(lam, {(i, j): T[i][j] for (i, j) in cells(lam)}) for T in B]
    tabs = sorted({t for e in E for t in e}, key=lambda t: [sorted(r) for r in t])
    # choose f tabloid coordinates on which the standard polytabloids are invertible
    Mfull = [[e.get(t, 0) for e in E] for t in tabs]
    rows, R = [], []
    for ti, row in enumerate(Mfull):
        cand = R + [row]
        if abs(rank_q(cand)) > len(R):
            R.append(row); rows.append(ti)
        if len(R) == f: break
    if len(R) != f: fail("standard polytabloids are linearly dependent")
    Rinv = inverse(R)
    def coords(v):
        x = [sum(Rinv[i][j] * v.get(tabs[rows[j]], 0) for j in range(f)) for i in range(f)]
        if any(c.denominator != 1 for c in x): return None
        x = [int(c) for c in x]
        rec = {}
        for c, e in zip(x, E):
            for t, a in e.items(): rec[t] = rec.get(t, 0) + c * a
        rec = {t: a for t, a in rec.items() if a}
        return x if rec == v else None
    # every polytabloid lies in the Z-span of the standard ones
    cs = cells(lam)
    for perm in itertools.permutations(range(1, n + 1)):
        if coords(poly(lam, dict(zip(cs, perm)))) is None: fail("a polytabloid is not an integral combination of standard ones")
    # A is the matrix of X_k
    A = C["A"]
    if len(A) != f or any(len(r) != f for r in A): fail("A has wrong size")
    weak = C.get("weak_form", False)
    if type(weak) is not bool: fail("weak_form must be true or false")
    if weak:
        if any(type(x) is not int for r in A for x in r): fail("A is not an f x f integer matrix")
        eig = [j - i for T in S for i, row in enumerate(T) for j, x in enumerate(row) if x == k]
        distinct = sorted(set(eig))
        I = [[int(i == j) for j in range(f)] for i in range(f)]
        P = I
        for c in distinct:
            P = matmul(P, [[A[i][j] - c * I[i][j] for j in range(f)] for i in range(f)])
        if any(x for r in P for x in r): fail("weak form: prod (A - cI) over the contents c is not 0")
        P = I
        for j in range(1, len(distinct)):
            P = matmul(P, A)
            if sum(P[i][i] for i in range(f)) != sum(c ** j for c in eig):
                fail(f"weak form: trace of A^{j} differs from the power sum of the contents")
    for j, e in enumerate(E):
        x = coords(apply_X(k, e))
        if x is None or x != [A[i][j] for i in range(f)]: fail(f"column {j} of A is not X_k e_T")
    U, V, snf = C["U"], C["V"], C["snf"]
    isint = lambda x: type(x) is int
    for name, M in (("A", A), ("U", U), ("V", V)):
        if not isinstance(M, list) or len(M) != f or any(not isinstance(r, list) or len(r) != f or not all(map(isint, r)) for r in M):
            fail(f"{name} is not an f x f integer matrix")
    if not isinstance(snf, list) or len(snf) != f or not all(map(isint, snf)): fail("snf is not a list of f integers")
    D = [[snf[i] if i == j else 0 for j in range(f)] for i in range(f)]
    if matmul(matmul(U, A), V) != D: fail("U A V != diag(snf)")
    if abs(det(U)) != 1 or abs(det(V)) != 1: fail("U or V not unimodular")
    nz = [x for x in snf if x != 0]
    if any(x < 0 for x in snf) or snf != nz + [0] * (f - len(nz)) or any(nz[i + 1] % nz[i] for i in range(len(nz) - 1)):
        fail("snf is not a nonnegative divisibility chain with zeros last")
    # Stanley's prediction
    cnt = {}
    for T in S:
        for i, row in enumerate(T):
            for j, x in enumerate(row):
                if x == k: cnt[(i + 1, j + 1)] = cnt.get((i + 1, j + 1), 0) + 1
    pred = [0] * f
    for r in range(1, f + 1):
        p = 1
        for (i, j), c in cnt.items():
            if c >= r: p *= (j - i)
        pred[f - r] = abs(p)
    if pred != C["predicted"]: fail("recorded prediction differs from the recomputed one")
    if weak:
        products = {1}
        for c in eig:
            products |= {p * abs(c) for p in products}
        if all(x in products for x in snf):
            fail("weak form holds: every snf entry is a product of eigenvalues")
    if pred == snf: fail("no discrepancy: snf equals the prediction")
    odd = sum(1 for x in snf if x % 2); podd = sum(1 for x in pred if x % 2)
    print(f"ACCEPT lambda={lam} n={n} k={k} f={f}: SNF {snf}; Conjecture 7.4 predicts {pred}; "
          f"rank mod 2 {odd} vs predicted {podd}"
          + (f"; eigenvalues {sorted(eig)}, SNF entries not products of them: "
             f"{sorted(set(x for x in snf if x not in products))}" if weak else ""))


def rank_q(M):
    M = [[Fraction(x) for x in r] for r in M]; r = 0
    for c in range(len(M[0])):
        p = next((i for i in range(r, len(M)) if M[i][c] != 0), None)
        if p is None: continue
        M[r], M[p] = M[p], M[r]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                q = M[i][c] / M[r][c]; M[i] = [x - q * y for x, y in zip(M[i], M[r])]
        r += 1
    return r


def inverse(M):
    n = len(M); A = [[Fraction(x) for x in r] + [Fraction(int(i == j)) for j in range(n)] for i, r in enumerate(M)]
    for c in range(n):
        p = next(i for i in range(c, n) if A[i][c] != 0)
        A[c], A[p] = A[p], A[c]
        A[c] = [x / A[c][c] for x in A[c]]
        for i in range(n):
            if i != c and A[i][c] != 0:
                q = A[i][c]; A[i] = [x - q * y for x, y in zip(A[i], A[c])]
    return [r[n:] for r in A]


if __name__ == "__main__":
    try:
        main(sys.argv[1])
    except SystemExit:
        raise
    except Exception as exc:  # malformed certificate
        fail(f"malformed certificate: {exc!r}")
