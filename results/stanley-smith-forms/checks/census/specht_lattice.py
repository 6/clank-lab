"""Independent SNF of Jucys-Murphy elements on the integral Specht lattice.

No standard-tableau basis, no straightening: the lattice S^lambda_Z is generated
inside the tabloid module M^lambda_Z as the Z[S_n]-span of one polytabloid, by
closing under the simple transpositions and taking Hermite normal forms (flint).
X_k is then expressed in the HNF basis and its Smith form computed twice
(flint and a pure-Python SNF).  Optionally the saturated lattice
(S^lambda_Q intersected with M^lambda_Z) is computed too.
"""
import itertools, sys, json
from math import gcd
import flint


def partitions(n, maxpart=None):
    if maxpart is None:
        maxpart = n
    if n == 0:
        yield ()
        return
    for p in range(min(n, maxpart), 0, -1):
        for rest in partitions(n - p, p):
            yield (p,) + rest


def tabloid_index(lam):
    """All tabloids as row-of tuples (row_of[v] for v in 0..n-1)."""
    n = sum(lam)
    rows = []
    def rec(prefix, counts):
        if len(prefix) == n:
            rows.append(tuple(prefix)); return
        for r, c in enumerate(counts):
            if c < lam[r]:
                counts[r] += 1; prefix.append(r)
                rec(prefix, counts)
                prefix.pop(); counts[r] -= 1
    rec([], [0] * len(lam))
    return {t: i for i, t in enumerate(rows)}


def perm_sign(p):
    s, seen = 1, [False] * len(p)
    for i in range(len(p)):
        if not seen[i]:
            j, L = i, 0
            while not seen[j]:
                seen[j] = True; j = p[j]; L += 1
            if L % 2 == 0:
                s = -s
    return s


def polytabloid(lam, T, idx):
    """T: list of rows (lists of entries 0..n-1). Returns dense int vector."""
    n = sum(lam)
    cols = [[T[i][j] for i in range(len(lam)) if lam[i] > j] for j in range(lam[0])]
    v = [0] * len(idx)
    for choice in itertools.product(*[list(itertools.permutations(range(len(c)))) for c in cols]):
        sgn = 1
        row_of = [None] * n
        for c, pc in zip(cols, choice):
            sgn *= perm_sign(list(pc))
            # sigma maps c[i] -> c[pc[i]]; entry at (i, j) of sigma T is sigma(c[i])
            for i in range(len(c)):
                row_of[c[pc[i]]] = i
        v[idx[tuple(row_of)]] += sgn
    return v


def act(perm, v, idx, keys):
    """perm: list, entry x -> perm[x]. Acts on tabloid: row_of'[perm[x]] = row_of[x]."""
    w = [0] * len(v)
    for i, c in enumerate(v):
        if c:
            t = keys[i]
            t2 = [None] * len(t)
            for x, r in enumerate(t):
                t2[perm[x]] = r
            w[idx[tuple(t2)]] += c
    return w


def transposition(n, a, b):
    p = list(range(n)); p[a], p[b] = b, a
    return p


def hnf_rows(rows):
    M = flint.fmpz_mat(rows).hnf()
    out = []
    for r in M.tolist():
        r = [int(x) for x in r]
        if any(r):
            out.append(r)
    return out


def specht_lattice(lam, idx, keys):
    n = sum(lam)
    T0, c = [], 0
    for l in lam:
        T0.append(list(range(c, c + l))); c += l
    B = hnf_rows([polytabloid(lam, T0, idx)])
    gens = [transposition(n, i, i + 1) for i in range(n - 1)]
    while True:
        new = list(B)
        for b in B:
            for g in gens:
                new.append(act(g, b, idx, keys))
        B2 = hnf_rows(new)
        if B2 == B:
            return B
        B = B2


def saturate(B):
    """Basis of (Q-span of B) intersect Z^N: via HNF of the kernel of the kernel."""
    M = flint.fmpz_mat(B)
    # nullspace of M (columns) gives rational kernel; integer lattice of
    # vectors orthogonal to ker = saturation.  Use flint nullspace over Q.
    K, r = M.nullspace()  # columns of K span ker(M) in Q^N
    Kt = [[int(K[i, j]) for i in range(K.nrows())] for j in range(r)]
    # saturation = {x in Z^N : K^T x = 0}; compute integer kernel by HNF of [Kt^T | I]
    N = M.ncols()
    if r == 0:
        return [[int(i == j) for j in range(N)] for i in range(N)]
    aug = [[Kt[j][i] for j in range(r)] + [int(i == jj) for jj in range(N)] for i in range(N)]
    H = flint.fmpz_mat(aug).hnf().tolist()
    sat = [[int(x) for x in row[r:]] for row in H if all(int(y) == 0 for y in row[:r]) and any(int(y) for y in row[r:])]
    return hnf_rows(sat)


def coords(B, w):
    """Exact integer coordinates of w in HNF basis B (pivot order)."""
    piv = [next(i for i, x in enumerate(b) if x) for b in B]
    r = list(w); c = []
    for b, p in zip(B, piv):
        q, rem = divmod(r[p], b[p])
        assert rem == 0, "not in lattice"
        c.append(q)
        if q:
            r = [x - q * y for x, y in zip(r, b)]
    assert not any(r), "not in span"
    return c


def jm_matrix(B, k, n, idx, keys):
    """Matrix (rows = images of basis vectors, in basis coordinates) of X_k, k 1-based."""
    rows = []
    for b in B:
        w = [0] * len(b)
        for i in range(k - 1):
            u = act(transposition(n, i, k - 1), b, idx, keys)
            w = [x + y for x, y in zip(w, u)]
        rows.append(coords(B, w))
    return rows


def snf_py(A):
    """Pure-Python SNF invariant factors (nonneg, divisibility chain, zeros last)."""
    A = [list(r) for r in A]
    m = len(A); nn = len(A[0]) if m else 0
    diag = []
    t = 0
    while t < min(m, nn):
        # find nonzero pivot with min abs value in submatrix
        best = None
        for i in range(t, m):
            for j in range(t, nn):
                if A[i][j] and (best is None or abs(A[i][j]) < abs(A[best[0]][best[1]])):
                    best = (i, j)
        if best is None:
            break
        i, j = best
        A[t], A[i] = A[i], A[t]
        for r in A:
            r[t], r[j] = r[j], r[t]
        done = False
        while not done:
            done = True
            p = A[t][t]
            for i in range(t + 1, m):
                q = A[i][t] // p
                if q:
                    A[i] = [x - q * y for x, y in zip(A[i], A[t])]
                if A[i][t]:
                    done = False
            for j in range(t + 1, nn):
                q = A[t][j] // p
                if q:
                    for r in A:
                        r[j] -= q * r[t]
                if A[t][j]:
                    done = False
            if not done:
                # move smallest nonzero in row/col t to pivot
                cand = [(abs(A[i][t]), i, t) for i in range(t, m) if A[i][t]] + \
                       [(abs(A[t][j]), t, j) for j in range(t, nn) if A[t][j]]
                _, i, j = min(cand)
                A[t], A[i] = A[i], A[t]
                for r in A:
                    r[t], r[j] = r[j], r[t]
                continue
            # divisibility: if some entry in submatrix not divisible by p, add its row
            bad = None
            for i in range(t + 1, m):
                for j in range(t + 1, nn):
                    if A[i][j] % p:
                        bad = i; break
                if bad is not None:
                    break
            if bad is not None:
                A[t] = [x + y for x, y in zip(A[t], A[bad])]
                done = False
        diag.append(abs(A[t][t]))
        t += 1
    diag += [0] * (min(m, nn) - len(diag))
    return diag


def snf_flint(A):
    S = flint.fmpz_mat(A).snf()
    return [abs(int(S[i, i])) for i in range(min(S.nrows(), S.ncols()))]


def normalize(d):
    nz = sorted(x for x in d if x)
    return nz + [0] * (len(d) - len(nz))


def syt(lam):
    n = sum(lam)
    out = []
    def rec(T, v):
        if v == n:
            out.append([list(r) for r in T]); return
        for i in range(len(lam)):
            if len(T[i]) < lam[i] and (i == 0 or len(T[i - 1]) > len(T[i])):
                T[i].append(v); rec(T, v + 1); T[i].pop()
    rec([[] for _ in lam], 0)
    return out


def predicted(lam, k):
    """Stanley Conj. 7.4 with 1-based positions and contents j - i."""
    from collections import Counter
    T = syt(lam)
    f = len(T)
    cnt = Counter()
    for t in T:
        for i, row in enumerate(t):
            for j, x in enumerate(row):
                if x == k - 1:
                    cnt[(i + 1, j + 1)] += 1
    alpha = [None] * f
    for r in range(1, f + 1):
        prod = 1
        for (i, j), c in cnt.items():
            if c >= r:
                prod *= (j - i)
        alpha[f - r] = abs(prod)
    return alpha, cnt


if __name__ == "__main__":
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    do_sat = "--sat" in sys.argv
    results = []
    for n in range(1, nmax + 1):
        for lam in partitions(n):
            idx = tabloid_index(lam)
            keys = {i: t for t, i in idx.items()}
            B = specht_lattice(lam, idx, keys)
            lattices = [("specht", B)]
            if do_sat:
                lattices.append(("saturated", saturate(B)))
            for name, L in lattices:
                for k in range(1, n + 1):
                    A = jm_matrix(L, k, n, idx, keys)
                    s1 = normalize(snf_flint(A)); s2 = normalize(snf_py(A))
                    assert s1 == s2, (lam, k, s1, s2)
                    pred, cnt = predicted(lam, k)
                    pred = normalize(pred)
                    rec = dict(n=n, lam=list(lam), k=k, lattice=name, f=len(L), snf=s1,
                               pred=pred, ok=(s1 == pred))
                    results.append(rec)
                    if not rec["ok"]:
                        print("MISMATCH", name, lam, k, "snf", s1, "pred", pred, flush=True)
        print("done n =", n, flush=True)
    json.dump(results, open(sys.argv[2] if len(sys.argv) > 2 and not sys.argv[2].startswith("--") else "/tmp/indep_results.json", "w"))
