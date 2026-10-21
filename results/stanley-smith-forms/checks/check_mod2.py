"""Checker B (written separately from checker A and the generator).

Usage: python3 check_mod2.py CERT.json      (exit 0 = accepted, nonzero = rejected)

Basis-free part: the F2-span W of all polytabloids inside the F2 tabloid module
has dimension f^lambda, so the integral Specht lattice L injects mod 2
(L/2L ~= W), and rank_F2(X_k on W) equals the number of odd Smith invariant
factors of X_k on L.  That rank is compared with the number of odd entries of
Stanley's Conjecture 7.4 list, recomputed here from Yamanouchi words.

Certificate part: the recorded basis is the set of standard tableaux, the
recorded A satisfies X_k e_{T_j} = sum_i A[i][j] e_{T_i} exactly over Z, and
U A V = diag(snf) with U, V of determinant +-1 (Bareiss) and snf a divisibility
chain whose number of odd entries matches the basis-free rank.

Weak form (only when the certificate has "weak_form": true): the eigenvalues of
X_k are read off the Yamanouchi words as the content (column - row) of k in each
SYT.  Applying the factors (A - c) for the distinct contents c in turn to every
unit vector gives 0, so every eigenvalue of A is a content; the traces of
A^1, ..., A^(d-1) (d distinct contents) match the power sums of the contents,
which fixes the multiplicities.  Then some snf entry must differ from the absolute
value of every product c^e over exponent vectors 0 <= e_c <= multiplicity of c.
"""
import itertools, json, sys


def bad(msg):
    print("REJECT:", msg); sys.exit(2)


def yamanouchi_syt(lam):
    """All SYT via lattice words: w[v] = row of entry v+1."""
    n = sum(lam); out = []
    def rec(word, filled):
        if len(word) == n:
            T = [[] for _ in lam]
            for v, r in enumerate(word): T[r].append(v + 1)
            out.append(T); return
        for r in range(len(lam)):
            if filled[r] < lam[r] and (r == 0 or filled[r - 1] > filled[r]):
                filled[r] += 1; word.append(r); rec(word, filled); word.pop(); filled[r] -= 1
    rec([], [0] * len(lam))
    return out


def tabloid_of_rows(rowlists, n):
    """Encode a tabloid as tuple: entry -> row."""
    rowof = [0] * (n + 1)
    for r, xs in enumerate(rowlists):
        for x in xs: rowof[x] = r
    return tuple(rowof[1:])


def column_rearrangements(T):
    lam = [len(r) for r in T]
    cols = [[T[i][j] for i in range(len(T)) if lam[i] > j] for j in range(lam[0])]
    for choice in itertools.product(*[list(itertools.permutations(c)) for c in cols]):
        sgn = 1
        for c, p in zip(cols, choice):
            pos = [c.index(x) for x in p]
            for a in range(len(pos)):
                for b in range(a + 1, len(pos)):
                    if pos[a] > pos[b]: sgn = -sgn
        rows = [[] for _ in T]
        for p in choice:
            for i, x in enumerate(p): rows[i].append(x)
        yield sgn, rows


def e_int(T, n):
    v = {}
    for s, rows in column_rearrangements(T):
        t = tabloid_of_rows(rows, n); v[t] = v.get(t, 0) + s
    return {t: c for t, c in v.items() if c}


def swap_tabloid(t, a, b):
    t = list(t); t[a - 1], t[b - 1] = t[b - 1], t[a - 1]; return tuple(t)


def X(k, v):
    out = {}
    for a in range(1, k):
        for t, c in v.items():
            u = swap_tabloid(t, a, k); out[u] = out.get(u, 0) + c
    return {t: c for t, c in out.items() if c}


class F2Space:
    def __init__(self): self.piv = {}
    def reduce(self, x):
        while x:
            h = x.bit_length() - 1
            if h not in self.piv: return x
            x ^= self.piv[h]
        return 0
    def add(self, x):
        x = self.reduce(x)
        if x: self.piv[x.bit_length() - 1] = x; return True
        return False


def bareiss_det(M):
    M = [r[:] for r in M]; n = len(M); sign = 1; prev = 1
    for c in range(n - 1):
        if M[c][c] == 0:
            p = next((i for i in range(c + 1, n) if M[i][c]), None)
            if p is None: return 0
            M[c], M[p] = M[p], M[c]; sign = -sign
        for i in range(c + 1, n):
            for j in range(c + 1, n):
                M[i][j] = (M[i][j] * M[c][c] - M[i][c] * M[c][j]) // prev
        prev = M[c][c]
    return sign * M[n - 1][n - 1]


def main(path):
    C = json.load(open(path))
    n, lam, k = int(C["n"]), [int(x) for x in C["lambda"]], int(C["k"])
    assert sum(lam) == n and all(lam[i] >= lam[i + 1] for i in range(len(lam) - 1)) and 1 <= k <= n
    S = yamanouchi_syt(lam); f = len(S)
    # all tabloids, indexed for bit vectors
    alltabs = sorted(set(itertools.permutations([r for r, l in enumerate(lam) for _ in range(l)])))
    idx = {t: i for i, t in enumerate(alltabs)}
    def bits(v):
        x = 0
        for t, c in v.items():
            if c % 2: x |= 1 << idx[t]
        return x
    # F2-span of ALL polytabloids (every filling of the diagram)
    W = F2Space(); shape_cells = [(i, j) for i, l in enumerate(lam) for j in range(l)]
    for perm in itertools.permutations(range(1, n + 1)):
        T = [[0] * l for l in lam]
        for (i, j), x in zip(shape_cells, perm): T[i][j] = x
        W.add(bits(e_int(T, n)))
    if len(W.piv) != f: bad(f"dim of F2-span of polytabloids is {len(W.piv)}, not f={f}")
    # rank of X_k on W
    def X2(x):
        v = {alltabs[i]: 1 for i in range(len(alltabs)) if x >> i & 1}
        return bits(X(k, v))
    img = F2Space()
    for x in W.piv.values(): img.add(X2(x))
    r2 = len(img.piv)
    # Stanley's list from Yamanouchi words
    cnt = {}
    for T in S:
        for i, row in enumerate(T):
            if k in row: cnt[(i + 1, row.index(k) + 1)] = cnt.get((i + 1, row.index(k) + 1), 0) + 1
    pred = []
    for r in range(f, 0, -1):
        p = 1
        for (i, j), c in cnt.items():
            if c >= r: p *= (j - i)
        pred.append(abs(p))
    podd = sum(1 for x in pred if x % 2)
    # certificate checks
    B = C["basis"]
    if sorted(map(str, B)) != sorted(map(str, S)): bad("recorded basis is not the set of SYT")
    A, U, V, snf = C["A"], C["U"], C["V"], C["snf"]
    def int_matrix(M):
        return isinstance(M, list) and len(M) == f and all(
            isinstance(r, list) and len(r) == f and all(type(x) is int for x in r) for r in M)
    if not (int_matrix(A) and int_matrix(U) and int_matrix(V)): bad("A, U, V must be f x f integer matrices")
    if not (isinstance(snf, list) and len(snf) == f and all(type(x) is int for x in snf)): bad("snf must be f integers")
    weak = C.get("weak_form", False)
    if not isinstance(weak, bool): bad("weak_form must be true or false")
    if weak:
        mult = {}
        for T in S:
            r = next(i for i, row in enumerate(T) if k in row)
            c = T[r].index(k) - r
            mult[c] = mult.get(c, 0) + 1
        def apply(M, x):
            return [sum(M[i][j] * x[j] for j in range(f)) for i in range(f)]
        for j in range(f):
            x = [int(i == j) for i in range(f)]
            for c in mult:
                x = [y - c * z for y, z in zip(apply(A, x), x)]
            if any(x): bad("weak form: the content polynomial of A is not 0")
        for p in range(1, len(mult)):
            tr = 0
            for j in range(f):
                x = [int(i == j) for i in range(f)]
                for _ in range(p): x = apply(A, x)
                tr += x[j]
            if tr != sum(m * c ** p for c, m in mult.items()):
                bad(f"weak form: trace of A^{p} disagrees with the contents")
    E = [e_int(T, n) for T in B]
    for j in range(f):
        lhs = X(k, E[j]); rhs = {}
        for i in range(f):
            for t, c in E[i].items(): rhs[t] = rhs.get(t, 0) + A[i][j] * c
        if lhs != {t: c for t, c in rhs.items() if c}: bad(f"X_k e_T{j} != sum_i A[i][{j}] e_Ti")
    UA = [[sum(U[i][t] * A[t][j] for t in range(f)) for j in range(f)] for i in range(f)]
    UAV = [[sum(UA[i][t] * V[t][j] for t in range(f)) for j in range(f)] for i in range(f)]
    if any(UAV[i][j] != (snf[i] if i == j else 0) for i in range(f) for j in range(f)): bad("U A V != diag(snf)")
    if abs(bareiss_det(U)) != 1 or abs(bareiss_det(V)) != 1: bad("U or V is not unimodular")
    nz = [x for x in snf if x]
    if snf[:len(nz)] != nz or any(x for x in snf[len(nz):]) or any(x <= 0 for x in nz) or \
       any(b % a for a, b in zip(nz, nz[1:])): bad("snf is not a divisibility chain")
    if sum(1 for x in snf if x % 2) != r2: bad("odd invariant factors disagree with the basis-free F2 rank")
    if pred != C["predicted"]: bad("recorded prediction differs from the recomputed one")
    if weak:
        cs = sorted(mult)
        reachable = set()
        for exps in itertools.product(*[range(mult[c] + 1) for c in cs]):
            v = 1
            for c, e in zip(cs, exps): v *= c ** e
            reachable.add(abs(v))
        lonely = sorted(set(x for x in snf if x not in reachable))
        if not lonely: bad("weak form holds: each snf entry is a product of eigenvalues")
    if podd == r2: bad("no mod-2 discrepancy with Conjecture 7.4")
    print(f"ACCEPT lambda={lam} n={n} k={k}: dim_F2 span = {f}, rank_F2 X_k = {r2}, "
          f"Conjecture 7.4 needs {podd} (prediction {pred}); certificate SNF {snf} verified"
          + (f"; eigenvalue multiplicities {dict(sorted(mult.items()))}, entries {lonely} "
             f"are not products of eigenvalues" if weak else ""))


if __name__ == "__main__":
    try:
        main(sys.argv[1])
    except SystemExit:
        raise
    except Exception as exc:
        bad(f"malformed certificate: {exc!r}")
