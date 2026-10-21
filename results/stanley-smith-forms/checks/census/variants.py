"""Corrected readings of Stanley's Conjecture 7.4 tested against the census.

Optional program, not part of the check.  Needs python-flint.

Usage, from the folder holding checks/ and data/:
    python3 checks/census/variants.py [NMAX=8] [--cache PATH]
prints a markdown table, one row per reading.  With --cache, the Smith forms
of X_k and Y_k are stored in PATH (and read from it if it exists); without it
nothing is written.

For every lambda |- n <= NMAX the integral Specht lattice S^lambda_Z is built
with specht_lattice.py (HNF closure of one polytabloid inside the tabloid
module).  Matrices of the simple transpositions s_i in that basis are computed
once (exact coordinates, checked); every transposition (a b) is then obtained
by conjugation, giving
  X_k = sum_{i<k} (i k)   and   Y_k = sum_{i>k} (i k)
for every k.  The SNF of X_k is checked against data/census-n8.json.
Each variant produces a predicted invariant-factor list for (lambda, k) and an
"actual" list (SNF of X_k, or of another element); a case matches when the two
lists agree after taking absolute values (zeros last, as in an SNF).
"""
import sys, os, json, itertools
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import flint
sys.dont_write_bytecode = True  # write nothing into this folder
import specht_lattice as S

ARGS = [a for a in sys.argv[1:]]
CACHE = None
if "--cache" in ARGS:
    i = ARGS.index("--cache")
    CACHE = ARGS[i + 1]
    del ARGS[i:i + 2]
NMAX = int(ARGS[0]) if ARGS else 8
CENSUS = os.path.join(HERE, "..", "..", "data", "census-n8.json")


# ---------------------------------------------------------------- lattices
def mat_coords(B, W):
    """Rows of W in the HNF basis B (rows): C with C*B = W, exact."""
    piv = [next(i for i, x in enumerate(b) if x) for b in B]
    Bp = flint.fmpq_mat([[b[p] for p in piv] for b in B])
    Wp = flint.fmpq_mat([[w[p] for p in piv] for w in W])
    Cq = Wp * Bp.inv()
    C = []
    for i in range(Cq.nrows()):
        row = []
        for j in range(Cq.ncols()):
            x = Cq[i, j]
            assert x.q == 1, "not in lattice"
            row.append(int(x.p))
        C.append(row)
    assert (flint.fmpz_mat(C) * flint.fmpz_mat(B)).tolist() == flint.fmpz_mat(W).tolist()
    return C


def element_snfs(lam):
    """{k: (snf X_k, snf Y_k)} on S^lam_Z (row convention: rows = images)."""
    n = sum(lam)
    idx = S.tabloid_index(lam)
    keys = {i: t for t, i in idx.items()}
    B = S.specht_lattice(lam, idx, keys)
    f = len(B)
    simple = []
    for i in range(n - 1):
        g = S.transposition(n, i, i + 1)
        simple.append(flint.fmpz_mat(mat_coords(B, [S.act(g, b, idx, keys) for b in B])))
    # rows = images of basis vectors, so the matrix of a product gh (g after h)
    # is M_h * M_g; conjugation (a, b+1) = s_b (a, b) s_b is symmetric anyway.
    T = {}
    for i in range(n - 1):
        T[(i, i + 1)] = simple[i]
    for d in range(2, n):
        for a in range(0, n - d):
            b = a + d
            s = simple[b - 1]
            T[(a, b)] = s * T[(a, b - 1)] * s
    out = {}
    zero = flint.fmpz_mat(f, f)
    for k in range(1, n + 1):
        X = zero
        for i in range(k - 1):
            X = X + T[(i, k - 1)]
        Y = zero
        for i in range(k, n):
            Y = Y + T[(k - 1, i)]
        out[k] = (snf(X), snf(Y))
    return f, out


def snf(M):
    D = M.snf()
    return S.normalize([abs(int(D[i, i])) for i in range(min(D.nrows(), D.ncols()))])


def smith_diag(lst):
    f = len(lst)
    if f == 0:
        return []
    return snf(flint.fmpz_mat([[lst[i] if i == j else 0 for j in range(f)] for i in range(f)]))


# ---------------------------------------------------------------- tableaux data
def conj(l):
    return tuple(sum(1 for x in l if x > j) for j in range(l[0]))


def cell_counts(lam, k):
    """cell (i, j) 1-based -> number of SYT of shape lam with k in that cell."""
    return Counter(S.predicted(lam, k)[1])


def restricted_counts(lam, k, upto):
    """cell -> number of distinct restrictions of SYT(lam) to entries <= k
    (upto=True) or >= k (upto=False) that put k in that cell."""
    seen = set()
    for t in S.syt(lam):
        pos = {}
        for i, row in enumerate(t):
            for j, x in enumerate(row):
                pos[x + 1] = (i + 1, j + 1)
        part = tuple(pos[v] for v in (range(1, k + 1) if upto else range(k, sum(lam) + 1)))
        seen.add((pos[k], part))
    return Counter(c for c, _ in seen)


def content(c):
    return c[1] - c[0]


def prod(cells, absolute=True):
    p = 1
    for c in cells:
        p *= content(c)
    return abs(p)


# ---------------------------------------------------------------- variants
def thresholded(cnt, f, test):
    """list L with L[r-1] = prod over cells with test(count, r), r = 1..f"""
    return [prod([c for c, m in cnt.items() if test(m, r)]) for r in range(1, f + 1)]


def literal(L):
    """alpha_{f-r+1} = L[r-1]: reversed list, compared position-wise."""
    return list(reversed(L))


def nozero_prod(cells):
    if cells and all(content(c) == 0 for c in cells):
        return 0
    return prod([c for c in cells if content(c) != 0])


def eigen(cnt):
    ev = []
    for c, m in cnt.items():
        ev += [abs(content(c))] * m
    return ev


def subset_products(ev):
    ps = {1}
    for e in ev:
        ps |= {p * e for p in ps}
    return ps


def main():
    census = {(tuple(r["lam"]), r["k"]): r for r in json.load(open(CENSUS))
              if r["lattice"] == "specht"}
    cache = CACHE
    if cache and os.path.exists(cache):
        E = {(tuple(e["lam"]), e["k"]): e for e in json.load(open(cache))}
    else:
        E = {}
        for n in range(1, NMAX + 1):
            for lam in S.partitions(n):
                f, out = element_snfs(lam)
                for k, (sx, sy) in out.items():
                    E[(lam, k)] = dict(n=n, lam=list(lam), k=k, f=f, X=sx, Y=sy)
            print("lattices done n =", n, file=sys.stderr, flush=True)
        if cache:
            json.dump(list(E.values()), open(cache, "w"))
    # consistency with the census
    for key, e in E.items():
        assert e["X"] == census[key]["snf"], key
    cases = sorted(E, key=lambda t: (sum(t[0]), [-x for x in t[0]], t[1]))

    def actX(lam, k):
        return E[(lam, k)]["X"]

    V = []  # (name, function (lam,k) -> (pred, actual) or None if out of range)

    def add(name, fn):
        V.append((name, fn))

    def base(lam, k):
        f = E[(lam, k)]["f"]
        return f, cell_counts(lam, k)

    ge = lambda m, r: m >= r
    # 0 baseline
    add("0. Stanley as stated: alpha_{f-r+1}=prod S_r, S_r = count>=r",
        lambda lam, k: (S.normalize(literal(thresholded(base(lam, k)[1], base(lam, k)[0], ge))), actX(lam, k)))
    # 1 indexing
    add("1a. alpha_r = prod S_r (position-wise)",
        lambda lam, k: (thresholded(base(lam, k)[1], base(lam, k)[0], ge), actX(lam, k)))
    add("1b. multiset: SNF(diag(prod S_1..prod S_f))",
        lambda lam, k: (smith_diag(thresholded(base(lam, k)[1], base(lam, k)[0], ge)), actX(lam, k)))
    # 2 definitions of S_r
    defs = [("exactly r", lambda m, r: m == r),
            ("more than r (= at least r+1)", lambda m, r: m > r),
            ("at most r (cells k occupies)", lambda m, r: 1 <= m <= r)]
    for tag, test in defs:
        add("2. S_r = count %s, literal" % tag,
            lambda lam, k, test=test: (literal(thresholded(base(lam, k)[1], base(lam, k)[0], test)), actX(lam, k)))
        add("2. S_r = count %s, Smith-normalized" % tag,
            lambda lam, k, test=test: (smith_diag(thresholded(base(lam, k)[1], base(lam, k)[0], test)), actX(lam, k)))

    def classes(lam, k, largest_first):
        f, cnt = base(lam, k)
        ms = sorted(set(cnt.values()), reverse=largest_first)
        L = [prod([c for c, m in cnt.items() if m == mm]) for mm in ms]
        return L + [1] * (f - len(L))
    add("2. multiplicity classes, r-th smallest -> alpha_{f-r+1}",
        lambda lam, k: (literal(classes(lam, k, False)), actX(lam, k)))
    add("2. multiplicity classes, r-th largest -> alpha_{f-r+1}",
        lambda lam, k: (literal(classes(lam, k, True)), actX(lam, k)))
    add("2. multiplicity classes, Smith-normalized",
        lambda lam, k: (smith_diag(classes(lam, k, False)), actX(lam, k)))
    add("2. cells with multiplicity: SNF(diag of eigenvalues)",
        lambda lam, k: (smith_diag(eigen(base(lam, k)[1])), actX(lam, k)))

    def nz(lam, k):
        f, cnt = base(lam, k)
        return [nozero_prod([c for c, m in cnt.items() if m >= r]) for r in range(1, f + 1)]
    add("2. |contents|, zero contents dropped, literal",
        lambda lam, k: (literal(nz(lam, k)), actX(lam, k)))
    add("2. |contents|, zero contents dropped, Smith-normalized",
        lambda lam, k: (smith_diag(nz(lam, k)), actX(lam, k)))

    # 3 range / definition of k
    pred0 = lambda lam, k: S.normalize(literal(thresholded(base(lam, k)[1], base(lam, k)[0], ge)))
    add("3. formula(k) vs SNF X_{k+1} (k<n only)",
        lambda lam, k: None if k == sum(lam) else (pred0(lam, k), actX(lam, k + 1)))
    add("3. formula(k) vs SNF X_{k-1} (k>1 only)",
        lambda lam, k: None if k == 1 else (pred0(lam, k), actX(lam, k - 1)))
    add("3. formula(k) vs SNF Y_k, Y_k = sum_{i>k}(i k)",
        lambda lam, k: (pred0(lam, k), E[(lam, k)]["Y"]))
    add("3. formula(k) vs SNF Y_{n+1-k} (X_k, labels counted from n down)",
        lambda lam, k: (pred0(lam, k), E[(lam, sum(lam) + 1 - k)]["Y"]))
    add("3. formula(n+1-k) vs SNF X_k",
        lambda lam, k: (pred0(lam, sum(lam) + 1 - k), actX(lam, k)))
    add("3. formula(lambda', k) vs SNF X_k on S^lambda",
        lambda lam, k: (pred0(conj(lam), k), actX(lam, k)))
    add("3. check: SNF X_k on S^lambda' vs on S^lambda",
        lambda lam, k: (actX(conj(lam), k), actX(lam, k)))
    add("3. check: SNF Y_{n+1-k} vs SNF X_k",
        lambda lam, k: (E[(lam, sum(lam) + 1 - k)]["Y"], actX(lam, k)))

    # 4 counting only partial fillings
    for upto, tag in [(True, "1..k"), (False, "k..n")]:
        def fn(lam, k, upto=upto):
            f = E[(lam, k)]["f"]
            cnt = restricted_counts(lam, k, upto)
            return S.normalize(literal(thresholded(cnt, f, ge))), actX(lam, k)
        add("4. count = # standard fillings of entries %s with k in cell" % tag, fn)
        def fn2(lam, k, upto=upto):
            f = E[(lam, k)]["f"]
            cnt = restricted_counts(lam, k, upto)
            return smith_diag(thresholded(cnt, f, ge)), actX(lam, k)
        add("4. same, %s, Smith-normalized" % tag, fn2)

    # weak form
    def weak(lam, k):
        ps = subset_products(eigen(base(lam, k)[1]))
        a = actX(lam, k)
        ok = all(x == 0 or x in ps for x in a)
        return (a, a) if ok else (a, None)
    add("W. weak form: every nonzero alpha a product of eigenvalues (sub-multiset)", weak)

    rows = []
    ex = ((5, 1), 5)
    for name, fn in V:
        m7 = t7 = m8 = t8 = 0
        first = None
        for (lam, k) in cases:
            if sum(lam) > NMAX:
                continue
            r = fn(lam, k)
            if r is None:
                continue
            p, a = r
            ok = (p == a)
            if sum(lam) <= 7:
                t7 += 1; m7 += ok
            t8 += 1; m8 += ok
            if not ok and first is None:
                lamstr = "(" + ",".join(map(str, lam)) + ")"
                if a is None:
                    first = "%s, k=%d: SNF %s, eigenvalues %s" % (
                        lamstr, k, p, sorted(eigen(base(lam, k)[1])))
                else:
                    first = "%s, k=%d: pred %s, actual %s" % (lamstr, k, p, a)
        r = fn(*ex)
        exs = "n/a" if r is None else ("yes" if r[0] == r[1] == [1, 1, 3, 3, 12] or
                                      (r[0] == r[1] and name.startswith("3. check")) or
                                      (name.startswith("W.") and r[0] == r[1]) else
                                      "no (%s)" % r[0])
        rows.append((name, m7, t7, m8, t8, exs, first or "none"))
    print("| variant | n<=7 | n<=8 | (5,1),k=5 -> (1,1,3,3,12) | first failure |")
    print("|---|---|---|---|---|")
    for name, m7, t7, m8, t8, exs, first in rows:
        print("| %s | %d/%d | %d/%d | %s | %s |" % (name, m7, t7, m8, t8, exs, first))


if __name__ == "__main__":
    main()
