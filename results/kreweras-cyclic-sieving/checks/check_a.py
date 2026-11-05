"""Checker A for the Reiner-Sommers Conjecture 1.4 certificate (exceptional types).

Imports nothing from the search program. Recomputes, with exact integer linear algebra
(python-flint ranks, int64 matrix products):
  - the root system, the reflections and c = s_1 ... s_n;
  - NC(W, c) bottom-up, with |NC| = Cat(W) and every element checked exactly;
  - the absolute order on NC (covers, then down-sets), with #pairs = Cat^(2)(W);
  - W-classes of the flats V^w: a generic point of V^w moved to the dominant
    chamber gives a standard parabolic J; standard J are identified up to
    W-conjugacy by Deodhar's moves (J -> w0(J+s) J w0(J+s));
  - labels: Dynkin type of J plus the number of restricted hyperplanes;
  - the fixed-point polynomials of Step 2 of the paper for each (h1, nu);
  - the right sides f_{e,1}(m; q) as exact polynomials in Z[q] (exact division
    of the tabulated quotients), reduced modulo the cyclotomic polynomial;
and compares everything with the certificate.

usage: python3 -I check_a.py TABLES.json CERT.json     (exit 0 = accept)"""
import ast
import itertools
import json
import math
import sys
from math import comb, gcd

import flint
import numpy as np


def reject(code, msg):
    print(f"REJECT {code}: {msg}", file=sys.stderr)
    sys.exit(1)


tables = json.load(open(sys.argv[1]))
cert = json.load(open(sys.argv[2]))
typ = cert["type"]
DEG = {"G2": [2, 6], "F4": [2, 6, 8, 12], "E6": [2, 5, 6, 8, 9, 12],
       "E7": [2, 6, 8, 10, 12, 14, 18], "E8": [2, 8, 12, 14, 18, 20, 24, 30]}[typ]
n, h = len(DEG), max(DEG)

# ---- root system ----
if typ == "G2":
    G = [[2, -3], [-3, 6]]
elif typ == "F4":
    G = [[4, -2, 0, 0], [-2, 4, -2, 0], [0, -2, 2, -1], [0, 0, -1, 2]]
else:
    G = [[0] * n for _ in range(n)]
    for i in range(n):
        G[i][i] = 2
    for a, b in [(1, 3), (3, 4), (4, 5), (5, 6), (6, 7), (7, 8), (2, 4)]:
        if b <= n:
            G[a - 1][b - 1] = G[b - 1][a - 1] = -1
G = np.array(G, dtype=np.int64)
I = np.eye(n, dtype=np.int64)


def refl(a):
    aa = int(a @ G @ a)
    M = I.copy()
    for j in range(n):
        k = 2 * int(a @ G[:, j])
        assert k % aa == 0
        M[:, j] -= (k // aa) * a
    return M


S = [refl(I[:, i]) for i in range(n)]
roots = {tuple(I[:, i]) for i in range(n)}
todo = list(roots)
while todo:
    r = todo.pop()
    for M in S:
        v = tuple(int(x) for x in M @ np.array(r))
        if v not in roots:
            roots.add(v)
            todo.append(v)
pos = sorted([np.array(r) for r in roots if min(r) >= 0], key=lambda r: (int(r.sum()), tuple(r)))
if len(pos) != n * h // 2:
    reject("ROOTS", "wrong number of roots")
T = [refl(a) for a in pos]
c = I.copy()
for M in S:
    c = c @ M


def ell(M):
    return flint.fmpz_mat((M - I).tolist()).rank()


def key(M):
    return M.tobytes()


# ---- NC(W, c) ----
nc, idx, rk = [I.copy()], {key(I): 0}, [0]
level = [0]
for k in range(n):
    nxt = []
    for w in level:
        for t in T:
            x = nc[w] @ t
            kx = key(x)
            if kx in idx:
                continue
            if ell(x) == k + 1 and flint.fmpz_mat((c - x).tolist()).rank() == n - k - 1:
                idx[kx] = len(nc)
                nc.append(x)
                rk.append(k + 1)
                nxt.append(idx[kx])
    level = nxt
N = len(nc)
cat = math.prod(h + d for d in DEG) // math.prod(DEG)
if N != cat or N != cert["nc_size"]:
    reject("NC_SIZE", f"{N} vs Cat {cat}")
rk = np.array(rk)
cidx = idx.get(key(c))
cinv = np.array(flint.fmpz_mat(c.tolist()).inv().tolist(), dtype=object).astype(np.int64)
conj = np.array([idx[key(c @ w @ cinv)] for w in nc])

# ---- order ----
down = [0] * N
for u in sorted(range(N), key=lambda x: rk[x]):
    d = 1 << u
    for t in T:
        z = idx.get(key(nc[u] @ t))
        if z is not None and rk[z] == rk[u] - 1:
            d |= down[z]
    down[u] = d
pz, pu = [], []
for u in range(N):
    d = down[u]
    while d:
        b = d & -d
        pz.append(b.bit_length() - 1)
        pu.append(u)
        d ^= b
pz, pu = np.array(pz), np.array(pu)
cat2 = math.prod(2 * h + d for d in DEG) // math.prod(DEG)
if len(pz) != cat2:
    reject("ORDER", f"{len(pz)} pairs vs Cat^(2) {cat2}")

# ---- classes ----
def nullspace(rows, ncols):
    if not rows:
        return [list(r) for r in I.tolist()]
    X, nul = flint.fmpz_mat(rows).nullspace()
    return [[int(X[i, j]) for i in range(ncols)] for j in range(nul)]


def dominant_J(w):
    B = nullspace((w - I).tolist(), n)  # basis of V^w
    if not B:
        return frozenset(range(n))
    B = [np.array(b, dtype=object) for b in B]
    Go = G.astype(object)
    perp = [all(int(b @ Go @ r) == 0 for b in B) for r in pos]
    for trial in itertools.count(1):
        x = sum((trial * 7919 * (i + 1) ** 3 + i * 104729) % 1999 * b for i, b in enumerate(B))
        if all(p or int(x @ Go @ r) != 0 for p, r in zip(perp, pos)):
            break
        if trial > 200:
            reject("GENERIC", "no generic point")
    while True:
        for i in range(n):
            if int(x @ Go[:, i]) < 0:
                x = S[i].astype(object) @ x
                break
        else:
            return frozenset(i for i in range(n) if int(x @ Go[:, i]) == 0)


def longest(L):
    w = I.copy()
    while True:
        for i in L:
            if (w @ I[:, i] >= 0).all():
                w = w @ S[i]
                break
        else:
            return w


subsets = [frozenset(J) for k in range(n + 1) for J in itertools.combinations(range(n), k)]
parent = {J: J for J in subsets}


def find(J):
    while parent[J] != J:
        J = parent[J]
    return J


for J in subsets:
    for s in set(range(n)) - J:
        w0 = longest(sorted(J | {s}))
        K = frozenset(int(np.nonzero((-(w0 @ I[:, j]))[:, None] == I)[0][0])
                      if False else [i for i in range(n) if (-(w0 @ I[:, j]) == I[:, i]).all()][0] for j in J)
        a, b = find(J), find(K)
        if a != b:
            parent[a] = b
cls = -np.ones(N, dtype=np.int64)
reps = {}
for w in range(N):
    if cls[w] >= 0:
        continue
    r = find(dominant_J(nc[w]))
    k = reps.setdefault(r, len(reps))
    x = w
    while cls[x] < 0:
        cls[x] = k
        x = conj[x]
if len(reps) != len({find(J) for J in subsets}):
    reject("CLASSES", "some parabolic class has no NC representative")


def comp_type(J):
    J = sorted(J)
    out, left = [], set(J)
    while left:
        st = [left.pop()]
        comp = set(st)
        while st:
            a = st.pop()
            for b in list(left):
                if G[a, b]:
                    left.discard(b)
                    comp.add(b)
                    st.append(b)
        k = len(comp)
        lens = sorted({int(G[i, i]) for i in comp})
        branch = [a for a in comp if sum(1 for b in comp if b != a and G[a, b]) == 3]
        if typ == "G2" and k == 2:
            out.append(("G", 2, False))
        elif len(lens) == 2:
            nlong = sum(1 for i in comp if G[i, i] == lens[1])
            out.append(("F", 4, False) if k == 4 else ("B", 2, False) if k == 2 else
                       ("B", 3, False) if nlong == 2 else ("C", 3, False))
        elif not branch:
            out.append(("A", k, typ in ("G2", "F4") and lens[0] < int(G.diagonal().max())))
        else:
            a = branch[0]
            leaves = [b for b in comp if sum(1 for x in comp if x != b and G[b, x]) == 1]
            # D_k: two leaves adjacent to the branch node; E_k: at most one
            adj = sum(1 for b in leaves if G[a, b])
            out.append(("D", k, False) if adj >= 2 else ("E", k, False))
    return tuple(sorted(out))


def hyperplanes(J):
    B = nullspace([[int(v) for v in G[:, j]] for j in J], n)
    seen = set()
    for r in pos:
        g = G @ r
        v = [sum(b[i] * int(g[i]) for i in range(n)) for b in B]
        if any(v):
            f = next(x for x in v if x)
            seen.add(tuple(flint.fmpq(x, f) for x in v))
    return len(seen)


def parse_label(lab):
    lab = lab.replace("(", "").replace(")", "").replace("'", "")
    if lab == "0":
        return ()
    out = []
    for part in lab.split("+"):
        i = 0
        while part[i].isdigit():
            i += 1
        mult = int(part[:i]) if i else 1
        rest = part[i:]
        out += [(rest.lstrip("~")[0], int(rest.lstrip("~")[1:]), rest.startswith("~"))] * mult
    return tuple(sorted(out))


rows = {r["label"]: r for r in tables if r["type"] == typ}
lab_of = {}
for r, k in reps.items():
    ty = comp_type(r)
    hc = hyperplanes(r)
    cand = [L for L, row in rows.items() if parse_label(L) == ty and sum(row["os_exponents"]) == hc
            and len(row["os_exponents"]) == n - len(r)]
    if len(cand) != 1:
        reject("LABEL", f"class {sorted(r)} type {ty} matches {cand}")
    lab_of[k] = cand[0]
if sorted(lab_of.values()) != sorted(rows):
    reject("LABEL", "classes and table rows are not in bijection")
cert_labels = {tuple(x["J"]): x["label"] for x in cert["classes"]}
for r, k in reps.items():
    if any(tuple(sorted(J)) in cert_labels and cert_labels[tuple(sorted(J))] != lab_of[k]
           for J in subsets if find(J) == r):
        reject("LABEL", f"certificate label differs for class {sorted(r)}")
if sorted(cert_labels.values()) != sorted(rows):
    reject("LABEL", "certificate classes differ from the table rows")


# ---- right side: exact polynomials in Z[q] ----
QP = flint.fmpz_poly([0, 1])


def qint(x):
    if x < 1:
        reject("BRACKET", f"[{x}] with x < 1")
    return flint.fmpz_poly([1] * x)


class RF:
    def __init__(self, num, den=None):
        self.n, self.d = num, den if den is not None else flint.fmpz_poly([1])

    def __mul__(self, o):
        o = o if isinstance(o, RF) else RF(flint.fmpz_poly([o]))
        return RF(self.n * o.n, self.d * o.d)

    __rmul__ = __mul__

    def __truediv__(self, o):
        return RF(self.n * o.d, self.d * o.n)

    def __add__(self, o):
        return RF(self.n * o.d + o.n * self.d, self.d * o.d)

    def __sub__(self, o):
        return RF(self.n * o.d - o.n * self.d, self.d * o.d)

    def __pow__(self, k):
        return RF(self.n ** k, self.d ** k)


def to_ast(f):
    toks, i, out = [], 0, []
    import re
    toks = re.findall(r"\d+|\*\*|[A-Za-z]|[()+\-*/]", f)
    for t in toks:
        if out and (out[-1] in (")", "m", "q") or out[-1].isdigit()) and (t in ("m", "q", "B", "(") or t.isdigit()):
            out.append("*")
        out.append(t)
    return ast.parse("".join(out), mode="eval").body


def ev(node, m, mode):
    """mode 'poly': RF in Z[q]; mode 'int': plain integers for exponents"""
    if isinstance(node, ast.Constant):
        return node.value
    if isinstance(node, ast.Name):
        if node.id == "m":
            return m
        if node.id == "q":
            return RF(QP)
        reject("PARSE", node.id)
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
        return -ev(node.operand, m, mode)
    if isinstance(node, ast.Call) and node.func.id == "B":
        x = ev(node.args[0], m, "int")
        return RF(qint(x))
    if isinstance(node, ast.BinOp):
        if isinstance(node.op, ast.Pow):
            base = node.left
            e = ev(node.right, m, "int")
            if isinstance(base, ast.Name) and base.id == "q":
                if e < 0:
                    reject("PARSE", "negative power of q")
                return RF(QP ** e)
            return ev(base, m, mode) ** e
        a, b = ev(node.left, m, mode), ev(node.right, m, mode)
        if isinstance(a, int) and isinstance(b, int):
            return {ast.Add: a + b, ast.Sub: a - b, ast.Mult: a * b}[type(node.op)]
        if isinstance(node.op, ast.Add):
            return a + b
        if isinstance(node.op, ast.Sub):
            return a - b
        if isinstance(node.op, ast.Mult):
            return a * b
        if isinstance(node.op, ast.Div):
            return a / b
    reject("PARSE", ast.dump(node))


ASTS = {L: to_ast(r["f"]) for L, r in rows.items()}
CYC = {}


def rhs(L, s, d):
    m = s * h + 1
    v = ev(ASTS[L], m, "poly")
    if not isinstance(v, RF):
        v = RF(flint.fmpz_poly([v]))
    qq, rr = divmod(v.n, v.d)
    if rr != 0:
        reject("NOT_POLY", f"{L} at m={m} is not a polynomial in q")
    if d not in CYC:
        CYC[d] = flint.fmpz_poly.cyclotomic(d)
    red = qq % CYC[d]
    if red.degree() > 0:
        reject("NOT_RATIONAL", f"{L} at m={m}, d={d}")
    val = int(red[0]) if red.degree() == 0 else 0
    if val < 0:
        reject("NEGATIVE", f"{L} at m={m}, d={d}: {val}")
    return val


# structural facts used for large nu (Step 4 of the paper)
def has_m1_factor(node):
    if isinstance(node, ast.Call):
        a = node.args[0]
        return (isinstance(a, ast.BinOp) and isinstance(a.op, ast.Sub) and isinstance(a.left, ast.Name)
                and a.left.id == "m" and isinstance(a.right, ast.Constant) and a.right.value == 1)
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Mult):
        return has_m1_factor(node.left) or has_m1_factor(node.right)
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Div):
        return has_m1_factor(node.left)
    return False


def const_brackets(node, acc):
    if isinstance(node, ast.Call) and isinstance(node.args[0], ast.Constant):
        acc.append(node.args[0].value)
    for ch in ast.iter_child_nodes(node):
        if isinstance(ch, ast.BinOp) and isinstance(ch.op, ast.Pow) and isinstance(ch.left, ast.Call) \
                and isinstance(ch.left.args[0], ast.Constant):
            acc.extend([ch.left.args[0].value] * ch.right.value)
        else:
            const_brackets(ch, acc)
    return acc


def lin(node):
    """an integer expression a*m + b; returns (a, b)"""
    for sub in ast.walk(node):
        if not isinstance(sub, (ast.BinOp, ast.UnaryOp, ast.Constant, ast.Name, ast.Add, ast.Sub,
                                ast.Mult, ast.USub, ast.Load)) or \
                (isinstance(sub, ast.Name) and sub.id != "m") or \
                (isinstance(sub, ast.Constant) and not isinstance(sub.value, int)):
            reject("SHAPE", "exponent or bracket argument is not an integer expression in m")
    v = [eval(compile(ast.Expression(node), "<l>", "eval"), {"__builtins__": {}}, {"m": x}) for x in (0, 1, 2)]
    if v[2] - v[1] != v[1] - v[0]:
        reject("SHAPE", "not linear in m")
    return v[1] - v[0], v[0]


def is_qpow(nd):
    if isinstance(nd, ast.Name) and nd.id == "q":
        return True
    return isinstance(nd, ast.BinOp) and isinstance(nd.op, ast.Pow) and isinstance(nd.left, ast.Name) \
        and nd.left.id == "q" and lin(nd.right) is not None


def is_mbracket(nd):
    return isinstance(nd, ast.Call) and nd.func.id == "B" and lin(nd.args[0])[0] == 1


def is_cbracket(nd):
    return isinstance(nd, ast.Call) and nd.func.id == "B" and lin(nd.args[0])[0] == 0 and lin(nd.args[0])[1] >= 1


def denom(nd):
    if is_cbracket(nd):
        return True
    if isinstance(nd, ast.BinOp) and isinstance(nd.op, ast.Pow) and is_cbracket(nd.left) \
            and isinstance(nd.right, ast.Constant):
        return True
    return isinstance(nd, ast.BinOp) and isinstance(nd.op, ast.Mult) and denom(nd.left) and denom(nd.right)


def sumterm(nd):
    return is_mbracket(nd) or (isinstance(nd, ast.BinOp) and isinstance(nd.op, ast.Mult)
                               and is_qpow(nd.left) and is_mbracket(nd.right))


def is_sum(nd):
    if isinstance(nd, ast.BinOp) and isinstance(nd.op, (ast.Add, ast.Sub)):
        return (is_sum(nd.left) or sumterm(nd.left)) and sumterm(nd.right)
    return False


def shape(nd):
    """number of numerator brackets (a sum counts once) of a row of the allowed shape:
    products of q^(a m + b), [m - a], sums of q^c-weighted [m - a], over products of [k]"""
    if is_qpow(nd):
        return 0
    if is_mbracket(nd):
        return 1
    if is_sum(nd):
        return 1
    if isinstance(nd, ast.BinOp) and isinstance(nd.op, ast.Mult):
        return shape(nd.left) + shape(nd.right)
    if isinstance(nd, ast.BinOp) and isinstance(nd.op, ast.Div):
        if not denom(nd.right):
            reject("SHAPE", "denominator is not a product of constant brackets")
        return shape(nd.left)
    reject("SHAPE", ast.dump(nd)[:120])


for L, a in ASTS.items():
    if shape(a) > n:
        reject("DEGREE", f"{L}: more than n numerator brackets")


regular = [L for L, r in rows.items() if not r["os_exponents"]]
if len(regular) != 1:
    reject("REGULAR", "no unique regular row")
regular = regular[0]
maxden = 0
for L, a in ASTS.items():
    cb = const_brackets(a, [])
    if len(cb) > n:
        reject("DEGREE", f"{L} has {len(cb)} denominator brackets > n")
    maxden = max([maxden] + cb)
    if L != regular and not has_m1_factor(a):
        reject("M1_FACTOR", f"{L} lacks a top-level [m-1] factor")
if rows[regular]["f"].replace(" ", "") != f"q**({n}m-{n})":
    reject("REGULAR", rows[regular]["f"])

# ---- left side: the reduction ----
def cpow_perm(e):
    p = np.arange(N)
    for _ in range(e % h):
        p = conj[p]
    return p


certred = {(e["h1"], e["nu"]): e for e in cert["reduction"]}
e_id = idx[key(I)]
expected = set()
for h1 in [x for x in range(1, h + 1) if h % x == 0]:
    ph = cpow_perm(h1)
    inC = ph == np.arange(N)
    mask = inC[pz] & inC[pu] & (pz != pu)
    az, au = pz[mask], pu[mask]
    ck = [np.zeros(N, dtype=object)]
    ck[0][e_id] = 1
    for k in range(n):
        nx = np.zeros(N, dtype=object)
        np.add.at(nx, au, ck[-1][az])
        ck.append(nx)
    for nu in range(1, n + 1):
        if gcd(h1, nu) != 1:
            continue
        expected.add((h1, nu))
        a, b = divmod(h1, nu)
        ex = [None] * (nu + 1)
        ex[1], k = 0, 1
        for _ in range(nu - 1):
            k2 = k + b
            ex[k2 if k2 <= nu else k2 - nu] = ex[k] + (a if k2 <= nu else a + 1)
            k = k2 if k2 <= nu else k2 - nu
        if (ex[k] + (a if k + b <= nu else a + 1)) != h1 and nu > 1:
            reject("CYCLE", "exponents do not close up")
        perms = [cpow_perm(ex[j]) for j in range(1, nu + 1)]
        poly = {}
        for u in np.nonzero(inC)[0]:
            P = I.copy()
            for p in perms:
                P = P @ nc[p[u]]
            w0 = c @ np.array(flint.fmpz_mat(P.tolist()).inv().tolist(), dtype=object).astype(np.int64)
            if ell(w0) + nu * int(rk[u]) != n:
                continue
            j = idx.get(key(w0))
            if j is None:
                reject("W0", "w0 not in NC")
            co = poly.setdefault(lab_of[cls[j]], [0] * (n + 1))
            for kk in range(n + 1):
                co[kk] += int(ck[kk][u])
        ce = certred.get((h1, nu))
        if ce is None or ce["d"] != nu * (h // h1):
            reject("COVER", f"certificate lacks (h1, nu) = ({h1}, {nu})")
        cp = {L: v for L, v in ce["binomial_coeffs"].items() if any(v)}
        if cp != {L: v for L, v in poly.items() if any(v)}:
            reject("LHS", f"fixed-point polynomial differs at (h1, nu) = ({h1}, {nu})")
        d = ce["d"]
        for m1 in range(1, n + 3):
            for L in rows:
                lhs = sum(cf * comb(m1, kk) for kk, cf in enumerate(cp.get(L, [0])))
                if lhs != rhs(L, m1 * nu, d):
                    reject("IDENTITY", f"{L}: (h1, nu, m1) = ({h1}, {nu}, {m1})")
if set(certred) != expected:
    reject("COVER", "certificate (h1, nu) set differs")

# ---- nu > n ----
big = set()
for h1 in [x for x in range(1, h + 1) if h % x == 0]:
    h2 = h // h1
    for nu in range(n + 1, maxden + 1):
        if gcd(h1, nu) == 1 and nu * h2 <= maxden:
            big.add((h1, nu))
            for m1 in range(1, n + 3):
                for L in rows:
                    if rhs(L, m1 * nu, nu * h2) != (1 if L == regular else 0):
                        reject("LARGE", f"{L}: (h1, nu, m1) = ({h1}, {nu}, {m1})")
if big != {(e["h1"], e["nu"]) for e in cert["large_m2"]}:
    reject("COVER", "certificate large-nu set differs")
print(json.dumps({"type": typ, "status": "ACCEPT", "nc": N, "pairs": int(len(pz)), "classes": len(reps),
                  "pairs_h1_m2": len(expected), "large_m2": len(big), "max_denominator": maxden}))
