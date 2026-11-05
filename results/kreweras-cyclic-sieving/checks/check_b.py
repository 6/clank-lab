"""Checker B for the Reiner-Sommers Conjecture 1.4 certificate (exceptional types).

Independent of the search program and of check_a.py. Different representations and methods:
  - W acts by permutations of the roots; c = s_1 ... s_n as a permutation;
  - V^w is spanned by the root-orbit sums of w, so dim V^w is the rank of those
    sums, and t_beta <= w (absolute order) iff beta is orthogonal to them;
  - NC(W, c) is built top-down from c by lower covers;
  - classes of flats are identified by the invariant (Dynkin type of the
    parabolic root subsystem, number of restricted hyperplanes); the number of
    distinct invariants must equal the number of table rows;
  - the block exponents of the reduction are derived by iterating the twisted
    rotation symbolically, not from the closed formula;
  - small-s fixed points are recounted by applying Bessis-Reiner (6.4) literally
    to (w0; w1, ..., ws), including the conjugated w0;
  - the right side is evaluated from leading terms of each factor at
    q = omega_d e^eps (Krattenthaler-Mueller's limit rule, extended to the
    bracketed sums by their first nonvanishing derivative).

usage: python3 -I check_b.py TABLES.json CERT.json [brute_s_max]   (exit 0 = accept)"""
import ast
import itertools
import json
import math
import re
import sys
from fractions import Fraction
from math import comb, gcd

import flint
import numpy as np


def reject(code, msg):
    print(f"REJECT {code}: {msg}", file=sys.stderr)
    sys.exit(1)


tables = json.load(open(sys.argv[1]))
cert = json.load(open(sys.argv[2]))
BRUTE = int(sys.argv[3]) if len(sys.argv) > 3 else 1
typ = cert["type"]
DEG = {"G2": [2, 6], "F4": [2, 6, 8, 12], "E6": [2, 5, 6, 8, 9, 12],
       "E7": [2, 6, 8, 10, 12, 14, 18], "E8": [2, 8, 12, 14, 18, 20, 24, 30]}[typ]
n, h = len(DEG), max(DEG)
if typ == "G2":
    G = np.array([[2, -3], [-3, 6]])
elif typ == "F4":
    G = np.array([[4, -2, 0, 0], [-2, 4, -2, 0], [0, -2, 2, -1], [0, 0, -1, 2]])
else:
    G = 2 * np.eye(n, dtype=np.int64)
    chain = [1, 3, 4, 5, 6, 7, 8][:n - 1]
    for a, b in list(zip(chain, chain[1:])) + [(2, 4)]:
        G[a - 1, b - 1] = G[b - 1, a - 1] = -1

# ---- roots and permutations ----
def sref(v, a):
    return v - (2 * int(v @ G @ a) // int(a @ G @ a)) * a


simple = [np.eye(n, dtype=np.int64)[i] for i in range(n)]
R = [tuple(a) for a in simple]
seen = set(R)
k = 0
while k < len(R):
    for a in simple:
        v = tuple(sref(np.array(R[k]), a))
        if v not in seen:
            seen.add(v)
            R.append(v)
    k += 1
R = sorted(R)
ridx = {r: i for i, r in enumerate(R)}
RA = np.array(R, dtype=np.int64)
NR = len(R)
posi = [i for i, r in enumerate(R) if min(r) >= 0]
if 2 * len(posi) != NR or len(posi) != n * h // 2:
    reject("ROOTS", "wrong root count")


def perm_of(a):
    return np.array([ridx[tuple(sref(np.array(r), a))] for r in R])


Sp = [perm_of(a) for a in simple]
Tp = [perm_of(RA[i]) for i in posi]
ident = np.arange(NR)
cp = ident
for P in Sp:
    cp = cp[P]          # c = s1 o s2 o ... o sn  (apply sn first)
GR = RA @ G             # rows: (root, .) pairings


def orbit_sums(P):
    seen = np.zeros(NR, bool)
    out = []
    for i in range(NR):
        if not seen[i]:
            j, acc = i, np.zeros(n, dtype=np.int64)
            while not seen[j]:
                seen[j] = True
                acc = acc + RA[j]
                j = P[j]
            out.append(acc)
    return np.array(out)


def fixdim(P):
    return flint.fmpz_mat(orbit_sums(P).tolist()).rank()


def perp_roots(P):
    """indices of roots orthogonal to V^w"""
    O = orbit_sums(P)
    return np.nonzero(~((GR @ O.T) != 0).any(axis=1))[0]


inv = lambda P: np.argsort(P)

# ---- NC(W, c), top-down ----
nc = [cp]
idx = {cp.tobytes(): 0}
rank = [n]
level = [0]
covers = []
posset = {r: k for k, r in enumerate(posi)}
for r in range(n, 0, -1):
    nxt = []
    for u in level:
        below = [posset[i] for i in perp_roots(nc[u]) if i in posset]
        if len(below) == 0:
            reject("NC", "element without reflections below")
        for t in below:
            x = nc[u][Tp[t]]          # u o t
            kx = x.tobytes()
            if kx not in idx:
                idx[kx] = len(nc)
                nc.append(x)
                rank.append(r - 1)
                nxt.append(idx[kx])
            covers.append((idx[kx], u))
    level = nxt
N = len(nc)
cat = math.prod(h + d for d in DEG) // math.prod(DEG)
if N != cat:
    reject("NC_SIZE", f"{N} != Cat {cat}")
rank = np.array(rank)
for w in range(N):
    if n - fixdim(nc[w]) != rank[w]:
        reject("RANK", "absolute length mismatch")
e_id = idx[ident.tobytes()]
cinv = inv(cp)
conj = np.array([idx[cp[nc[w]][cinv].tobytes()] for w in range(N)])

# order: down-sets from covers
downs = [None] * N
lower = [[] for _ in range(N)]
for z, u in covers:
    lower[u].append(z)
for w in sorted(range(N), key=lambda x: rank[x]):
    d = 1 << w
    for z in lower[w]:
        d |= downs[z]
    downs[w] = d
pz, pu = [], []
for u in range(N):
    d = downs[u]
    while d:
        b = d & -d
        pz.append(b.bit_length() - 1)
        pu.append(u)
        d ^= b
pz, pu = np.array(pz), np.array(pu)
if len(pz) != math.prod(2 * h + d for d in DEG) // math.prod(DEG):
    reject("ORDER", "pair count differs from Cat^(2)")

# ---- classes by invariant ----
def dynkin(simple_idx):
    vecs = [RA[i] for i in simple_idx]
    k = len(vecs)
    M = [[int(a @ G @ b) for b in vecs] for a in vecs]
    allmax = int(G.diagonal().max())
    comps, left = [], set(range(k))
    while left:
        st = [left.pop()]
        comp = {st[0]}
        while st:
            a = st.pop()
            for b in list(left):
                if M[a][b]:
                    left.discard(b)
                    comp.add(b)
                    st.append(b)
        comps.append(comp)
    out = []
    for comp in comps:
        m = len(comp)
        lens = sorted({M[i][i] for i in comp})
        deg = {a: sum(1 for b in comp if b != a and M[a][b]) for a in comp}
        if len(lens) == 2:
            if any(M[a][b] ** 2 == M[a][a] * M[b][b] * 3 // 4 for a in comp for b in comp if a != b and M[a][b]):
                out.append(("G", 2, False))
            elif m == 4:
                out.append(("F", 4, False))
            elif m == 2:
                out.append(("B", 2, False))
            else:
                nlong = sum(1 for i in comp if M[i][i] == lens[1])
                out.append(("B", 3, False) if nlong == 2 else ("C", 3, False))
        elif max(deg.values()) <= 2:
            out.append(("A", m, typ in ("G2", "F4") and lens[0] < allmax))
        else:
            br = next(a for a in comp if deg[a] == 3)
            short_arms = sum(1 for b in comp if M[br][b] and b != br and deg[b] == 1)
            out.append(("D", m, False) if short_arms >= 2 else ("E", m, False))
    return tuple(sorted(out))


def invariant(w):
    perp = set(perp_roots(nc[w]).tolist())
    pos_perp = [i for i in posi if i in perp]
    sums = set()
    for a, b in itertools.combinations(pos_perp, 2):
        sums.add(tuple(RA[a] + RA[b]))
    simple_idx = [i for i in pos_perp if R[i] not in sums]
    # restricted hyperplanes: beta, gamma (not in perp) give the same one iff
    # span(perp + beta) contains gamma
    base = [RA[i].tolist() for i in simple_idx]
    r0 = len(base)
    groups = set()
    for b in posi:
        if b in perp:
            continue
        mem = []
        for g in posi:
            if g in perp:
                continue
            if flint.fmpz_mat(base + [RA[b].tolist(), RA[g].tolist()]).rank() == r0 + 1:
                mem.append(g)
        groups.add(tuple(mem))
    return dynkin(simple_idx), len(groups)


cls_inv = [None] * N
for w in range(N):
    if cls_inv[w] is not None:
        continue
    key = invariant(w)
    x = w
    while cls_inv[x] is None:
        cls_inv[x] = key
        x = conj[x]


def parse_label(lab):
    lab = lab.replace("(", "").replace(")", "").replace("'", "")
    if lab == "0":
        return ()
    out = []
    for part in lab.split("+"):
        mt = re.match(r"(\d*)(~?)([A-Z])(\d+)$", part)
        out += [(mt.group(3), int(mt.group(4)), mt.group(2) == "~")] * (int(mt.group(1)) if mt.group(1) else 1)
    return tuple(sorted(out))


rows = {r["label"]: r for r in tables if r["type"] == typ}
invs = set(cls_inv)
if len(invs) != len(rows):
    reject("CLASSES", f"{len(invs)} invariants for {len(rows)} rows")
lab_of = {}
for iv in invs:
    cand = [L for L, r in rows.items() if parse_label(L) == iv[0] and sum(r["os_exponents"]) == iv[1]]
    if len(cand) != 1:
        reject("LABEL", f"{iv}: {cand}")
    lab_of[iv] = cand[0]
if sorted(lab_of.values()) != sorted(rows):
    reject("LABEL", "not a bijection")
label = [lab_of[cls_inv[w]] for w in range(N)]
cnt = {L: label.count(L) for L in rows}
for x in cert["classes"]:
    if cnt[x["label"]] != x["count_s1"]:
        reject("LABEL", f"class size of {x['label']}")

# ---- right side by leading terms ----
class K:
    """Q(zeta_d) via flint fmpq_poly modulo the cyclotomic polynomial"""
    def __init__(self, d):
        self.d = d
        self.phi = flint.fmpq_poly(list(flint.fmpz_poly.cyclotomic(d).coeffs()))

    def w(self, k):
        k %= self.d
        return flint.fmpq_poly([0] * k + [1]) % self.phi

    def inv(self, a):
        g, s, _ = a.xgcd(self.phi)
        if g != 1:
            reject("FIELD", "non-invertible")
        return s % self.phi


def toks(f):
    out = []
    for t in re.findall(r"\d+|\*\*|[A-Za-z]|[()+\-*/]", f):
        if out and (out[-1] in (")", "m", "q") or out[-1].isdigit()) and (t in ("m", "q", "B", "(") or t.isdigit()):
            out.append("*")
        out.append(t)
    return ast.parse("".join(out), mode="eval").body


def ival(node, m):
    return eval(compile(ast.Expression(node), "<e>", "eval"), {"__builtins__": {}}, {"m": m})


def lead(node, m, F):
    """leading term (value in Q(zeta_d), order in eps) of a product/quotient tree"""
    if isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Mult, ast.Div)):
        a, b = lead(node.left, m, F), lead(node.right, m, F)
        if isinstance(node.op, ast.Mult):
            return ((a[0] * b[0]) % F.phi, a[1] + b[1])
        return ((a[0] * F.inv(b[0])) % F.phi, a[1] - b[1])
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Pow):
        a = lead(node.left, m, F)
        e = ival(node.right, m)
        if isinstance(node.left, ast.Name):
            return (F.w(e), 0)
        v = flint.fmpq_poly([1])
        for _ in range(e):
            v = (v * a[0]) % F.phi
        return (v, a[1] * e)
    if isinstance(node, ast.Name) and node.id == "q":
        return (F.w(1), 0)
    terms = []  # sum of sign * q^c * [x]

    def collect(nd, sign):
        if isinstance(nd, ast.BinOp) and isinstance(nd.op, (ast.Add, ast.Sub)):
            collect(nd.left, sign)
            collect(nd.right, sign if isinstance(nd.op, ast.Add) else -sign)
        elif isinstance(nd, ast.Call):
            terms.append((sign, 0, ival(nd.args[0], m)))
        elif isinstance(nd, ast.BinOp) and isinstance(nd.op, ast.Mult) and isinstance(nd.right, ast.Call):
            qn = nd.left
            c = 1 if isinstance(qn, ast.Name) else ival(qn.right, m)
            terms.append((sign, c, ival(nd.right.args[0], m)))
        else:
            reject("PARSE", ast.dump(nd))
    collect(node, 1)
    for _, _, x in terms:
        if x < 1:
            reject("BRACKET", f"[{x}]")
    if F.d == 1:
        return (flint.fmpq_poly([sum(sg * x for sg, _, x in terms)]), 0)
    # numerator sum_j sign_j w^{c_j} (e^{c_j eps} - w^{x_j} e^{(c_j + x_j) eps}); denominator 1 - w e^eps
    for k in range(0, 4):
        co = flint.fmpq_poly([0])
        for sg, c, x in terms:
            co += sg * (F.w(c) * flint.fmpq(c ** k, math.factorial(k)) -
                        F.w(c + x) * flint.fmpq((c + x) ** k, math.factorial(k)))
        co %= F.phi
        if co != 0:
            return ((co * F.inv(flint.fmpq_poly([1]) - F.w(1))) % F.phi, k)
    reject("ORDER", "sum vanishes to order > 3")


ASTS = {L: toks(r["f"]) for L, r in rows.items()}


def slope(node):
    vals = []
    for x in (0, 1, 2):
        v = ival(node, x)
        if not isinstance(v, int):
            reject("SHAPE", "non-integer exponent or bracket")
        vals.append(v)
    if vals[2] - vals[1] != vals[1] - vals[0]:
        reject("SHAPE", "non-linear exponent or bracket")
    return vals[1] - vals[0]


def audit(node, side):
    """count (numerator m-brackets, denominator constant brackets); enforce the shape"""
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Mult):
        a, b = audit(node.left, side), audit(node.right, side)
        return a[0] + b[0], a[1] + b[1]
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Div):
        a, b = audit(node.left, side), audit(node.right, -side)
        return a[0] + b[0], a[1] + b[1]
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Pow):
        if isinstance(node.left, ast.Name) and node.left.id == "q":
            slope(node.right)
            return 0, 0
        if isinstance(node.left, ast.Call) and side < 0 and slope(node.left.args[0]) == 0:
            return 0, ival(node.right, 0)
        reject("SHAPE", "power of something other than q or a constant bracket")
    if isinstance(node, ast.Name) and node.id == "q":
        return 0, 0
    if isinstance(node, ast.Call):
        sl = slope(node.args[0])
        if side > 0 and sl == 1:
            return 1, 0
        if side < 0 and sl == 0:
            return 0, 1
        reject("SHAPE", "bracket of the wrong kind on this side")
    if isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Add, ast.Sub)) and side > 0:
        lead(node, 1001, K(2))  # parses as a sum of q^c-weighted brackets or rejects
        for sub in ast.walk(node):
            if isinstance(sub, ast.Call) and slope(sub.args[0]) != 1:
                reject("SHAPE", "constant bracket inside a sum")
        return 1, 0
    reject("SHAPE", ast.dump(node)[:100])


def top_factors(node):
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Mult):
        return top_factors(node.left) + top_factors(node.right)
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Div):
        return top_factors(node.left)
    return [node]


for L, a in ASTS.items():
    if rows[L]["os_exponents"] and not any(isinstance(x, ast.Call) and slope(x.args[0]) == 1
                                           and ival(x.args[0], 0) == -1 for x in top_factors(a)):
        reject("M1_FACTOR", L)
for L, a in ASTS.items():
    nb, db = audit(a, 1)
    if nb > n or db > n:
        reject("DEGREE", f"{L}: {nb} numerator, {db} denominator brackets")


def rhs(L, s, d):
    m = s * h + 1
    F = K(d)
    v, order = lead(ASTS[L], m, F)
    if order < 0:
        reject("POLE", f"{L} m={m} d={d}")
    if order > 0:
        return 0
    if v.degree() > 0:
        reject("NOT_RATIONAL", f"{L} m={m} d={d}")
    x = v[0] if v.degree() == 0 else flint.fmpq(0)
    if x.q != 1 or x < 0:
        reject("NOT_NATURAL", f"{L} m={m} d={d}: {x}")
    return int(x.p)


# ---- left side ----
def block_exponents(h1, nu):
    """iterate rho^{h1} on symbolic entries (position, exponent) for s = nu"""
    t = [(i, 0) for i in range(nu)]
    for _ in range(h1):
        j, e = t[-1]
        t = [(j, e + 1)] + t[:-1]
    # fixed point: w_i = c^{e} w_{j} c^{-e} with (j, e) = t[i]; solve from position 0
    ex = {0: 0}
    changed = True
    while changed:
        changed = False
        for i, (j, e) in enumerate(t):
            if j in ex and i not in ex:
                ex[i] = ex[j] + e
                changed = True
    if len(ex) != nu:
        reject("CYCLE", "blocks not on one cycle")
    return [ex[i] for i in range(nu)]


def cpow(e):
    p = np.arange(N)
    for _ in range(e % h):
        p = conj[p]
    return p


certred = {(x["h1"], x["nu"]): x for x in cert["reduction"]}
done = set()
for h1 in [x for x in range(1, h + 1) if h % x == 0]:
    ch1 = ident
    for _ in range(h1):
        ch1 = ch1[cp]
    inC = np.array([(nc[u][ch1] == ch1[nc[u]]).all() for u in range(N)])
    msk = inC[pz] & inC[pu] & (pz != pu)
    az, au = pz[msk], pu[msk]
    ck = [np.zeros(N, dtype=object)]
    ck[0][e_id] = 1
    for _ in range(n):
        nx = np.zeros(N, dtype=object)
        np.add.at(nx, au, ck[-1][az])
        ck.append(nx)
    for nu in range(1, n + 1):
        if gcd(h1, nu) != 1:
            continue
        done.add((h1, nu))
        ex = block_exponents(h1, nu)
        ps = [cpow(e) for e in ex]
        poly = {}
        for u in np.nonzero(inC)[0]:
            P = ident
            for p in ps:
                P = P[nc[p[u]]]
            w0 = cp[inv(P)]
            if (n - fixdim(w0)) + nu * rank[u] != n:
                continue
            j = idx.get(w0.tobytes())
            if j is None:
                reject("W0", "not in NC")
            co = poly.setdefault(label[j], [0] * (n + 1))
            for kk in range(n + 1):
                co[kk] += int(ck[kk][u])
        ce = certred.get((h1, nu))
        if ce is None:
            reject("COVER", f"missing ({h1}, {nu})")
        if {L: v for L, v in ce["binomial_coeffs"].items() if any(v)} != {L: v for L, v in poly.items() if any(v)}:
            reject("LHS", f"({h1}, {nu})")
        for m1 in range(1, n + 3):
            for L in rows:
                lhs = sum(cf * comb(m1, kk) for kk, cf in enumerate(poly.get(L, [0])))
                if lhs != rhs(L, m1 * nu, nu * (h // h1)):
                    reject("IDENTITY", f"{L} ({h1}, {nu}, {m1})")
if done != set(certred):
    reject("COVER", "(h1, nu) sets differ")

# ---- large nu ----
regular = [L for L, r in rows.items() if not r["os_exponents"]][0]
maxden = max(int(x) for r in rows.values() for x in re.findall(r"B\((\d+)\)", r["f"]))
if maxden != cert["max_denominator"]:
    reject("LARGE", "max denominator")
for x in cert["large_m2"]:
    for m1 in range(1, n + 3):
        for L in rows:
            if rhs(L, m1 * x["nu"], x["d"]) != (L == regular):
                reject("LARGE", f"{L} {x}")
want = {(h1, nu) for h1 in range(1, h + 1) if h % h1 == 0 for nu in range(n + 1, maxden + 1)
        if gcd(h1, nu) == 1 and nu * (h // h1) <= maxden}
if want != {(x["h1"], x["nu"]) for x in cert["large_m2"]}:
    reject("COVER", "large-nu set")

# ---- brute force with the literal action ----
def phi(t):
    w0, ws = t[0], t[1:]
    cw = cp[ws[-1]][cinv]
    v = cw[w0][inv(cw)]
    return (v,) + (cw,) + tuple(ws[:-1])


chains = [[x] for x in range(N)]
brute = {(b[0], b[1], b[3]): b[4] for b in cert["brute_small_s"]}
for s in range(1, BRUTE + 1):
    if s > 1:
        up = [[] for _ in range(N)]
        for a, b in zip(pz, pu):
            up[a].append(b)
        chains = [ch + [b] for ch in chains for b in up[ch[-1]]]
    tuples = []
    for ch in chains:
        pis = [nc[x] for x in ch] + [cp]
        delta = [pis[0]] + [inv(pis[i])[pis[i + 1]] for i in range(s)]
        tuples.append(tuple(d.tobytes() for d in delta))
    for p in range(1, s * h + 1):
        if (s * h) % p:
            continue
        counts = {L: 0 for L in rows}
        for ch, tp in zip(chains, tuples):
            t = tuple(np.frombuffer(x, dtype=cp.dtype) for x in tp)
            for _ in range(p):
                t = phi(t)
            if tuple(x.tobytes() for x in t) == tp:
                counts[label[ch[0]]] += 1
        for L in rows:
            if brute.get((s, p, L)) != counts[L] or counts[L] != rhs(L, s, s * h // p):
                reject("BRUTE", f"s={s} p={p} {L}: {counts[L]}")
# ---- brute force by the twisted rotation on (w1, ..., ws), vectorised, up to the certificate's s ----
SROT = max(b[0] for b in cert["brute_small_s"])
up_s = np.argsort(pz, kind="stable")
zs_s, us_s = pz[up_s], pu[up_s]
st = np.searchsorted(zs_s, np.arange(N + 1))
labarr = np.array([label[w] for w in range(N)])
qcache = {}


def q_idx(a, b):
    k = (a, b)
    if k not in qcache:
        qcache[k] = idx[inv(nc[a])[nc[b]].tobytes()]
    return qcache[k]


cidx = idx[cp.tobytes()]
ch = np.arange(N).reshape(-1, 1)
for s in range(1, SROT + 1):
    if s > 1:
        last = ch[:, -1]
        cnt = st[last + 1] - st[last]
        ch = np.hstack([np.repeat(ch, cnt, axis=0), np.concatenate([us_s[st[a]:st[a + 1]] for a in last]).reshape(-1, 1)])
    ws = np.array([[q_idx(int(r[i]), int(r[i + 1]) if i + 1 < s else cidx) for r in ch] for i in range(s)])
    for p in [x for x in range(1, s * h + 1) if (s * h) % x == 0]:
        cur = ws
        for _ in range(p):
            cur = np.vstack([conj[cur[-1]][None], cur[:-1]])
        fx = (cur == ws).all(axis=0)
        for L in rows:
            c = int((fx & (labarr[ch[:, 0]] == L)).sum())
            if brute.get((s, p, L)) != c or c != rhs(L, s, s * h // p):
                reject("BRUTE_ROT", f"s={s} p={p} {L}: {c}")
if {(b[0], b[1], b[3]) for b in cert["brute_small_s"]} != {(s, p, L) for s in range(1, SROT + 1)
                                                           for p in range(1, s * h + 1) if (s * h) % p == 0 for L in rows}:
    reject("BRUTE_ROT", "certificate brute-force table incomplete")
print(json.dumps({"type": typ, "status": "ACCEPT", "nc": N, "classes": len(rows),
                  "pairs_h1_m2": len(done), "large_m2": len(want), "brute_s_literal": BRUTE, "brute_s_rotation": SROT}))
