#!/usr/bin/env python3
"""Checker A: rigorous check of mu(G) >= 6 certificates (exact rational arithmetic, python-flint fmpq).

Usage: checker_a.py CERT.json [CERT.json ...]
       checker_a.py --corrupt CERT.json      (runs the corruption suite)
Written independently of check_cert.py, from the certificate format description only.
"""
import sys, json, copy
from fractions import Fraction
from flint import fmpq, fmpq_mat
import numpy as np


class Reject(Exception):
    pass


def need(cond, msg):
    if not cond:
        raise Reject(msg)


def Q(s):
    """exact rational from 'p/q', integer or decimal string"""
    need(isinstance(s, str), "number not a string: %r" % (s,))
    f = Fraction(s.strip())
    return fmpq(f.numerator, f.denominator)


# ---------------------------------------------------------------- graph6
def parse_graph6(s):
    need(len(s) >= 1, "empty graph6")
    data = [ord(c) - 63 for c in s]
    need(all(0 <= d <= 63 for d in data), "graph6: invalid character")
    n = data[0]
    need(n <= 62, "graph6: only n<=62 supported")
    nbits = n * (n - 1) // 2
    nchars = (nbits + 5) // 6
    need(len(data) == 1 + nchars, "graph6: wrong length")
    bits = []
    for d in data[1:]:
        for k in range(5, -1, -1):
            bits.append((d >> k) & 1)
    need(all(b == 0 for b in bits[nbits:]), "graph6: nonzero padding bits")
    E = set()
    p = 0
    for j in range(1, n):
        for i in range(j):
            if bits[p]:
                E.add((i, j))
            p += 1
    return n, E


def adj(E, a, b):
    return (min(a, b), max(a, b)) in E


# ---------------------------------------------------------------- exact helpers
def mat(rows):
    r = len(rows); c = len(rows[0]) if r else 0
    return fmpq_mat(r, c, [x for row in rows for x in row])


def to_rows(M):
    return [[M[i, j] for j in range(M.ncols())] for i in range(M.nrows())]


def absm(rows):
    return [[abs(x) for x in row] for row in rows]


def mm(A, B):
    """product of row-lists"""
    return to_rows(mat(A) * mat(B))


def tr(A):
    return [list(r) for r in zip(*A)]


def addm(*Ms):
    return [[sum((M[i][j] for M in Ms), fmpq(0)) for j in range(len(Ms[0][0]))] for i in range(len(Ms[0]))]


def ldl_inertia(rows):
    """Inertia (pos, neg, zero) of an exact symmetric matrix by congruence (symmetric Gaussian elimination
    with diagonal pivoting and 2x2 blocks when the remaining diagonal is zero)."""
    A = [list(r) for r in rows]
    n = len(A)
    pos = neg = 0
    idx = list(range(n))
    while idx:
        piv = next((i for i in idx if A[i][i] != 0), None)
        if piv is not None:
            d = A[piv][piv]
            if d > 0: pos += 1
            else: neg += 1
            rest = [i for i in idx if i != piv]
            for i in rest:
                f = A[i][piv] / d
                if f != 0:
                    for j in rest:
                        A[i][j] -= f * A[piv][j]
            idx = rest
            continue
        pair = next(((i, j) for i in idx for j in idx if i < j and A[i][j] != 0), None)
        if pair is None:
            break  # remaining block is zero
        i, j = pair
        # replace row/col i by row/col i + row/col j: new diagonal = 2 A_ij != 0 (congruence)
        for k in idx:
            A[i][k] += A[j][k]
        for k in idx:
            A[k][i] += A[k][j]
    return pos, neg, n - pos - neg


def is_pos_def_exact(rows):
    """True iff the symmetric rational matrix is positive definite (all LDL pivots > 0, no pivoting)."""
    A = [list(r) for r in rows]
    n = len(A)
    for k in range(n):
        d = A[k][k]
        if d <= 0:
            return False
        for i in range(k + 1, n):
            f = A[i][k] / d
            if f != 0:
                for j in range(k + 1, n):
                    A[i][j] -= f * A[k][j]
    return True


def descartes_inertia(rows):
    """Inertia from the characteristic polynomial: real-rooted, so Descartes' rule is exact."""
    n = len(rows)
    c = mat(rows).charpoly().coeffs()  # low -> high
    c = [fmpq(x) for x in c]
    z = 0
    while z < len(c) and c[z] == 0:
        z += 1
    def changes(seq):
        s = [x for x in seq if x != 0]
        return sum(1 for a, b in zip(s, s[1:]) if (a > 0) != (b > 0))
    pos = changes(c[z:])
    neg = changes([x * (-1) ** k for k, x in enumerate(c)][z:])
    return pos, neg, z


def sigma_min_sq_lower(G_rows):
    """Rigorous rational t >= 0 with G - t I positive definite (so lambda_min(G) > t); 0 if none found."""
    n = len(G_rows)
    Gf = np.array([[float(x) for x in r] for r in G_rows])
    lam = float(np.linalg.eigvalsh(Gf)[0])
    if not lam > 0:
        return fmpq(0)
    for frac in (Fraction(1, 2), Fraction(1, 8), Fraction(1, 64)):
        tf = Fraction(lam).limit_denominator(10 ** 12) * frac
        t = fmpq(tf.numerator, tf.denominator)
        if t > 0 and is_pos_def_exact([[G_rows[i][j] - (t if i == j else 0) for j in range(n)] for i in range(n)]):
            return t
    return fmpq(0)


# ---------------------------------------------------------------- the check
def check(cert, log=print):
    n, E = parse_graph6(cert["graph6"])
    S = list(cert["S"]); T = list(cert["T"])
    log("graph6=%s n=%d m=%d" % (cert["graph6"], n, len(E)))
    need(all(isinstance(v, int) for v in S + T), "S/T entries not integers")
    need(len(S) == 6, "|S| != 6")
    need(sorted(S + T) == list(range(n)), "S,T is not a partition of 0..n-1")
    s, t = len(S), len(T)
    posS = {v: k for k, v in enumerate(S)}
    posT = {v: k for k, v in enumerate(T)}

    # --- C: exact, symmetric, sign pattern
    Cr = cert["C_rows_T_order"]
    need(len(Cr) == t and all(len(r) == t for r in Cr), "C has wrong shape")
    C = [[Q(x) for x in r] for r in Cr]
    for a in range(t):
        for b in range(t):
            need(C[a][b] == C[b][a], "C not symmetric at (%d,%d)" % (T[a], T[b]))
            if a != b:
                if adj(E, T[a], T[b]):
                    need(C[a][b] < 0, "C entry on edge %d-%d not < 0" % (T[a], T[b]))
                else:
                    need(C[a][b] == 0, "C entry on non-edge %d-%d not 0" % (T[a], T[b]))
    log("C: symmetric, pattern OK (%d edges inside T)" % sum(1 for a in range(t) for b in range(a + 1, t) if adj(E, T[a], T[b])))

    # --- inertia of C (two exact methods)
    in1 = ldl_inertia(C)
    in2 = descartes_inertia(C)
    log("inertia(C) (pos,neg,zero): LDL %s, charpoly/Descartes %s" % (in1, in2))
    need(in1 == in2, "inertia methods disagree")
    need(in1[1] == 1 and in1[2] == 0, "C must be nonsingular with exactly one negative eigenvalue")
    Cm = mat(C)
    D = to_rows(Cm.inv())

    # --- B: fixed entries, unknowns, zero elsewhere
    r = Q(str(cert["box_radius"]))
    need(r > 0, "box radius not positive")
    B0 = [[fmpq(0)] * t for _ in range(s)]
    seen = set()
    for key, val in cert["B_fixed"].items():
        i, tt = [int(x) for x in key.split(",")]
        need(i in posS and tt in posT, "B_fixed key %s not in S x T" % key)
        need((i, tt) not in seen, "duplicate B position %s" % key)
        seen.add((i, tt))
        v = Q(val)
        need(adj(E, i, tt), "B_fixed %s on a non-edge" % key)
        need(v < 0, "B_fixed %s not < 0" % key)
        B0[posS[i]][posT[tt]] = v
    unk = [tuple(int(x) for x in p) for p in cert["unknowns"]]
    um = [Q(x) for x in cert["u_mid"]]
    need(len(um) == len(unk), "u_mid length != number of unknowns")
    for k, (i, tt) in enumerate(unk):
        need(i in posS and tt in posT, "unknown %s not in S x T" % ((i, tt),))
        need((i, tt) not in seen, "duplicate B position %s" % ((i, tt),))
        seen.add((i, tt))
        need(adj(E, i, tt), "unknown %s on a non-edge" % ((i, tt),))
        need(um[k] + r < 0, "unknown %d not strictly negative over the box" % k)
    for i in S:
        for tt in T:
            if adj(E, i, tt):
                need((i, tt) in seen, "S-T edge %d-%d has no (nonzero) entry" % (i, tt))
    log("max over unknowns of (u_mid+r) = %.4f" % max(float(x + r) for x in um))
    log("B: %d fixed, %d unknowns, every S-T edge covered, all strictly negative over box" % (len(cert["B_fixed"]), len(unk)))

    # --- equations: one per non-adjacent pair in S
    pairs = [(a, b) for a in range(s) for b in range(a + 1, s) if not adj(E, S[a], S[b])]
    q = len(unk)
    need(len(pairs) == q, "number of non-adjacent S pairs (%d) != number of unknowns (%d)" % (len(pairs), q))
    log("square system: %d equations / unknowns" % q)

    def Bof(u):
        B = [list(row) for row in B0]
        for k, (i, tt) in enumerate(unk):
            B[posS[i]][posT[tt]] = u[k]
        return B

    Bm = Bof(um)
    DBt = mm(D, tr(Bm))           # t x s, = D B^T
    Am = mm(Bm, DBt)              # s x s
    Fm = [Am[a][b] for (a, b) in pairs]
    # Jacobian at um: dF_p/du_k
    J = [[fmpq(0)] * q for _ in range(q)]
    Hs = [[[fmpq(0)] * q for _ in range(q)] for _ in range(q)]  # constant Hessian
    for p, (a, b) in enumerate(pairs):
        for k, (i, tt) in enumerate(unk):
            ri, ct = posS[i], posT[tt]
            if ri == a:
                J[p][k] += DBt[ct][b]
            if ri == b:
                J[p][k] += DBt[ct][a]
            for l, (i2, t2) in enumerate(unk):
                ri2, ct2 = posS[i2], posT[t2]
                if (ri == a and ri2 == b) or (ri == b and ri2 == a):
                    Hs[p][k][l] += D[ct][ct2]
    # Delta_{pk} = sum_l |H_pkl| r bounds |J(u)-J(um)| over the box
    Delta = [[sum((abs(Hs[p][k][l]) for l in range(q)), fmpq(0)) * r for k in range(q)] for p in range(q)]
    Jm = mat(J)
    need(Jm.det() != 0, "Jacobian at midpoint singular")
    Y = to_rows(Jm.inv())          # exact inverse, so I - Y J(um) = 0
    YF = mm(Y, [[x] for x in Fm])
    YD = mm(absm(Y), Delta)
    worst = fmpq(0)
    for k in range(q):
        lhs = abs(YF[k][0]) + sum(YD[k], fmpq(0)) * r
        need(lhs < r, "Krawczyk inclusion fails in coordinate %d" % k)
        worst = max(worst, lhs / r)
    maxF = max(abs(x) for x in Fm)
    log("Krawczyk (exact rational): max|F(mid)|=%.3e, max_k |K-mid|_k/r = %.3e < 1 -> unique zero u* in box" % (float(maxF), float(worst)))

    # --- A signs over the box
    R = [[fmpq(0)] * t for _ in range(s)]
    for (i, tt) in unk:
        R[posS[i]][posT[tt]] = r
    aD = absm(D); aB = absm(Bm)
    dA = addm(mm(mm(R, aD), tr(aB)), mm(mm(aB, aD), tr(R)), mm(mm(R, aD), tr(R)))  # |A(u)-A(um)| <= dA
    nedgeS = 0; amax = None
    for a in range(s):
        for b in range(a + 1, s):
            if adj(E, S[a], S[b]):
                nedgeS += 1
                need(Am[a][b] + dA[a][b] < 0, "A entry on edge %d-%d not strictly negative over box" % (S[a], S[b]))
                amax = Am[a][b] + dA[a][b] if amax is None else max(amax, Am[a][b] + dA[a][b])
    log("A: %d edges inside S, all strictly negative over box (max upper bound %.4f); non-edges are 0 at u* by the equations" % (nedgeS, float(amax) if amax is not None else float('nan')))

    # --- inertia/corank of M*: congruence with diag(A - B C^-1 B^T = 0, C)
    log("M*: Schur complement 0 -> inertia = inertia(C) + 6 zeros = (%d,%d,%d); corank exactly 6" % (in1[0], in1[1], 6))

    # --- SAP, formulation 1 (kernel): K = [I; -D B^T], X = K Z K^T, Z in Sym_6
    order = S + T
    rowsK_m = [[fmpq(1) if a == b else fmpq(0) for b in range(s)] for a in range(s)] + [[-x for x in row] for row in DBt]
    dK = [[fmpq(0)] * s for _ in range(s)] + mm(aD, tr(R))  # |K(u)-K(um)| <= dK entrywise
    constr = [(v, v) for v in range(n)] + sorted(E)
    pos_ = {v: k for k, v in enumerate(order)}
    Zbasis = [(a, b) for a in range(s) for b in range(a, s)]
    Phi = []; dPhi = []
    for (x, y) in constr:
        i, j = pos_[x], pos_[y]
        row = []; drow = []
        for (a, b) in Zbasis:
            if a == b:
                terms = [(i, a, j, a)]
            else:
                terms = [(i, a, j, b), (i, b, j, a)]
            val = fmpq(0); dv = fmpq(0)
            for (p1, c1, p2, c2) in terms:
                k1, k2 = rowsK_m[p1][c1], rowsK_m[p2][c2]
                e1, e2 = dK[p1][c1], dK[p2][c2]
                val += k1 * k2
                dv += e1 * abs(k2) + abs(k1) * e2 + e1 * e2
            row.append(val); drow.append(dv)
        Phi.append(row); dPhi.append(drow)
    G1 = mm(tr(Phi), Phi)
    t1 = sigma_min_sq_lower(G1)
    pert1 = sum((x * x for row in dPhi for x in row), fmpq(0))
    need(t1 > 0 and pert1 < t1, "SAP (kernel form) not certified")
    log("SAP[kernel form]: Phi is %dx%d; sigma_min(Phi(mid))^2 > %.4e (exact LDL), ||Phi(u)-Phi(mid)||_F^2 <= %.3e" % (len(Phi), len(Zbasis), float(t1), float(pert1)))

    # --- SAP, formulation 2 (direct): X -> M X on symmetric X supported on non-edges
    Mm = [[fmpq(0)] * n for _ in range(n)]
    dM = [[fmpq(0)] * n for _ in range(n)]
    for a in range(s):
        for b in range(s):
            Mm[a][b] = Am[a][b]; dM[a][b] = dA[a][b]
        for c in range(t):
            Mm[a][s + c] = Mm[s + c][a] = Bm[a][c]
            dM[a][s + c] = dM[s + c][a] = R[a][c]
    for c in range(t):
        for d in range(t):
            Mm[s + c][s + d] = C[c][d]
    nonedges = [(x, y) for x in range(n) for y in range(x + 1, n) if not adj(E, x, y)]
    # column for X = E_ij + E_ji: MX has column j = M e_i, column i = M e_j
    L = []
    colsq = []
    for (x, y) in nonedges:
        i, j = pos_[x], pos_[y]
        col = [fmpq(0)] * (n * n)
        for k in range(n):
            col[k * n + j] += Mm[k][i]
            col[k * n + i] += Mm[k][j]
        L.append(col)
        colsq.append(sum((dM[k][i] ** 2 + dM[k][j] ** 2 for k in range(n)), fmpq(0)))
    G2 = mm(L, tr(L))
    t2 = sigma_min_sq_lower(G2)
    pert2 = sum(colsq, fmpq(0))
    need(t2 > 0 and pert2 < t2, "SAP (direct form) not certified")
    log("SAP[direct form]: map is %dx%d; sigma_min(L(mid))^2 > %.4e (exact LDL), ||L(u)-L(mid)||_F^2 <= %.3e" % (n * n, len(nonedges), float(t2), float(pert2)))
    log("RESULT: certificate VALID, mu >= 6")
    return True


def run(cert, quiet=False):
    lines = []
    try:
        check(cert, log=lines.append)
        ok, why = True, ""
    except Reject as e:
        ok, why = False, str(e)
    except Exception as e:  # malformed input is a rejection too
        ok, why = False, "exception: %r" % (e,)
    return ok, why, lines


def corruptions(cert):
    out = []
    # 1. C off-diagonal edge entry sign flip (both symmetric copies, and one copy only)
    Cr = cert["C_rows_T_order"]
    t = len(Cr)
    a, b = next((a, b) for a in range(t) for b in range(a + 1, t) if Q(Cr[a][b]) != 0)
    flip = lambda x: x[1:] if x.startswith("-") else "-" + x
    c1 = copy.deepcopy(cert); c1["C_rows_T_order"][a][b] = flip(Cr[a][b]); c1["C_rows_T_order"][b][a] = flip(Cr[b][a])
    out.append(("C[%d][%d] and C[%d][%d] sign flipped (T order)" % (a, b, b, a), c1))
    c2 = copy.deepcopy(cert); c2["C_rows_T_order"][a][b] = flip(Cr[a][b])
    out.append(("C[%d][%d] only sign flipped" % (a, b), c2))
    # 2. u_mid[0] shifted by 1e-30 (both directions)
    for sgn in ("+", "-"):
        c3 = copy.deepcopy(cert)
        f = Fraction(cert["u_mid"][0]) + (Fraction(1, 10 ** 30) if sgn == "+" else -Fraction(1, 10 ** 30))
        c3["u_mid"][0] = "%d/%d" % (f.numerator, f.denominator)
        out.append(("u_mid[0] %s 1e-30" % sgn, c3))
    # 3. every single bit of the graph6 string (all 6 bits of every character)
    g = cert["graph6"]
    for pos in range(len(g)):
        for bit in range(6):
            ch = chr(((ord(g[pos]) - 63) ^ (1 << bit)) + 63)
            c4 = copy.deepcopy(cert); c4["graph6"] = g[:pos] + ch + g[pos + 1:]
            out.append(("graph6 char %d bit %d -> %s" % (pos, bit, c4["graph6"]), c4))
    return out


def main():
    args = sys.argv[1:]
    if args and args[0] == "--corrupt":
        allok = True
        for path in args[1:]:
            cert = json.load(open(path))
            ok0, why0, _ = run(cert)
            print("== %s: original -> %s" % (path, "ACCEPT" if ok0 else "REJECT " + why0))
            nrej = 0; tot = 0
            for name, c in corruptions(cert):
                ok, why, _ = run(c)
                tot += 1
                if ok:
                    allok = False
                    print("  !! ACCEPTED corrupted: %s" % name)
                else:
                    nrej += 1
                    if True:
                        print("  rejected: %-45s | %s" % (name, why))
            print("  %d/%d corruptions rejected" % (nrej, tot))
            allok = allok and ok0
        print("CORRUPTION SUITE:", "PASS" if allok else "FAIL")
        return 0 if allok else 1
    rc = 0
    for path in args:
        cert = json.load(open(path))
        ok, why, lines = run(cert)
        print("== %s (%s)" % (path, cert.get("name")))
        for l in lines:
            print("  " + l)
        if not ok:
            print("  RESULT: REJECTED: " + why); rc = 1
    return rc


if __name__ == "__main__":
    sys.exit(main())
