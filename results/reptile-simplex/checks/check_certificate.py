"""Check certificate.json: S is a 4-reptile 4-simplex.

Reads only the certificate (no search code). Exact rational arithmetic.
Verifies, for T = phi(S):
  1. S is a nondegenerate 4-simplex;
  2. phi^T phi = 2 I, so T is similar to S with ratio sqrt(2);
  3. each piece is M_i S + t_i with M_i^T M_i = I (congruent to S), and its
     listed vertices equal the images of S's vertices;
  4. every piece vertex lies in T (barycentric coordinates >= 0), so each
     piece lies in T;
  5. for each pair of pieces the listed hyperplane has one piece on each
     closed side, so interiors are disjoint;
  6. the piece volumes sum to vol(T).
Closed convex pieces inside T with disjoint interiors and total volume vol(T)
cover T, so phi^{-1} of the pieces tiles S by 4 mutually congruent simplices
similar to S. Exit 0 on success, 1 with a reason otherwise.
"""
import itertools, json, sys
from fractions import Fraction as F


def fail(msg):
    print("REJECT:", msg)
    sys.exit(1)


def det(m):
    m = [list(r) for r in m]
    n, s = len(m), F(1)
    for c in range(n):
        p = next((r for r in range(c, n) if m[r][c] != 0), None)
        if p is None:
            return F(0)
        if p != c:
            m[c], m[p] = m[p], m[c]
            s = -s
        s *= m[c][c]
        for r in range(c + 1, n):
            f = m[r][c] / m[c][c]
            m[r] = [x - f * y for x, y in zip(m[r], m[c])]
    return s


def vol6(simplex):
    """4! times the signed volume."""
    v0 = simplex[0]
    return det([[v[j] - v0[j] for j in range(4)] for v in simplex[1:]])


def bary(simplex, x):
    """Barycentric coordinates by Cramer's rule."""
    total = vol6(simplex)
    out = []
    for i in range(5):
        repl = list(simplex)
        repl[i] = x
        out.append(vol6(repl) / total)
    return out


def main(path):
    c = json.load(open(path))
    rd = lambda rows: [tuple(F(x) for x in r) for r in rows]
    S = rd(c["S"])
    phi = rd(c["phi"])
    if len(S) != 5 or any(len(v) != 4 for v in S):
        fail("S is not 5 points in R^4")
    vS = vol6(S)
    if vS == 0:
        fail("S is degenerate")
    for i in range(4):
        for j in range(4):
            g = sum(phi[k][i] * phi[k][j] for k in range(4))
            if g != (2 if i == j else 0):
                fail("phi^T phi != 2I at (%d,%d)" % (i, j))
    T = [tuple(sum(phi[r][k] * v[k] for k in range(4)) for r in range(4)) for v in S]
    vT = vol6(T)
    if abs(vT) != 4 * abs(vS):
        fail("vol(T) != 4 vol(S)")
    pieces = c["pieces"]
    if len(pieces) != 4:
        fail("expected 4 pieces, got %d" % len(pieces))
    P = []
    for n, p in enumerate(pieces):
        M, t, V = rd(p["M"]), tuple(F(x) for x in p["t"]), rd(p["vertices"])
        for i in range(4):
            for j in range(4):
                g = sum(M[k][i] * M[k][j] for k in range(4))
                if g != (1 if i == j else 0):
                    fail("piece %d: M not orthogonal" % n)
        img = [tuple(sum(M[r][k] * v[k] for k in range(4)) + t[r] for r in range(4)) for v in S]
        if img != V:
            fail("piece %d: vertices are not M S + t" % n)
        for v in V:
            if min(bary(T, v)) < 0:
                fail("piece %d: vertex %s outside T" % (n, [str(x) for x in v]))
        P.append(V)
    seen = set()
    for s in c["separators"]:
        i, j = s["pair"]
        nrm = tuple(F(x) for x in s["normal"])
        k = F(s["offset"])
        if all(x == 0 for x in nrm):
            fail("zero separator normal")
        sign = 1 if s["side_of_first"] == "<=" else -1
        for v in P[i]:
            if sign * (sum(a * b for a, b in zip(nrm, v)) - k) > 0:
                fail("separator %d,%d: piece %d on wrong side" % (i, j, i))
        for v in P[j]:
            if sign * (sum(a * b for a, b in zip(nrm, v)) - k) < 0:
                fail("separator %d,%d: piece %d on wrong side" % (i, j, j))
        seen.add((min(i, j), max(i, j)))
    if seen != set(itertools.combinations(range(4), 2)):
        fail("separators do not cover every pair")
    total = sum(abs(vol6(V)) for V in P)
    if total != abs(vT):
        fail("piece volumes sum to %s, vol(T) is %s (times 4!)" % (total, abs(vT)))
    dets = [det(rd(p["M"])) for p in pieces]
    print("ACCEPT: S is a 4-reptile 4-simplex (k = 4 = 2^2, scale ratio 1/sqrt 2)")
    print("4!*vol(S) =", abs(vS), " 4!*vol(T) =", abs(vT), " det M_i =", [str(d) for d in dets])


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "certificate.json")
