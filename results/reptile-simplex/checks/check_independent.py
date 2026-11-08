#!/usr/bin/env python3
"""Independent checker for the claim that S is a 4-reptile simplex (Theorem 1 of the paper).

Usage: python3 -I check_independent.py certificate.json

Decides, in exact rational arithmetic only, that T = phi(S) is the union of
the four certificate pieces, each congruent to S, with pairwise disjoint
interiors, phi being sqrt(2) times an orthogonal map. The certificate's
"separators" field is ignored.

Method:
  1. S and phi must equal the simplex and map stated in the paper (S as a
     vertex set, in any order); S nondegenerate; phi^T phi = 2I.
  2. T = phi(S) is put in halfspace form a.x <= b (one inequality per facet,
     normal from 3x3 cofactors, oriented by the opposite vertex).
  3. Congruence: for each piece, the 10 pairwise squared distances among its
     vertices equal those of S under the listed vertex correspondence; and
     separately M^T M = I and M s_k + t = v_k for every vertex k.
  4. Containment: every piece vertex satisfies all 5 facet inequalities of T.
  5. Interior disjointness of each pair (A, B): both in halfspace form; the
     polytope P = A n B is enumerated exactly (every 4 of the 10 inequalities
     made tight, solved, kept if feasible). P is bounded, so P is the convex
     hull of these vertices; int A n int B = int P is empty iff the vertex set
     has affine rank < 4 (or is empty).
  6. Coverage: the pieces are closed, lie in T and have pairwise disjoint
     interiors, so vol(union) = sum of volumes; if that equals vol(T), then
     T minus the union is relatively open in the full-dimensional convex T
     and of measure zero, hence empty. Volume = |det(edges)| / 24.
"""
import itertools
import json
import sys
from fractions import Fraction

D = 4
N_PIECES = 4

CLAIM_S = [
    ("0", "0", "0", "0"),
    ("1", "0", "0", "0"),
    ("1/2", "1/2", "0", "0"),
    ("2/3", "1/3", "1/3", "0"),
    ("3/4", "1/4", "1/4", "1/4"),
]
CLAIM_PHI = [
    ("1", "1", "0", "0"),
    ("1", "-1", "0", "0"),
    ("0", "0", "1", "1"),
    ("0", "0", "1", "-1"),
]


class Reject(Exception):
    pass


def fr(x):
    if isinstance(x, bool) or not isinstance(x, (str, int)):
        raise Reject("non-exact number %r (strings or integers required)" % (x,))
    try:
        return Fraction(x)
    except (ValueError, ZeroDivisionError) as e:
        raise Reject("unparsable number %r: %s" % (x, e))


def vec(x, n, what):
    if not isinstance(x, list) or len(x) != n:
        raise Reject("%s: expected a list of %d numbers" % (what, n))
    return tuple(fr(c) for c in x)


def mat(x, rows, cols, what):
    if not isinstance(x, list) or len(x) != rows:
        raise Reject("%s: expected %d rows" % (what, rows))
    return [vec(r, cols, "%s row %d" % (what, i)) for i, r in enumerate(x)]


def det(m):
    m = [list(r) for r in m]
    n = len(m)
    d = Fraction(1)
    for c in range(n):
        p = next((r for r in range(c, n) if m[r][c] != 0), None)
        if p is None:
            return Fraction(0)
        if p != c:
            m[c], m[p] = m[p], m[c]
            d = -d
        d *= m[c][c]
        for r in range(c + 1, n):
            f = m[r][c] / m[c][c]
            if f:
                for k in range(c, n):
                    m[r][k] -= f * m[c][k]
    return d


def solve(a, b):
    """Solve square a x = b exactly; None if singular."""
    n = len(a)
    m = [list(a[i]) + [b[i]] for i in range(n)]
    for c in range(n):
        p = next((r for r in range(c, n) if m[r][c] != 0), None)
        if p is None:
            return None
        m[c], m[p] = m[p], m[c]
        piv = m[c][c]
        m[c] = [v / piv for v in m[c]]
        for r in range(n):
            if r != c and m[r][c] != 0:
                f = m[r][c]
                m[r] = [m[r][k] - f * m[c][k] for k in range(n + 1)]
    return tuple(m[i][n] for i in range(n))


def rank(rows):
    m = [list(r) for r in rows]
    if not m:
        return 0
    rk, ncol = 0, len(m[0])
    for c in range(ncol):
        p = next((r for r in range(rk, len(m)) if m[r][c] != 0), None)
        if p is None:
            continue
        m[rk], m[p] = m[p], m[rk]
        for r in range(len(m)):
            if r != rk and m[r][c] != 0:
                f = m[r][c] / m[rk][c]
                m[r] = [m[r][k] - f * m[rk][k] for k in range(ncol)]
        rk += 1
    return rk


def sub(u, v):
    return tuple(a - b for a, b in zip(u, v))


def dot(u, v):
    return sum((a * b for a, b in zip(u, v)), Fraction(0))


def matvec(m, v):
    return tuple(dot(r, v) for r in m)


def transpose_times(m):
    return [[sum((m[k][i] * m[k][j] for k in range(D)), Fraction(0))
             for j in range(D)] for i in range(D)]


def signed_vol6(verts):
    """det of edge vectors (24 * signed volume)."""
    return det([sub(v, verts[0]) for v in verts[1:]])


def halfspaces(verts, what):
    """Facet inequalities a.x <= b of a nondegenerate 4-simplex."""
    hs = []
    for j in range(D + 1):
        face = [verts[k] for k in range(D + 1) if k != j]
        rows = [sub(face[k], face[0]) for k in range(1, D)]  # 3 x 4
        a = []
        for i in range(D):
            minor = [[r[c] for c in range(D) if c != i] for r in rows]
            a.append((-1) ** i * det(minor))
        a = tuple(a)
        b = dot(a, face[0])
        for p in face:
            if dot(a, p) != b:
                raise Reject("%s: internal facet computation failed" % what)
        s = dot(a, verts[j])
        if s == b:
            raise Reject("%s: degenerate (vertex %d on opposite facet)" % (what, j))
        if s > b:
            a, b = tuple(-c for c in a), -b
        hs.append((a, b))
    return hs


def intersection_dim(hs):
    """Dimension of the bounded polytope {x : a.x <= b for (a,b) in hs};
    -1 if empty. Exact vertex enumeration plus affine rank."""
    verts = set()
    for combo in itertools.combinations(hs, D):
        x = solve([a for a, _ in combo], [b for _, b in combo])
        if x is None:
            continue
        if all(dot(a, x) <= b for a, b in hs):
            verts.add(x)
    if not verts:
        return -1, 0
    vl = sorted(verts)
    return rank([sub(v, vl[0]) for v in vl[1:]]), len(vl)


def check(cert):
    if not isinstance(cert, dict):
        raise Reject("certificate is not a JSON object")
    for key in ("S", "phi", "pieces"):
        if key not in cert:
            raise Reject("missing field %r" % key)

    # 1. S and phi as in the paper
    S = [tuple(v) for v in mat(cert["S"], D + 1, D, "S")]
    claim_S = [tuple(Fraction(c) for c in v) for v in CLAIM_S]
    if sorted(S) != sorted(claim_S):
        raise Reject("S is not the simplex stated in the paper")
    vS = signed_vol6(S)
    if vS == 0:
        raise Reject("S is degenerate")
    phi = mat(cert["phi"], D, D, "phi")
    if phi != [tuple(Fraction(c) for c in r) for r in CLAIM_PHI]:
        raise Reject("phi is not the map stated in the paper")
    ptp = transpose_times(phi)
    for i in range(D):
        for j in range(D):
            if ptp[i][j] != (2 if i == j else 0):
                raise Reject("phi^T phi != 2I (entry %d,%d = %s)" % (i, j, ptp[i][j]))

    # 2. T = phi(S) in halfspace form
    T = [matvec(phi, v) for v in S]
    hT = halfspaces(T, "T")
    vT = abs(signed_vol6(T))
    if vT != 4 * abs(vS):
        raise Reject("vol(T) != 4 vol(S)")

    # 3. pieces: congruence
    pieces = cert["pieces"]
    if not isinstance(pieces, list) or len(pieces) != N_PIECES:
        raise Reject("expected exactly %d pieces" % N_PIECES)
    dS = {(i, j): dot(sub(S[i], S[j]), sub(S[i], S[j]))
          for i in range(D + 1) for j in range(i + 1, D + 1)}
    P, mirrors = [], 0
    for n, pc in enumerate(pieces):
        if not isinstance(pc, dict):
            raise Reject("piece %d is not an object" % n)
        for key in ("M", "t", "vertices"):
            if key not in pc:
                raise Reject("piece %d: missing field %r" % (n, key))
        V = [tuple(v) for v in mat(pc["vertices"], D + 1, D, "piece %d vertices" % n)]
        for (i, j), d in dS.items():
            dv = dot(sub(V[i], V[j]), sub(V[i], V[j]))
            if dv != d:
                raise Reject("piece %d: |v%d-v%d|^2 = %s but S has %s (not congruent)"
                             % (n, i, j, dv, d))
        M = mat(pc["M"], D, D, "piece %d M" % n)
        t = vec(pc["t"], D, "piece %d t" % n)
        mtm = transpose_times(M)
        for i in range(D):
            for j in range(D):
                if mtm[i][j] != (1 if i == j else 0):
                    raise Reject("piece %d: M not orthogonal (M^T M[%d][%d] = %s)"
                                 % (n, i, j, mtm[i][j]))
        for k in range(D + 1):
            img = tuple(a + b for a, b in zip(matvec(M, S[k]), t))
            if img != V[k]:
                raise Reject("piece %d: M s%d + t != v%d" % (n, k, k))
        if det(M) < 0:
            mirrors += 1
        if signed_vol6(V) == 0:
            raise Reject("piece %d degenerate" % n)
        # 4. containment in T
        for k, v in enumerate(V):
            for f, (a, b) in enumerate(hT):
                if dot(a, v) > b:
                    raise Reject("piece %d vertex %d violates facet %d of T" % (n, k, f))
        P.append(V)

    # 5. pairwise interior disjointness
    H = [halfspaces(V, "piece %d" % n) for n, V in enumerate(P)]
    dims = []
    for i, j in itertools.combinations(range(N_PIECES), 2):
        dim, nv = intersection_dim(H[i] + H[j])
        if dim >= D:
            raise Reject("pieces %d and %d have overlapping interiors "
                         "(intersection is 4-dimensional, %d vertices)" % (i, j, nv))
        dims.append(dim)

    # 6. coverage by volume
    tot = sum((abs(signed_vol6(V)) for V in P), Fraction(0))
    if tot != vT:
        raise Reject("piece volumes sum to %s, vol(T) = %s" % (tot / 24, vT / 24))

    return ("vol(S) = %s, phi^T phi = 2I, vol(T) = %s; 4 pieces congruent to S "
            "(%d mirror), inside T, pairwise intersections of dimension %s, "
            "volumes sum to vol(T)"
            % (abs(vS) / 24, vT / 24, mirrors, max(dims)))


def main():
    if len(sys.argv) != 2:
        print("REJECT: usage: check_independent.py certificate.json")
        return 1
    try:
        with open(sys.argv[1]) as fh:
            cert = json.load(fh)
        summary = check(cert)
    except Reject as e:
        print("REJECT: %s" % e)
        return 1
    except (OSError, ValueError, TypeError, KeyError, IndexError, RecursionError) as e:
        print("REJECT: malformed input: %s: %s" % (type(e).__name__, e))
        return 1
    print("ACCEPT: %s" % summary)
    return 0


if __name__ == "__main__":
    sys.exit(main())
