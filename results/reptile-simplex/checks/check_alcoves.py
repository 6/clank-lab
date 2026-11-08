"""Third check of certificate.json, by the alcove structure (exact rationals).

For each of the 48 roots alpha of F4 (Bourbaki: +-e_i, (+-1,+-1,+-1,+-1)/2,
+-e_i +- e_j), the affine F4 arrangement has the hyperplanes <alpha,x> = n,
n an integer. A closed simplex is one alcove when, for every root, the values
<alpha,v> over its vertices lie in one interval [n, n+1]. This checks that
S and the four pieces are alcoves (alcoves are congruent to each other under
the affine Weyl group), that the pieces are pairwise distinct (distinct
alcoves have disjoint interiors), that phi^T phi = 2I (phi(S) is similar to
S), that every piece vertex lies in phi(S), and that vol(phi(S)) = 4 vol(S),
so the four distinct alcoves fill phi(S). It ignores the M, t and separator
fields.
"""
import itertools, json, sys
from fractions import Fraction as F


def roots():
    out = []
    for i in range(4):
        for s in (1, -1):
            v = [0] * 4; v[i] = s; out.append(tuple(map(F, v)))
    for signs in itertools.product((1, -1), repeat=4):
        out.append(tuple(F(s, 2) for s in signs))
    for i, j in itertools.combinations(range(4), 2):
        for si, sj in itertools.product((1, -1), repeat=2):
            v = [0] * 4; v[i] = si; v[j] = sj; out.append(tuple(map(F, v)))
    assert len(out) == 48
    return out


def is_alcove(V, R):
    cell = []
    for a in R:
        vals = [sum(x * y for x, y in zip(a, v)) for v in V]
        lo = min(vals)
        n = lo.numerator // lo.denominator  # floor
        if max(vals) > n + 1:
            return None
        cell.append(n)  # all values lie in [n, n+1]
    return tuple(cell)


def det(m):
    m = [list(r) for r in m]; s = F(1)
    for c in range(4):
        p = next((r for r in range(c, 4) if m[r][c] != 0), None)
        if p is None:
            return F(0)
        if p != c:
            m[c], m[p] = m[p], m[c]; s = -s
        s *= m[c][c]
        for r in range(c + 1, 4):
            f = m[r][c] / m[c][c]
            m[r] = [x - f * y for x, y in zip(m[r], m[c])]
    return s


def vol(V):
    return abs(det([[v[j] - V[0][j] for j in range(4)] for v in V[1:]]))


def main(path):
    c = json.load(open(path))
    rd = lambda rows: [tuple(F(x) for x in r) for r in rows]
    R = roots()
    S, phi = rd(c["S"]), rd(c["phi"])
    for i in range(4):
        for j in range(4):
            if sum(phi[k][i] * phi[k][j] for k in range(4)) != (2 if i == j else 0):
                print("REJECT: phi^T phi != 2I"); sys.exit(1)
    if is_alcove(S, R) is None or vol(S) == 0:
        print("REJECT: S is not an F4 alcove"); sys.exit(1)
    T = [tuple(sum(phi[r][k] * v[k] for k in range(4)) for r in range(4)) for v in S]
    if vol(T) != 4 * vol(S):
        print("REJECT: vol(phi S) != 4 vol(S)"); sys.exit(1)
    # T's facets: each piece vertex must be a convex combination of T's vertices.
    cells = set()
    for n, p in enumerate(c["pieces"]):
        V = rd(p["vertices"])
        cell = is_alcove(V, R)
        if cell is None or vol(V) != vol(S):
            print("REJECT: piece %d is not an F4 alcove" % n); sys.exit(1)
        # an alcove is determined by its vertex set
        key = frozenset(V)
        if key in cells:
            print("REJECT: piece %d repeats an alcove" % n); sys.exit(1)
        cells.add(key)
        for v in V:
            for i in range(5):
                repl = list(T); repl[i] = v
                sgn = det([[w[j] - repl[0][j] for j in range(4)] for w in repl[1:]])
                ref = det([[w[j] - T[0][j] for j in range(4)] for w in T[1:]])
                if sgn * ref < 0:
                    print("REJECT: piece %d vertex outside phi(S)" % n); sys.exit(1)
    if len(cells) != 4:
        print("REJECT: expected 4 pieces"); sys.exit(1)
    print("ACCEPT: S and the 4 pieces are distinct F4 alcoves inside phi(S), and vol(phi S) = 4 vol(S)")


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "certificate.json")
