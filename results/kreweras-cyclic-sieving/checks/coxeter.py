"""The two facts about the Coxeter element that the Lean statement takes as hypotheses
(lean/Main.lean, conjecture_1_4: hch and the identification ell(c) = n):
c = s_1 ... s_n has order exactly h, and ell(c) = rank(c - 1) = n.

Builds the simple reflections from the symmetrised Cartan matrices (Bourbaki numbering), as
checker A does, but imports nothing from the checkers or the search program.

usage: python3 -I coxeter.py     (exit 0 = all five types pass)"""
import json
import sys

import flint

H = {"G2": (2, 6), "F4": (4, 12), "E6": (6, 12), "E7": (7, 18), "E8": (8, 30)}


def gram(typ, n):
    if typ == "G2":
        return [[2, -3], [-3, 6]]
    if typ == "F4":
        return [[4, -2, 0, 0], [-2, 4, -2, 0], [0, -2, 2, -1], [0, 0, -1, 2]]
    g = [[2 if i == j else 0 for j in range(n)] for i in range(n)]
    for a, b in [(1, 3), (3, 4), (4, 5), (5, 6), (6, 7), (7, 8), (2, 4)]:
        if b <= n:
            g[a - 1][b - 1] = g[b - 1][a - 1] = -1
    return g


def simple(g, n, i):
    # s_i(e_j) = e_j - (2 (a_i, a_j) / (a_i, a_i)) e_i, as a matrix acting on columns
    m = [[1 if r == col else 0 for col in range(n)] for r in range(n)]
    for j in range(n):
        k = 2 * g[i][j]
        assert k % g[i][i] == 0
        m[i][j] -= k // g[i][i]
    return flint.fmpz_mat(m)


ok = True
for typ, (n, h) in H.items():
    g = gram(typ, n)
    c = flint.fmpz_mat([[1 if r == col else 0 for col in range(n)] for r in range(n)])
    for i in range(n):
        c = c * simple(g, n, i)
    one = flint.fmpz_mat([[1 if r == col else 0 for col in range(n)] for r in range(n)])
    p, order = one, None
    for k in range(1, h + 1):
        p = p * c
        if p == one:
            order = k
            break
    rank = (c - one).rank()
    good = order == h and rank == n
    ok &= good
    print(json.dumps({"type": typ, "order_of_c": order, "h": h, "rank_c_minus_1": rank, "n": n,
                      "status": "ACCEPT" if good else "REJECT"}))
sys.exit(0 if ok else 1)
