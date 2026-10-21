# Second construction: standard polytabloid basis, coordinates by exact rational solve, sympy SNF.
import sys, sympy
from sympy.matrices.normalforms import smith_normal_form
sys.dont_write_bytecode = True  # write nothing into this folder
import specht_lattice as S


def run(lam, k):
    n = sum(lam); idx = S.tabloid_index(lam); keys = {i: t for t, i in idx.items()}
    E = [S.polytabloid(lam, T, idx) for T in S.syt(lam)]
    M = sympy.Matrix(E).T  # columns = standard polytabloids
    G = M.T * M
    rows = []
    for e in E:
        w = [0] * len(e)
        for i in range(k - 1):
            u = S.act(S.transposition(n, i, k - 1), e, idx, keys); w = [a + b for a, b in zip(w, u)]
        c = G.LUsolve(M.T * sympy.Matrix(w))
        assert M * c == sympy.Matrix(w) and all(x.is_integer for x in c)
        rows.append([int(x) for x in c])
    A = sympy.Matrix(rows)
    D = smith_normal_form(A, domain=sympy.ZZ)
    return S.normalize([abs(int(D[i, i])) for i in range(A.rows)])


if __name__ == "__main__":
    for lam, k in [((3, 1, 1), 3), ((3, 1, 1), 5), ((5, 1), 5), ((2, 2, 1), 3), ((4, 1), 3)]:
        print(lam, k, run(lam, k), 'pred', S.normalize(S.predicted(lam, k)[0]))


def compare_all(results_path, nmax):
    """Recompute every case with n <= nmax by this construction and compare with the census."""
    import json
    R = [r for r in json.load(open(results_path)) if r['lattice'] == 'specht' and r['n'] <= nmax]
    bad = [(r['lam'], r['k']) for r in R if run(tuple(r['lam']), r['k']) != r['snf']]
    print(f"standard-basis/sympy vs census, n <= {nmax}: {len(R)} cases, {len(bad)} differ {bad[:5]}")
