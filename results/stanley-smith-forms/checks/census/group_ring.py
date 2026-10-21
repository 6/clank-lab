# Literal reading test: SNF of left multiplication by X_k on Z[S_n] versus the
# Smith form of the block-diagonal matrix with f^lambda copies of each predicted list.
import itertools, sys, flint
from collections import Counter
sys.dont_write_bytecode = True  # write nothing into this folder
import specht_lattice as S

def run(n, k):
    perms = list(itertools.permutations(range(n)))
    pos = {p: i for i, p in enumerate(perms)}
    N = len(perms)
    rows = [[0] * N for _ in range(N)]
    for g in perms:
        for i in range(k - 1):
            t = list(range(n)); t[i], t[k - 1] = k - 1, i
            h = tuple(t[g[x]] for x in range(n))  # t o g
            rows[pos[g]][pos[h]] += 1
    D = flint.fmpz_mat(rows).snf()
    got = Counter(abs(int(D[i, i])) for i in range(N))
    pred = Counter()
    for lam in S.partitions(n):
        p, _ = S.predicted(lam, k)
        f = len(p)
        for a in p:
            pred[a] += f
    # the SNF of a block-diagonal matrix is the Smith form of the diagonal of all block entries
    entries = [a for a, m in pred.items() for _ in range(m)]
    D2 = flint.fmpz_mat([[entries[i] if i == j else 0 for j in range(N)] for i in range(N)]).snf()
    pred = Counter(abs(int(D2[i, i])) for i in range(N))
    return got, pred

for n in range(2, int(sys.argv[1]) + 1):
    for k in range(1, n + 1):
        got, pred = run(n, k)
        print(n, k, "OK" if got == pred else "DIFF", dict(sorted(got.items())), dict(sorted(pred.items())), flush=True)
