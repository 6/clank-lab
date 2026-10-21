#!/usr/bin/env python3
"""Empirical test of the clause check's soundness (../README.md, lemma L5).

On small instances every admissible colouring can be listed, so a clause's
validity under the witness extension can be decided by brute force.  This
mutates clauses of the pinned command's formula (drop a literal, flip a
sign, replace a variable), asks the auditor's clause check, and requires
that every mutant it accepts is true for every admissible colouring.  It
also counts valid mutants the check rejects (it is allowed to be strict).

usage: soundness_fuzz.py [MUTANTS_PER_INSTANCE]
"""
import os
import random
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import audit as A  # noqa: E402


def main():
    per = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
    rng = random.Random(20261020)
    unsound = 0
    for n, m, k in [(4, 3, 0), (5, 4, 0), (5, 4, 2), (5, 4, 3)]:
        src = subprocess.run([sys.executable, os.path.join(A.CHECKS, 'encode.py'), str(n), str(m),
                              '--fix', str(k)], capture_output=True, text=True, check=True).stdout
        cls = [[int(t) for t in l.split()[:-1]] for l in src.splitlines() if l and l[0] not in 'cp']
        gens = A.stated_generators(n, k)
        enc = A.Encoding(n, k, gens)
        K = enc.K
        P = A.path_edges(K, k)
        exts = []
        for v in range(3 ** K.ne):
            X = A.decode(v, K.ne)
            if all(X[e] == 0 for e in P) and all(X <= A.act(K, g, X) for g in gens):
                val = {3 * e + c + 1: X[e] == c for e in range(K.ne) for c in range(3)}
                for a, (g, j) in enc.aux.items():
                    val[a] = all(X[f] == enc.sig[g][X[s]] for f, s in enc.comp[g][:j])
                exts.append(val)
        acc = strict = 0
        for _ in range(per):
            c = list(rng.choice(cls))
            op = rng.randrange(3)
            i = rng.randrange(len(c))
            if op == 0 and len(c) > 1:
                c.pop(i)
            elif op == 1:
                c[i] = -c[i]
            else:
                c[i] = rng.choice((1, -1)) * rng.randint(1, enc.nvars)
            truly = all(any(e[abs(l)] == (l > 0) for l in c) for e in exts)
            said = enc.valid(c, 2)
            if said and not truly:
                unsound += 1
                print(f'UNSOUND K_{n}, P_{m}, fixed P_{k}: accepted {c}')
            acc += said
            strict += truly and not said
        print(f'K_{n}, P_{m}, fixed P_{k}: {len(exts)} admissible colourings; {per} mutants, '
              f'{acc} accepted, all true for every admissible colouring; '
              f'{strict} valid mutants rejected (strict)')
    sys.exit(1 if unsound else 0)


if __name__ == '__main__':
    main()
