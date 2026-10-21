#!/usr/bin/env python3
"""DIMACS encoding: a 3-edge-colouring of K_n with no monochromatic P_m,
under the ladder symmetry reduction.  The path clauses themselves are NOT
in this file: the solver adds them lazily and logs each one, and
check_paths.py checks every logged clause independently.

Usage: encode.py n m [--fix k] [--nolex] > out.cnf

Variables: edges (i,j), i<j, in row-wise order (0,1),(0,2),...,(n-2,n-1),
edge index e; colour c in {0,1,2}; variable x(e,c) = 3e + c + 1.

Clauses:
  * exactly one colour per edge;
  * --fix k: edges (t,t+1), t = 0..k-2, have colour 0 (a colour-0 path on
    vertices 0..k-1).  Sound when R_3(P_k) <= n: every colouring of K_n
    then has a monochromatic P_k, and relabelling vertices and colours
    moves it there;
  * lex-leader constraints X <=lex g(X) for generators g of a group G that
    maps the set of colourings in the previous item to itself (the
    stabiliser of the fixed path: permutations of W = {k..n-1}, reversal
    of the path, swapping colours 1 and 2; without --fix, all vertex
    transpositions and colour transpositions).  For any such G, the
    lex-least member of each G-orbit satisfies every constraint at once,
    so the constraints keep a representative of every orbit.
"""
import sys, itertools

def main():
    a = sys.argv[1:]
    n, m = int(a[0]), int(a[1])
    fixk = int(a[a.index('--fix') + 1]) if '--fix' in a else 0
    lex = '--nolex' not in a
    E = list(itertools.combinations(range(n), 2))
    eid = {e: i for i, e in enumerate(E)}
    x = lambda e, c: 3 * eid[e] + c + 1
    top = [3 * len(E)]
    cls = []
    for e in E:
        cls.append([x(e, c) for c in range(3)])
        for c, d in itertools.combinations(range(3), 2):
            cls.append([-x(e, c), -x(e, d)])
    for t in range(fixk - 1):
        cls.append([x((t, t + 1), 0)])

    def lexleader(pi, sigma):
        """X <=lex Y where Y(pi(e)) = sigma(X(e)); positions in edge order."""
        inv = {}
        for e in E:
            f = tuple(sorted((pi[e[0]], pi[e[1]])))
            inv[f] = e
        eq = None   # literal: positions so far equal (None = true)
        for e in E:
            src = inv[e]                    # Y(e) = sigma(X(src))
            if src == e and all(sigma[c] == c for c in range(3)):
                continue                    # Y_e == X_e identically
            sinv = [sigma.index(v) for v in range(3)]
            A = [x(e, v) for v in range(3)]           # X_e = v
            B = [x(src, sinv[v]) for v in range(3)]   # Y_e = v
            pre = [] if eq is None else [-eq]
            for v in range(3):
                for w in range(v):                    # forbid X_e=v > w=Y_e
                    cls.append(sorted(set(pre + [-A[v], -B[w]])))
            top[0] += 1
            ne = top[0]
            for v in range(3):          # prefix equal and X_e = Y_e  ->  ne
                cls.append(sorted(set(pre + [-A[v], -B[v], ne])))
            if eq is not None:
                cls.append([-ne, eq])
            for v in range(3):          # ne -> X_e = Y_e
                cls.append(sorted(set([-ne, -A[v], B[v]])))
            eq = ne

    gens = []
    ident_s = [0, 1, 2]
    def transp(i, j):
        p = list(range(n)); p[i], p[j] = j, i; return p
    if lex:
        if fixk:
            W = range(fixk, n)
            for i, j in itertools.combinations(W, 2):
                gens.append((transp(i, j), ident_s))
            rev = list(range(n))
            for t in range(fixk): rev[t] = fixk - 1 - t
            gens.append((rev, ident_s))
            gens.append((list(range(n)), [0, 2, 1]))
        else:
            for i, j in itertools.combinations(range(n), 2):
                gens.append((transp(i, j), ident_s))
            gens.append((list(range(n)), [1, 0, 2]))
            gens.append((list(range(n)), [0, 2, 1]))
        for p, s in gens:
            lexleader(p, s)
    out = sys.stdout
    out.write(f'c encode.py n={n} m={m} fix={fixk} lex={int(lex)} gens={len(gens)}\n')
    out.write(f'c x(e,c)=3e+c+1, edges row-wise; path clauses added lazily\n')
    out.write(f'p cnf {top[0]} {len(cls)}\n')
    for c in cls:
        out.write(' '.join(map(str, c)) + ' 0\n')

if __name__ == '__main__':
    main()
