"""Replay all Hecke equations by pushing target flags forward through each edge."""
import itertools
import json
from math import prod
from pathlib import Path

from sage.all import EllipticCurve, factor


def check(case, ell, directory, primes):
    directory = Path(directory)
    levels = [(int(q), int(q**e)) for q, e in factor(case["N"])]
    # Each chart entry is an integral representative of a rank-one summand.
    charts = [[(1, i) for i in range(m)] + [(i, 1) for i in range(0, m, q)]
              for q, m in levels]
    sizes = tuple(map(len, charts))

    def push(matrix, column, q, m):
        a, b, c, d = matrix
        u, v = column
        x, y = a*u+b*v, c*u+d*v
        if x % q:
            return y*pow(x, -1, m) % m
        if y % q:
            return m + (x*pow(y, -1, m) % m)//q
        return None  # backtracking at a bad prime

    def mapping(edge):
        fibre = []
        for (q, m), chart in zip(levels, charts):
            inverse = [[] for v in chart]
            for j, v in enumerate(chart):
                s = push(edge[f"p{q}"], v, q, m)
                if s is not None:
                    inverse[s].append(j)
            fibre.append(inverse)
        return fibre

    def read(name):
        return json.loads((directory/name).read_text())

    def at(i, lines):
        for s, size in zip(lines, sizes):
            i = i*size+s
        return vector[i]

    vector = read("eigen.json")
    units = read("classes.json")["units"]
    p = case["p"]
    if (len(vector) != len(units)*prod(sizes)
            or any(type(a) is not int or not 0 <= a < p for a in vector)
            or next((a for a in vector if a), 0) != 1):
        raise ValueError("invalid normalized eigenfunction")
    E = EllipticCurve(case["ainvs"])
    operators = [(q, int(E.ap(q)), read(f"q{q}.json")) for q in primes+case["levels"]]
    operators.append((ell, case["eps"], [[e] for e in read(f"well{ell}.json")]))
    for i, group in enumerate(units):
        # Equality for each generator, not just their sum.
        for g in group:
            perms = mapping(g)
            for s in itertools.product(*(range(k) for k in sizes)):
                t = tuple(P[x][0] for P, x in zip(perms, s))
                if at(i, s) != at(i, t):
                    raise ValueError("unit changes the eigenfunction")
    for q, trace, rows in operators:
        degree = 1 if q == ell else q if q in case["levels"] else q+1
        for i, edges in enumerate(rows):
            maps = [(e["index"], mapping(e)) for e in edges]
            for s in itertools.product(*(range(k) for k in sizes)):
                total = count = 0
                for j, P in maps:
                    for t in itertools.product(*(A[x] for A, x in zip(P, s))):
                        total += at(j, t)
                        count += 1
                if count != degree or (total-trace*at(i, s)) % p:
                    raise ValueError(f"failed degree or eigenvalue at {q}, class {i}, flags {s}")
