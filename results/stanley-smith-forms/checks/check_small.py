"""Checker C: Conjecture 7.4 in every case with n <= 5 (minimality of the counterexample).

Usage: python3 check_small.py      (exit 0 = all assertions hold)

Written separately from check_snf.py and check_mod2.py and importing neither;
standard library only.  For every partition lambda of n <= 5 and every
1 <= k <= n it
  1. builds the polytabloids e_T of all n! fillings T in the row-tabloid module;
  2. proves the standard polytabloids are a Z-basis of their Z-span: the square
     matrix of coefficients of the tabloids {T} (T standard) in the standard
     polytabloids has determinant +-1, and every one of the n! polytabloids is
     reconstructed exactly from the integer coordinates this matrix gives;
  3. forms the matrix of X_k = (1,k) + ... + (k-1,k) in that basis;
  4. computes its Smith form from determinantal divisors (the gcd d_j of all
     j x j minors, exact integer determinants; invariant factor d_j / d_{j-1});
  5. computes Stanley's list alpha_{f-r+1} = |prod_{(i,j) in S_r} (j - i)|,
     S_r = cells k occupies in at least r standard tableaux (empty product 1).
It asserts that all 34 cases with n <= 4 agree with the conjecture, that at
n = 5 exactly two of the 35 cases disagree, both for lambda = (3,1,1):
k = 3 (Smith form 1,1,1,1,2,2 against 1,1,1,1,1,4) and k = 5 (1,1,2,2,4,4
against 1,1,1,4,4,4), and that Stanley's worked example lambda = (5,1), k = 5
gives (1,1,3,3,12), as predicted.
"""
from fractions import Fraction
from itertools import combinations, permutations
from math import gcd
import sys


class Rejected(Exception):
    pass


def need(ok, message):
    if not ok:
        raise Rejected(message)


def partitions(n, largest=None):
    largest = n if largest is None else largest
    if n == 0:
        yield ()
        return
    for first in range(min(n, largest), 0, -1):
        for rest in partitions(n - first, first):
            yield (first,) + rest


def diagram(lam):
    return [(r, c) for r, length in enumerate(lam) for c in range(length)]


def fillings(lam):
    """Every filling of the diagram, as a dict cell -> entry (entries 1..n)."""
    cells = diagram(lam)
    for values in permutations(range(1, len(cells) + 1)):
        yield dict(zip(cells, values))


def is_standard(lam, filling):
    return all(filling[(r, c)] < filling[(r, c + 1)] for (r, c) in filling if (r, c + 1) in filling) \
        and all(filling[(r, c)] < filling[(r + 1, c)] for (r, c) in filling if (r + 1, c) in filling)


def tabloid(filling, n):
    """The row tabloid of a filling: the row of each entry 1..n."""
    rows = [0] * n
    for (r, _), value in filling.items():
        rows[value - 1] = r
    return tuple(rows)


def sign(order):
    inversions = sum(1 for a, b in combinations(order, 2) if a > b)
    return -1 if inversions % 2 else 1


def polytabloid(lam, filling):
    """e_T = sum over column permutations sigma of sgn(sigma) {sigma T}."""
    n = sum(lam)
    columns = [[(r, c) for r in range(len(lam)) if lam[r] > c] for c in range(lam[0])]
    result = {}
    def extend(index, current, sgn):
        if index == len(columns):
            key = tabloid(current, n)
            result[key] = result.get(key, 0) + sgn
            return
        column = columns[index]
        for order in permutations(range(len(column))):
            moved = dict(current)
            for source, target in zip(column, (column[i] for i in order)):
                moved[target] = filling[source]
            extend(index + 1, moved, sgn * sign(order))
    extend(0, dict(filling), 1)
    return {key: value for key, value in result.items() if value}


def jucys_murphy(k, vector):
    """X_k acting on a combination of tabloids: (i,k) swaps the rows of i and k."""
    out = {}
    for i in range(1, k):
        for key, value in vector.items():
            rows = list(key)
            rows[i - 1], rows[k - 1] = rows[k - 1], rows[i - 1]
            rows = tuple(rows)
            out[rows] = out.get(rows, 0) + value
    return {key: value for key, value in out.items() if value}


def determinant(matrix):
    """Exact integer determinant by fraction-free (Bareiss) elimination."""
    m = [list(row) for row in matrix]
    size = len(m)
    if size == 0:
        return 1
    flip, previous = 1, 1
    for p in range(size - 1):
        if m[p][p] == 0:
            swap = next((r for r in range(p + 1, size) if m[r][p]), None)
            if swap is None:
                return 0
            m[p], m[swap] = m[swap], m[p]
            flip = -flip
        for r in range(p + 1, size):
            for c in range(p + 1, size):
                m[r][c] = (m[r][c] * m[p][p] - m[r][p] * m[p][c]) // previous
        previous = m[p][p]
    return flip * m[size - 1][size - 1]


def inverse(matrix):
    size = len(matrix)
    work = [[Fraction(x) for x in row] + [Fraction(int(i == j)) for j in range(size)]
            for i, row in enumerate(matrix)]
    for p in range(size):
        pivot = next(r for r in range(p, size) if work[r][p])
        work[p], work[pivot] = work[pivot], work[p]
        scale = work[p][p]
        work[p] = [x / scale for x in work[p]]
        for r in range(size):
            if r != p and work[r][p]:
                factor = work[r][p]
                work[r] = [x - factor * y for x, y in zip(work[r], work[p])]
    return [row[size:] for row in work]


def smith_form(matrix):
    """Invariant factors from determinantal divisors d_j = gcd of the j x j minors."""
    size = len(matrix)
    divisors = [1]
    for j in range(1, size + 1):
        d = 0
        for rows in combinations(range(size), j):
            for cols in combinations(range(size), j):
                d = gcd(d, determinant([[matrix[r][c] for c in cols] for r in rows]))
        divisors.append(d)
    factors = []
    for j in range(1, size + 1):
        factors.append(0 if divisors[j] == 0 else divisors[j] // divisors[j - 1])
    return factors


def prediction(lam, k, standard):
    counts = {}
    for filling in standard:
        cell = next(cell for cell, value in filling.items() if value == k)
        counts[cell] = counts.get(cell, 0) + 1
    f = len(standard)
    alpha = [0] * f
    for r in range(1, f + 1):
        product = 1
        for (row, col), count in counts.items():
            if count >= r:
                product *= (col + 1) - (row + 1)
        alpha[f - r] = abs(product)
    return alpha


def case_results(lam):
    """The Smith form of every X_k on S^lambda, after proving the standard basis."""
    n = sum(lam)
    all_fillings = list(fillings(lam))
    standard = [t for t in all_fillings if is_standard(lam, t)]
    f = len(standard)
    basis = [polytabloid(lam, t) for t in standard]
    keys = [tabloid(t, n) for t in standard]
    need(len(set(keys)) == f, 'standard tableaux with equal tabloids')
    square = [[e.get(key, 0) for e in basis] for key in keys]
    need(abs(determinant(square)) == 1, f'{lam}: tabloid submatrix is not unimodular')
    solve = inverse(square)

    def coordinates(vector):
        x = [sum(solve[i][j] * vector.get(keys[j], 0) for j in range(f)) for i in range(f)]
        need(all(c.denominator == 1 for c in x), f'{lam}: non-integral coordinates')
        x = [int(c) for c in x]
        rebuilt = {}
        for c, e in zip(x, basis):
            for key, value in e.items():
                rebuilt[key] = rebuilt.get(key, 0) + c * value
        need({key: v for key, v in rebuilt.items() if v} == vector, f'{lam}: not in the Z-span')
        return x

    for filling in all_fillings:
        coordinates(polytabloid(lam, filling))
    results = {}
    for k in range(1, n + 1):
        columns = [coordinates(jucys_murphy(k, e)) for e in basis]
        matrix = [[columns[j][i] for j in range(f)] for i in range(f)]
        results[k] = (smith_form(matrix), prediction(lam, k, standard))
    return results


def main():
    agree, disagree = 0, []
    for n in range(1, 6):
        for lam in partitions(n):
            for k, (snf, predicted) in case_results(lam).items():
                if snf == predicted:
                    agree += 1
                else:
                    disagree.append((n, lam, k, snf, predicted))
    small = [d for d in disagree if d[0] <= 4]
    need(not small, f'disagreement with n <= 4: {small}')
    expected = [(5, (3, 1, 1), 3, [1, 1, 1, 1, 2, 2], [1, 1, 1, 1, 1, 4]),
                (5, (3, 1, 1), 5, [1, 1, 2, 2, 4, 4], [1, 1, 1, 4, 4, 4])]
    need(sorted(disagree) == expected, f'disagreements at n = 5: {disagree}')
    need(agree + len(disagree) == 34 + 35, 'wrong number of cases')
    snf, predicted = case_results((5, 1))[5]
    need(snf == predicted == [1, 1, 3, 3, 12], f'(5,1), k=5 gives {snf}, predicted {predicted}')
    print(f'ACCEPT n <= 5: all 34 cases with n <= 4 agree; at n = 5, 33 of 35 agree and only '
          f'(3,1,1) with k = 3 and k = 5 disagree; (5,1), k = 5 gives {snf} as predicted')


if __name__ == '__main__':
    try:
        main()
    except Rejected as exc:
        print('REJECT:', exc)
        sys.exit(1)
