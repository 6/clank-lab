"""Check eigen.json on every raw flag, with no search or kernel dependency.

Run with Sage's Python 3:
    python check_form.py CASE_JSON ELL DIRECTORY PRIME [PRIME ...]

PRIME arguments select good Hecke operators to check, including any
operators held out from the search. The checker always checks the units,
every level reversal, every harmonic fibre and the ramified operator.
It takes the class and transport data as inputs.
"""
import argparse
import json
from itertools import product
from math import prod
from pathlib import Path

from sage.all import EllipticCurve, is_prime


def _read(path):
    with path.open() as stream:
        return json.load(stream)


def _matrix(record, q):
    entries = record[f"p{q}"]
    if len(entries) != 4 or any(type(x) is not int for x in entries):
        raise ValueError(f"malformed matrix at level {q}")
    return tuple(x % q for x in entries)


def _slope(x, y, q):
    x %= q
    y %= q
    if x:
        return y * pow(x, -1, q) % q
    if y:
        return q
    raise ValueError(f"zero line at {q}")


def _project(m, q):
    a, b, c, d = m
    if (a * d - b * c) % q == 0:
        raise ValueError(f"expected invertible matrix at {q}")
    columns = [(1, s) for s in range(q)] + [(0, 1)]
    return [_slope(a * x + b * y, c * x + d * y, q) for x, y in columns]


def _reverse_lines(m, q):
    a, b, c, d = m
    if (a * d - b * c) % q or not any(m):
        raise ValueError(f"expected rank-one reversal matrix at {q}")
    outgoing = _slope(a, c, q) if a or c else _slope(b, d, q)
    incoming = _slope(-b, a, q) if a or b else _slope(-d, c, q)
    return outgoing, incoming


class _Cover:
    def __init__(self, directory, ell, levels):
        self.directory = directory
        self.levels = levels
        data = _read(directory / "classes.json")
        if data["ell"] != ell or not isinstance(data["units"], list) or not data["units"]:
            raise ValueError("wrong ramified prime or missing class data")
        self.units = data["units"]
        self.classes = len(self.units)
        self.slopes = [range(q + 1) for q in levels]
        self.strides = [prod(len(r) for r in self.slopes[k + 1:])
                        for k in range(len(self.slopes))]
        self.per_class = prod(map(len, self.slopes))
        self.count = self.classes * self.per_class

    def flags(self, i):
        offset = i * self.per_class
        for section, lines in enumerate(product(*self.slopes)):
            yield offset + section, lines

    def rows(self, q):
        rows = _read(self.directory / f"q{q}.json")
        if not isinstance(rows, list) or len(rows) != self.classes:
            raise ValueError(f"wrong number of T_{q} rows")
        if any(not isinstance(row, list) or len(row) != q + 1 for row in rows):
            raise ValueError(f"T_{q} rows must have {q + 1} edges")
        return rows

    def unit(self, i, record):
        return i * self.per_class, [
            [stride * s for s in _project(_matrix(record, q), q)]
            for q, stride in zip(self.levels, self.strides)
        ]

    def edge(self, record, reversal=None):
        if not isinstance(record, dict):
            raise ValueError("expected a transport edge dictionary")
        target = record["index"]
        if type(target) is not int or not 0 <= target < self.classes:
            raise ValueError(f"invalid target class {target!r}")
        outgoing = None
        base = target * self.per_class
        offsets = []
        for q, stride in zip(self.levels, self.strides):
            a, b, c, d = _matrix(record, q)
            if q == reversal:
                outgoing, incoming = _reverse_lines((a, b, c, d), q)
                base += incoming * stride
                offsets.append(None)
            else:
                permutation = _project((d, -b, -c, a), q)
                offsets.append([stride * slope for slope in permutation])
        return outgoing, (base, offsets)


def _target(edge, lines):
    base, offsets = edge
    return base + sum(coordinate[s] for coordinate, s in zip(offsets, lines)
                      if coordinate is not None)


def _check_units(cover, values):
    for i, units in enumerate(cover.units):
        if not isinstance(units, list):
            raise ValueError(f"expected list of units for class {i}")
        moves = [cover.unit(i, unit) for unit in units]
        for index, lines in cover.flags(i):
            if any(values[_target(move, lines)] != values[index] for move in moves):
                raise ValueError(f"unit invariance fails at flag {(i, *lines)}")


def _check_ramified(cover, values, ell, eps, p):
    edges = _read(cover.directory / f"well{ell}.json")
    if not isinstance(edges, list) or len(edges) != cover.classes:
        raise ValueError(f"expected one W_{ell} edge per class")
    for i, edge in enumerate(edges):
        _, move = cover.edge(edge)
        for index, lines in cover.flags(i):
            if (values[_target(move, lines)] - eps * values[index]) % p:
                raise ValueError(f"U_{ell} eigenvalue fails at flag {(i, *lines)}")


def _check_level(cover, values, k, q, trace, p):
    stride = cover.strides[k]
    for i, row in enumerate(cover.rows(q)):
        reversals = dict(cover.edge(record, reversal=q) for record in row)
        if set(reversals) != set(range(q + 1)):
            raise ValueError(f"reversal edges at {q} do not cover the projective line")
        for index, lines in cover.flags(i):
            if lines[k] == 0:
                total = sum(values[index + s * stride] for s in range(q + 1))
                if total % p:
                    raise ValueError(f"harmonicity at {q} fails at flag {(i, *lines)}")
            # The forward U_q sum omits the reversed flag. By harmonicity
            # it is minus that flag's value.
            reversed_value = values[_target(reversals[lines[k]], lines)]
            if (reversed_value + trace * values[index]) % p:
                raise ValueError(f"reversal sign at {q} fails at flag {(i, *lines)}")


def _check_hecke(cover, values, q, trace, p):
    for i, row in enumerate(cover.rows(q)):
        moves = [cover.edge(record)[1] for record in row]
        for index, lines in cover.flags(i):
            total = sum(values[_target(move, lines)] for move in moves)
            if (total - trace * values[index]) % p:
                raise ValueError(f"T_{q} eigenvalue fails at flag {(i, *lines)}")


def check_vector(case, ell, directory, primes, values):
    """Raise ValueError on an invalid certificate or a failed equation."""
    p, N, eps = case["p"], case["N"], case["eps"]
    levels = tuple(case["levels"])
    if (tuple(sorted(set(levels))) != levels or p not in levels
            or any(not is_prime(q) or N % q or not N % (q * q) for q in levels)):
        raise ValueError("invalid level list")
    if not is_prime(ell) or not N % ell or eps not in (-1, 1):
        raise ValueError("invalid ramified prime or sign")
    good = [q for q in dict.fromkeys(primes) if q not in levels]
    if not good or any(q == ell or not is_prime(q) or not N % q for q in good):
        raise ValueError("supply at least one good Hecke prime away from N and ell")

    cover = _Cover(Path(directory), ell, levels)
    if not isinstance(values, list) or len(values) != cover.count:
        raise ValueError(f"expected a list of {cover.count} eigenfunction values")
    if any(type(a) is not int or not 0 <= a < p for a in values):
        raise ValueError(f"eigenfunction values must be integer residues in [0, {p})")
    if next((a for a in values if a), None) != 1:
        raise ValueError("first nonzero flag value must be 1")

    curve = EllipticCurve(case["ainvs"])
    if int(curve.ap(p)) != case["ap"]:
        raise ValueError("case ap disagrees with the curve")
    _check_units(cover, values)
    _check_ramified(cover, values, ell, eps, p)
    for k, q in enumerate(levels):
        trace = int(curve.ap(q))
        if abs(trace) != 1:
            raise ValueError(f"expected multiplicative reduction at {q}")
        _check_level(cover, values, k, q, trace, p)
    for q in good:
        _check_hecke(cover, values, q, int(curve.ap(q)), p)


def check(case, ell, directory, primes):
    """Verify directory/eigen.json and return the checked values."""
    directory = Path(directory)
    values = _read(directory / "eigen.json")
    check_vector(case, ell, directory, primes, values)
    return values


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("case", type=Path)
    parser.add_argument("ell", type=int)
    parser.add_argument("directory", type=Path)
    parser.add_argument("primes", type=int, nargs="+")
    args = parser.parse_args()
    values = check(_read(args.case), args.ell, args.directory, args.primes)
    print(f"Verified {len(values)} flag values")
