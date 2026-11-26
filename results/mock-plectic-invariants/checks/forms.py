"""Solve for a normalized residual eigenfunction on the Brandt flag cover.

Use Sage's Python 3. The case supplies p, D, N, ainvs, levels, eps,
ap and vdelta. The arithmetic inputs D and vdelta are used elsewhere.
primes supplies good Hecke primes in the desired elimination order.
Level primes in that list are handled by their reversal and harmonicity
equations. The ramified operator is read from well{ell}.json.

The signed quotient parametrizes exactly the functions invariant under
the units and with the prescribed reversal and ramified eigenvalues.
For odd p, any inconsistent sign cycle forces its whole component to
vanish. Each remaining component has one coordinate. Good Hecke
equations at the component representatives suffice on a certified graph
because the good operators commute with the level and ramified operators
on unit orbits. Harmonicity is imposed on every fibre of every level.

For each level q, we also compute the lower-level eigenspace after
forgetting q, using only units, W_ell and the good Hecke equations. The
trace that sums over the forgotten lines commutes with W_ell and every
good T_r: the inverse transports on the omitted projective line are
bijections. The trace is unit invariant for the same reason. We require
every such lower eigenspace to vanish. Thus the trace of a full Hecke
eigenform at each q is zero. On a harmonic function U_q sums over the
forward lines at the reversed flag, giving minus the reversal value.
The genuine eigenform therefore has the reversal signs imposed here.

Successive exact right kernels compute the dimension for the finite
search. We require dimension one and independently check its candidate
on all the flags. Together with existence of a full eigenform from level
raising, this identifies the line with the genuine one. A dimension
greater than one, or a nonzero lower eigenspace, can mean the chosen
good primes have not separated the eigensystems. In either case solve
aborts and further good primes can be supplied.
"""
import argparse
import json
from itertools import islice, product
from math import prod
from pathlib import Path
from tempfile import NamedTemporaryFile

from sage.all import EllipticCurve, GF, is_prime, matrix

from check_form import check_vector


# At conductor 817 the system before imposing the involution has 4,913 coordinates.
# Reserve for six double-width dense buffers and bound
# cumulative elimination work relative to that reference solve.
MAX_FLAGS = 250_000
MAX_TRANSPORTS = 30_000_000
MAX_DENSE_BYTES = 1536 * 1024**2
MAX_DENSE_WORK = 8 * 4913**3
MAX_BLOCK_ENTRIES = 500_000
MAX_GRAPH_BYTES = 128 * 1024**2


class PriceLimit(ValueError):
    """The estimated solve exceeds the supported price."""


def _line(x, y, prime):
    if x % prime:
        return y * pow(x, -1, prime) % prime
    if y % prime:
        return prime
    raise ValueError("zero column in projective transport")


def _action(matrix_entries, prime):
    a, b, c, d = matrix_entries
    if (a * d - b * c) % prime == 0:
        raise ValueError(f"singular transport at {prime}")
    return tuple(
        _line(a + b * s, c + d * s, prime) for s in range(prime)
    ) + (_line(b, d, prime),)


def _adj(matrix_entries):
    a, b, c, d = matrix_entries
    return d, -b, -c, a


def _image(matrix_entries, prime):
    a, b, c, d = matrix_entries
    if (a * d - b * c) % prime:
        raise ValueError(f"reversal transport is invertible at {prime}")
    if a % prime or c % prime:
        return _line(a, c, prime)
    return _line(b, d, prime)


def _load(directory, name):
    path = directory / name
    if path.stat().st_size > MAX_GRAPH_BYTES:
        raise PriceLimit(f"{name} exceeds the graph input size cap")
    with path.open() as stream:
        return json.load(stream)


class _Flags:
    def __init__(self, directory, ell, levels, primes, *, reverse=True):
        self.directory = directory
        self.levels = levels
        data = _load(directory, "classes.json")
        if data["ell"] != ell or not data["units"]:
            raise ValueError("classes.json has the wrong ramified prime or no classes")

        self.ranges = tuple(range(q + 1) for q in levels)
        self.strides = tuple(prod(len(r) for r in self.ranges[k + 1:])
                             for k in range(len(levels)))
        self.fibre_size = prod(map(len, self.ranges))
        self.classes = len(data["units"])
        self.count = self.fibre_size * self.classes
        if self.count > MAX_FLAGS:
            raise PriceLimit(f"{self.count:,} raw flags exceed the {MAX_FLAGS:,} flag cap")
        visits = (self.count * (sum(q + 1 for q in primes) + 2 * len(levels) + 1)
                  + self.fibre_size * sum(map(len, data["units"])))
        if visits > MAX_TRANSPORTS:
            raise PriceLimit(f"{visits:,.0f} flag visits exceed the transport price cap")

        self.units = [
            [tuple(_action(unit[f"p{q}"], q) for q in levels) for unit in row]
            for row in data["units"]
        ]
        self.reversals = []
        if reverse:
            self.reversals = [
                self._read_reversal(position, q) for position, q in enumerate(levels)
            ]
        well = _load(directory, f"well{ell}.json")
        if not isinstance(well, list) or len(well) != self.classes:
            raise ValueError(f"expected one W_{ell} edge per class")
        self.well = [self._edge(edge) for edge in well]

    def states(self):
        return product(range(self.classes), *self.ranges)

    def position(self, base, moves, lines):
        return base + sum(move[s] * stride for move, s, stride
                          in zip(moves, lines, self.strides) if move is not None)

    def _edge(self, edge, reversal=None):
        if not isinstance(edge, dict):
            raise ValueError("expected a transport edge dictionary")
        j = edge["index"]
        if type(j) is not int or not 0 <= j < self.classes:
            raise ValueError(f"invalid target class {j!r}")
        base = j * self.fibre_size
        moves = []
        for q, stride in zip(self.levels, self.strides):
            inverse = _adj(edge[f"p{q}"])
            if q == reversal:
                base += stride * _image(inverse, q)
                moves.append(None)
            else:
                moves.append(_action(inverse, q))
        return base, tuple(moves)

    def _rows(self, prime):
        rows = _load(self.directory, f"q{prime}.json")
        if len(rows) != self.classes or any(len(row) != prime + 1 for row in rows):
            raise ValueError(f"wrong number of T_{prime} edges")
        return rows

    def _read_reversal(self, position, prime):
        rows = []
        for row in self._rows(prime):
            outgoing = sorted((_image(edge[f"p{prime}"], prime), k)
                              for k, edge in enumerate(row))
            if [s for s, _ in outgoing] != list(self.ranges[position]):
                raise ValueError(f"reversal edges at {prime} do not cover the projective line")
            rows.append([self._edge(row[k], prime) for _, k in outgoing])
        return rows

    def hecke(self, prime):
        return [[self._edge(edge) for edge in row] for row in self._rows(prime)]

    def harmonic_fibres(self, position):
        stride = self.strides[position]
        width = len(self.ranges[position])
        for block in range(0, self.count, width * stride):
            for tail in range(stride):
                start = block + tail
                yield range(start, start + width * stride, stride)


class _SignedComponents:
    def __init__(self, count):
        self.parent = list(range(count))
        self.sign = [1] * count
        self.size = [1] * count
        self.zero = [False] * count

    def find(self, i):
        parent = self.parent[i]
        if parent != i:
            self.parent[i], sign = self.find(parent)
            self.sign[i] *= sign
        return self.parent[i], self.sign[i]

    def join(self, i, j, sign):
        """Impose f(j) = sign * f(i)."""
        root_i, sign_i = self.find(i)
        root_j, sign_j = self.find(j)
        relation = sign * sign_i * sign_j
        if root_i == root_j:
            if relation == -1:
                self.zero[root_i] = True
            return
        if self.size[root_i] < self.size[root_j]:
            root_i, root_j = root_j, root_i
        self.parent[root_j] = root_i
        self.sign[root_j] = relation
        self.size[root_i] += self.size[root_j]
        self.zero[root_i] |= self.zero[root_j]


def _quotient(flags, reversal_signs, eps):
    components = _SignedComponents(flags.count)
    for index, (i, *lines) in enumerate(flags.states()):
        for moves in flags.units[i]:
            target = flags.position(i * flags.fibre_size, moves, lines)
            components.join(index, target, 1)
        for k, (rows, sign) in enumerate(zip(flags.reversals, reversal_signs)):
            target = flags.position(*rows[i][lines[k]], lines)
            components.join(index, target, sign)
        target = flags.position(*flags.well[i], lines)
        components.join(index, target, eps)

    representatives, labels, root_labels = [], [], {}
    for index, state in enumerate(flags.states()):
        root, sign = components.find(index)
        if components.zero[root]:
            labels.append((0, 0))
            continue
        if root not in root_labels:
            root_labels[root] = len(representatives), sign
            representatives.append(state)
        column, base_sign = root_labels[root]
        labels.append((column, sign * base_sign))
    return representatives, labels


def _add(row, label):
    column, sign = label
    if sign:
        row[column] = row.get(column, 0) + sign


def _nonzero(row, p):
    return {column: coefficient % p for column, coefficient in row.items()
            if coefficient % p}


def _hecke_equations(flags, representatives, labels, prime, trace, p):
    graph = flags.hecke(prime)
    for column, (i, *lines) in enumerate(representatives):
        row = {column: -trace}
        for base, moves in graph[i]:
            _add(row, labels[flags.position(base, moves, lines)])
        row = _nonzero(row, p)
        if row:
            yield row


def _harmonic_equations(flags, labels, position, p):
    for fibre in flags.harmonic_fibres(position):
        row = {}
        for index in fibre:
            _add(row, labels[index])
        row = _nonzero(row, p)
        if row:
            yield row


class _Kernel:
    """Intersect exact kernels, storing the current basis by rows."""

    def __init__(self, p, width, work=0):
        if 6 * 8 * width**2 > MAX_DENSE_BYTES:
            raise PriceLimit(f"{width:,} quotient variables exceed the dense memory price cap")
        self.p = p
        self.field = GF(p)
        self.width = width
        self.basis = None
        self.work = work

    @property
    def dimension(self):
        return self.width if self.basis is None else self.basis.nrows()

    def impose(self, rows):
        while self.dimension:
            if self.dimension == 1:
                vector = ([1] if self.basis is None
                          else [int(x) for x in self.basis.row(0)])
                for row in rows:
                    if sum(a * vector[j] for j, a in row.items()) % self.p:
                        self.basis = matrix(self.field, 0, self.width)
                        break
                return

            block = []
            entries = 0
            for row in islice(rows, self.width):
                block.append(row)
                entries += len(row)
                if entries >= MAX_BLOCK_ENTRIES:
                    break
            if not block:
                return
            height = len(block)
            self.work += height * self.width * self.dimension
            if self.work > MAX_DENSE_WORK:
                raise PriceLimit("cumulative dense elimination exceeds the CPU price cap")
            equations = matrix(self.field, height, self.width)
            for i, row in enumerate(block):
                for j, coefficient in row.items():
                    equations[i, j] = coefficient
            if self.basis is None:
                self.basis = equations.right_kernel_matrix()
            else:
                restricted = equations * self.basis.transpose()
                change = restricted.right_kernel_matrix()
                if change.nrows() < self.dimension:
                    self.basis = change * self.basis

    def generator(self):
        return [1] if self.basis is None else [int(x) for x in self.basis.row(0)]


def _exclude_lower_eigenspaces(directory, ell, levels, traces, p, eps, work):
    nullities = {}
    for omitted in levels:
        remaining = tuple(q for q in levels if q != omitted)
        flags = _Flags(directory, ell, remaining, traces, reverse=False)
        reps, labels = _quotient(flags, (), eps)
        space = _Kernel(p, len(reps), work)
        dims = []
        for prime, trace in traces.items():
            space.impose(_hecke_equations(flags, reps, labels, prime, trace, p))
            dims.append(space.dimension)
            if not space.dimension:
                break
        if space.dimension:
            raise ValueError(f"lower level omitting {omitted} has joint eigenspace "
                             f"dimension {space.dimension}; T nullities {dims}; "
                             "trace vanishing is unresolved")
        nullities[omitted] = dims
        work = space.work
    return nullities


def solve(case, ell, directory, primes):
    """Write directory/eigen.json atomically on success and return its values."""
    directory = Path(directory)
    p, N, eps = (case[key] for key in ("p", "N", "eps"))
    levels = tuple(case["levels"])
    if (levels != tuple(sorted(set(levels))) or p not in levels
            or any(not is_prime(q) or N % q or N % (q * q) == 0 for q in levels)):
        raise ValueError("levels must be increasing distinct primes dividing N exactly once")
    if not is_prime(ell) or N % ell == 0 or eps not in (-1, 1):
        raise ValueError("expected a ramified prime away from N and eps = ±1")
    good = tuple(q for q in dict.fromkeys(primes) if q not in levels)
    if not good or any(not is_prime(q) or q == ell or N % q == 0 for q in good):
        raise ValueError("supply at least one good Hecke prime away from N and ell")

    curve = EllipticCurve(case["ainvs"])
    bad_traces = tuple(int(curve.ap(q)) for q in levels)
    if bad_traces[levels.index(p)] != case["ap"] or any(abs(a) != 1 for a in bad_traces):
        raise ValueError("case ap or multiplicative level traces disagree with the curve")
    # Over F_2 opposite signs agree, so all quotient relations have sign +1.
    signs = tuple(-a for a in bad_traces) if p != 2 else (1,) * len(levels)
    quotient_eps = eps if p != 2 else 1
    traces = {q: int(curve.ap(q)) for q in good}
    flags = _Flags(directory, ell, levels, good)
    reps, labels = _quotient(flags, signs, quotient_eps)
    space = _Kernel(p, len(reps))
    dimensions = []
    for q, trace in traces.items():
        space.impose(_hecke_equations(flags, reps, labels, q, trace, p))
        dimensions.append((f"T_{q}", space.dimension))
    for k, q in enumerate(levels):
        space.impose(_harmonic_equations(flags, labels, k, p))
        dimensions.append((f"harmonic_{q}", space.dimension))
    if space.dimension != 1:
        raise ValueError(f"joint eigenspace dimension {space.dimension}; "
                         f"{len(reps)} quotient variables, dimensions {dimensions}")
    lower = _exclude_lower_eigenspaces(directory, ell, levels, traces, p,
                                      quotient_eps, space.work)
    vector = space.generator()
    values = [sign * vector[column] % p if sign else 0 for column, sign in labels]
    scale = pow(next(value for value in values if value), -1, p)
    values = [value * scale % p for value in values]
    check_vector(case, ell, directory, good, values)

    with NamedTemporaryFile("w", dir=directory, prefix=".eigen-", delete=False) as stream:
        temporary = Path(stream.name)
        try:
            json.dump(values, stream, separators=(",", ":"))
            stream.write("\n")
            stream.close()
            temporary.replace(directory / "eigen.json")
        finally:
            temporary.unlink(missing_ok=True)

    print(f"{flags.count} flags, {len(reps)} quotient variables, dimensions {dimensions}; "
          f"lower-level T nullities by omitted prime {lower}", flush=True)
    return values


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("case", type=Path)
    parser.add_argument("ell", type=int)
    parser.add_argument("directory", type=Path)
    parser.add_argument("primes", type=int, nargs="+")
    args = parser.parse_args()
    solve(json.loads(args.case.read_text()), args.ell, args.directory, args.primes)
