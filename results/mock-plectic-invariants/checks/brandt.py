"""Exact definite Brandt graph and local flag transports (SageMath 10.8)."""

import argparse
import json
from collections import Counter, defaultdict
from itertools import chain, combinations, product
from pathlib import Path

from sage.all import BrandtModule, GF, Integers, QQ, ZZ, kronecker_symbol, matrix, set_random_seed


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def save(path, obj):
    temporary = path.with_suffix(".tmp")
    temporary.write_text(json.dumps(obj, separators=(",", ":")) + "\n")
    temporary.replace(path)


def linear_combination(coefficients, basis):
    return sum(c * x for c, x in zip(coefficients, basis))


def reduce_matrix(full, ring):
    """Reduce a rational matrix, allowing only unit denominators."""
    denominator = full.denominator()
    require(denominator.gcd(ring.cardinality()) == 1,
            "nonintegral transport in the local lattice basis")
    return (full * denominator).change_ring(ZZ).change_ring(ring) * ring(denominator)**-1


class Lattice:
    """Quaternion lattice with coordinates in the actual given Z-basis."""

    def __init__(self, obj):
        self.basis = obj.basis()
        self.matrix = matrix(QQ, [x.coefficient_tuple() for x in self.basis])
        self.inverse = self.matrix.inverse()

    def coordinates(self, elements):
        return matrix(QQ, [x.coefficient_tuple() for x in elements]) * self.inverse

    def right_action(self, x):
        return self.coordinates(b * x for b in self.basis).change_ring(ZZ)

    def left_map_from(self, source, x):
        return self.coordinates(x * b for b in source.basis)


def nonisotropic(vectors, pairing):
    for v in [*vectors, *(u + v for u, v in combinations(vectors, 2))]:
        if (v * pairing).dot_product(v):
            return v
    raise ArithmeticError("degenerate trace-zero form at a split prime")


def split_idempotent(order, prime, depth):
    """Lift a rank-one idempotent through the maximal order, also at 2."""
    basis = order.basis
    if prime == 2:
        for coefficients in product(range(2), repeat=4):
            e = linear_combination(coefficients, basis)
            if e.reduced_trace() % 2 == 1 and e.reduced_norm() % 2 == 0:
                break
        else:
            raise ArithmeticError("no rank-one idempotent at 2")
    else:
        field = GF(prime)
        trace = matrix(field, [[x.reduced_trace() for x in basis]])
        pairing = matrix(field, [[(x * y).reduced_trace() for y in basis] for x in basis])
        pure = trace.right_kernel().basis()
        u = nonisotropic(pure, pairing)
        perpendicular = matrix(field, [trace.row(0), u * pairing]).right_kernel().basis()
        v = nonisotropic(perpendicular, pairing)
        a = -(u * pairing).dot_product(u) / 2
        b = -(v * pairing).dot_product(v) / 2
        target = -field(4)**-1
        for s in field:
            square = (target - a * s*s) / b
            if square.is_square():
                t = square.sqrt()
                t = min(int(t), int(-t))
                e = int(field(2)**-1) + linear_combination([int(c) for c in s*u + t*v], basis)
                break
        else:
            raise ArithmeticError(f"no rank-one idempotent at {prime}")

    precision = 1
    while precision < depth:
        precision = min(2 * precision, depth)
        e = 3*e**2 - 2*e**3
        coordinates = order.coordinates([e]).change_ring(ZZ).list()
        e = linear_combination([c % prime**precision for c in coordinates], basis)
    modulus = prime**depth
    require(e.reduced_trace() % prime == 1 and e.reduced_norm() % prime == 0,
            f"nonprimitive idempotent at {prime}")
    error = order.coordinates([e**2 - e]).change_ring(ZZ)
    require(not any(c % modulus for c in error.list()), f"idempotent lift at {prime}")
    return e


class LocalFrame:
    """Rows of basis generate I e in exact lattice coordinates modulo q^d."""

    def __init__(self, lattice, split, native=None):
        self.prime = split.prime
        self.ring = split.ring
        self.projector = lattice.right_action(split.idempotent).change_ring(self.ring)
        self.indices = self.projector.change_ring(GF(self.prime)).transpose().pivots()
        require(len(self.indices) == 2, f"wrong local column rank at {self.prime}")
        self.basis = self.projector.matrix_from_rows(self.indices)
        self.columns = self.basis.change_ring(GF(self.prime)).pivots()
        if native is not None:
            native_lattice = matrix(self.ring, [native(x) for x in lattice.basis])
            require(int(native_lattice.det()) % self.prime != 0,
                    f"legacy frame fails to span the matrix algebra at {self.prime}")
            e_matrix = native(split.idempotent)
            column = next(j for j in range(2)
                          if any(e_matrix[2*i+j] % self.prime for i in range(2)))
            projected = [native(lattice.basis[i] * split.idempotent) for i in self.indices]
            change = matrix(self.ring, [[x[column], x[2+column]] for x in projected])
            require(int(change.det()) % self.prime != 0, "singular native change of basis")
            self.basis = change.inverse() * self.basis

        self.inverse_minor = self.basis.matrix_from_columns(self.columns).inverse()
        require(self.basis * self.projector == self.basis
                and self.coordinates(self.projector) * self.basis == self.projector,
                f"projected frame does not span the lattice at {self.prime}")

    def coordinates(self, rows):
        return rows.matrix_from_columns(self.columns) * self.inverse_minor

    def transport_from(self, source, full, index):
        full = reduce_matrix(full, self.ring)
        require(source.projector * full == full * self.projector,
                f"left transport does not commute with right projection at {self.prime}")
        image = source.basis * full
        coordinates = self.coordinates(image)
        require(coordinates * self.basis == image, f"transport leaves I e at {self.prime}")
        determinant = ZZ(int(coordinates.det()))
        modulus = ZZ(self.ring.cardinality())
        expected = QQ(index).numerator().gcd(modulus)
        require(determinant.gcd(modulus) == expected,
                f"wrong determinant valuation at {self.prime}")
        return coordinates.transpose()


class SplitOrder:
    """Morita splitting O_q -> End(O_q e) in the order's own coordinates."""

    def __init__(self, order, prime, depth, native=None):
        self.prime = prime
        self.ring = Integers(prime**depth)
        self.idempotent = split_idempotent(order, prime, depth)
        frame = LocalFrame(order, self, native)
        field = GF(prime)
        maps = []
        for x in order.basis:
            full = order.left_map_from(order, x).change_ring(ZZ).change_ring(self.ring)
            image = frame.basis * full
            coordinates = frame.coordinates(image)
            require(coordinates * frame.basis == image, f"order action leaves O e at {prime}")
            maps.append(coordinates.list())
        require(matrix(field, [[int(c) for c in row] for row in maps]).rank() == 4,
                f"order action does not give a full matrix algebra at {prime}")


def legacy_matrix(prime, depth):
    """The frozen 817 splitting of (-2,-269), including its root choice."""
    modulus = prime**depth
    a, b = next((a, b) for b in range(prime) for a in range(1, prime)
                if (a*a + 2*b*b + 269) % prime == 0)
    for n in range(1, depth):
        power = prime**n
        a += power * ((-(a*a + 2*b*b + 269)//power * pow(2*a, -1, prime)) % prime)

    def encode(x):
        h, i, j, k = [int(c.numerator()) * pow(int(c.denominator()), -1, modulus)
                      for c in x.coefficient_tuple()]
        return [(h+a*j-2*b*k) % modulus, (-2*i+2*b*j+2*a*k) % modulus,
                (i+b*j+a*k) % modulus, (h-a*j+2*b*k) % modulus]

    return encode


def same_lattice(first, second):
    return first.free_module() == second.free_module()


def ramified_prime(order, ell):
    """Find the two-sided prime by the radical of the reduced-trace pairing."""
    basis = order.basis()
    pairing = matrix(GF(ell), [[(x * y).reduced_trace() for y in basis] for x in basis])
    radical = pairing.right_kernel()
    require(radical.dimension() == 2, "wrong trace radical at the ramified prime")
    generators = [ell*x for x in basis]
    generators += [linear_combination([int(c) for c in row], basis) for row in radical.basis()]
    algebra = order.quaternion_algebra()
    ideal = algebra.ideal(generators)
    unit = order.unit_ideal()
    require(same_lattice(unit * ideal, ideal) and same_lattice(ideal * unit, ideal)
            and same_lattice(ideal * ideal, unit.scale(ell)),
            "ramified lattice is not the two-sided prime")
    require(ideal.norm() == ell, "wrong norm of the ramified prime")
    return ideal


def morita_neighbors(order, ideal, lattice, split):
    """Enumerate the q+1 lines of (I/qI)e and lift their right spans."""
    prime = split.prime
    # The selected rows come from exact elements of I, even if q divides N(I).
    frame = LocalFrame(lattice, split)
    first, second = [lattice.basis[i] * split.idempotent for i in frame.indices]
    base = [prime*x for x in ideal.basis()]
    for x in chain((first + t*second for t in range(prime)), (second,)):
        yield order.right_ideal(base + [x])


def line_key(matrix_at_prime, prime):
    field = GF(prime)
    # Reduce via integers, since the original ring may be Z/q^3.
    reduced = matrix(field, 2, 2, [int(x) for x in matrix_at_prime.list()])
    require(reduced.rank() == 1, f"edge does not induce a line at {prime}")
    x, y = next(col for col in reduced.columns() if col)
    return int(y / x) if x else prime


class BrandtGraph:
    def __init__(self, ell, depths, legacy):
        set_random_seed(817)
        self.ell = ell
        self.module = BrandtModule(ell)
        self.order = self.module.order_of_level_N()
        self.algebra = self.order.quaternion_algebra()
        require(self.algebra.discriminant() == ell and self.order.discriminant() == ell,
                "wrong algebra or maximal-order discriminant")
        self.order_lattice = Lattice(self.order)
        self.ideals = self.module.right_ideals()
        require(len(self.ideals) == self.module.dimension(), "missing maximal-order classes")
        self.lattices = [Lattice(ideal) for ideal in self.ideals]
        self.buckets = defaultdict(list)
        for index, (ideal, lattice) in enumerate(zip(self.ideals, self.lattices)):
            for x in self.order.basis():
                lattice.right_action(x)  # checks exact right stability
            bucket = self.buckets[self.fingerprint(ideal)]
            require(all(not ideal.is_right_equivalent(self.ideals[i], 0) for i in bucket),
                    "duplicated maximal-order class")
            bucket.append(index)
        if legacy:
            require(tuple(self.algebra.invariants()) == (-2, -269), "817 presentation changed")
        self.legacy = legacy
        self.depths = depths
        self.native = {r: legacy_matrix(r, depth) for r, depth in depths.items()} if legacy else {}
        self.splits = {r: SplitOrder(self.order_lattice, r, depth, self.native.get(r))
                       for r, depth in depths.items()}
        self.frames = {r: [LocalFrame(lattice, split, self.native.get(r)) for lattice in self.lattices]
                       for r, split in self.splits.items()}

    @classmethod
    def from_case(cls, case, ell):
        """Open the same ideal representatives and local frames as build()."""
        p, N, ell = (int(value) for value in (case["p"], case["N"], ell))
        depths = level_depths(case)
        if not ZZ(ell).is_prime() or ell in depths:
            raise ValueError("ell must be prime and coprime to N")
        return cls(ell, depths, (p, N, ell) == (19, 817, 269))

    @staticmethod
    def fingerprint(ideal):
        return tuple(ideal.theta_series_vector(32))

    def classify(self, ideal):
        for index in self.buckets[self.fingerprint(ideal)]:
            same, alpha = ideal.is_right_equivalent(self.ideals[index], 0, certificate=True)
            if same:
                require(same_lattice(alpha * self.ideals[index], ideal), "false equivalence certificate")
                return index, alpha
        raise ArithmeticError("unclassified ideal")

    def _transport(self, row, column, alpha, full, degree):
        require(abs(full.det()) == degree**2, "wrong exact lattice determinant of transport")
        maps = {r: frames[row].transport_from(frames[column], full, degree) for r, frames in self.frames.items()}
        for r, native in self.native.items():
            require([int(c) for c in maps[r].list()] == native(alpha), f"legacy coordinate mismatch at {r}")
        return maps

    def transport(self, row, column, alpha, index):
        """Certify an integral left map I_column -> I_row of index index^2."""
        full = self.lattices[row].left_map_from(self.lattices[column], alpha).change_ring(ZZ)
        require(alpha.reduced_norm() * self.ideals[column].norm() == index * self.ideals[row].norm(),
                "wrong reduced norm of transport")
        return self._transport(row, column, alpha, full, index)

    def local_transport(self, row, column, alpha):
        """Frame a left map I_column -> I_row that is integral at all flag primes."""
        full = self.lattices[row].left_map_from(self.lattices[column], alpha)
        degree = alpha.reduced_norm() * self.ideals[column].norm() / self.ideals[row].norm()
        require(degree > 0, "zero local transport")
        return self._transport(row, column, alpha, full, degree)

    @staticmethod
    def encode(maps, reduce_units=False):
        return {f"p{r}": [int(c) % r if reduce_units else int(c) for c in m.list()]
                for r, m in maps.items()}

    def _order_elements(self, index, bound):
        order = self.ideals[index].left_order()
        vectors = order.quadratic_form().short_vector_list_up_to_length(bound + 1)
        return [[linear_combination(v, order.basis()) for v in shell] for shell in vectors]

    def cm_embeddings(self, D):
        """Yield (class index, quaternion omega), in classes.json order."""
        trace, norm = cm_polynomial(D)
        for i in range(len(self.ideals)):
            for x in self._order_elements(i, norm)[norm]:
                if x.reduced_trace() == trace and x.reduced_norm() == norm:
                    yield i, x

    def class_data(self, D):
        trace, norm = cm_polynomial(D)
        units, cm, weights = [], [], []
        for i in range(len(self.ideals)):
            order_units = self._order_elements(i, norm)[1]
            unit_set = set(order_units)
            require(len(unit_set) == len(order_units) and 1 in unit_set and -1 in unit_set
                    and all(x.reduced_norm() == 1 and -x in unit_set for x in unit_set),
                    "wrong unit enumeration")
            weights.append(len(order_units))
            units.append([self.encode(self.transport(i, i, x, 1), reduce_units=self.legacy)
                          for x in order_units if x != -1])
        for i, x in self.cm_embeddings(D):
            maps = self.transport(i, i, x, norm)
            for r, local in maps.items():
                modulus = int(local.base_ring().cardinality())
                require(int(local.trace()) == trace % modulus and int(local.det()) == norm % modulus,
                        f"CM polynomial does not match at {r}")
            cm.append(dict(index=i, omega=str(x), **self.encode(maps)))
        require(sum(QQ(1)/weight for weight in weights) == QQ(self.ell-1)/24,
                "maximal-order mass mismatch")
        quadratic_units = {-3: 6, -4: 4}.get(D, 2)
        embedding_count = ZZ(D).class_number() * (1 - kronecker_symbol(D, self.ell))
        require(sum(QQ(quadratic_units)/weights[c["index"]] for c in cm) == embedding_count,
                "optimal embedding count mismatch")
        self.weights = weights
        return dict(units=units, cm=cm, ell=self.ell)

    def hecke(self, prime):
        split = self.splits.get(prime)
        if split is None and not self.legacy:
            split = SplitOrder(self.order_lattice, prime, 1)
        rows, counts = [], []
        for i, (ideal, lattice) in enumerate(zip(self.ideals, self.lattices)):
            if self.legacy:
                neighbors = self.module.cyclic_submodules(ideal, ZZ(prime))
            else:
                neighbors = morita_neighbors(self.order, ideal, lattice, split)
            row, seen, lines = [], set(), set()
            for neighbor in neighbors:
                relative = lattice.coordinates(neighbor.basis()).change_ring(ZZ)
                require(abs(relative.det()) == prime**2 and (prime * relative.inverse()).denominator() == 1,
                        f"neighbor is not an index-{prime**2} lattice between qI and I")
                key = tuple(relative.hermite_form().list())
                require(key not in seen, "duplicate neighbor lattice")
                seen.add(key)
                j, alpha = self.classify(neighbor)
                maps = self.transport(i, j, alpha, prime)
                if prime in maps:
                    lines.add(line_key(maps[prime], prime))
                row.append(dict(index=j, **self.encode(maps)))
            # A split maximal order has exactly q+1 such right sublattices.
            require(len(seen) == prime + 1, f"incomplete T_{prime} lattice row {i}")
            if prime in self.frames:
                require(lines == set(range(prime + 1)), f"incomplete local flag cover for T_{prime}, row {i}")
            rows.append(row)
            counts.append(Counter(edge["index"] for edge in row))
        for i, row in enumerate(counts):
            for j, multiplicity in row.items():
                require(multiplicity * self.weights[j] == counts[j][i] * self.weights[i],
                        f"T_{prime} fails weighted reciprocity")
        return rows

    def atkin_lehner(self):
        prime = ramified_prime(self.order, self.ell)
        edges, alphas, transports = [], [], []
        for i, ideal in enumerate(self.ideals):
            neighbor = ideal * prime
            relative = self.lattices[i].coordinates(neighbor.basis()).change_ring(ZZ)
            require(abs(relative.det()) == self.ell**2, "wrong index of I times the two-sided prime")
            j, alpha = self.classify(neighbor)
            maps = self.transport(i, j, alpha, self.ell)
            edges.append(dict(index=j, **self.encode(maps)))
            alphas.append(alpha)
            transports.append(maps)
        for i, edge in enumerate(edges):
            j = edge["index"]
            require(edges[j]["index"] == i, "ramified class permutation is not an involution")
            unit = alphas[i] * alphas[j] / self.ell
            unit_maps = self.transport(i, i, unit, 1)
            for r, unit_map in unit_maps.items():
                require(transports[i][r] * transports[j][r] == self.ell * unit_map,
                        f"ramified transport square is not scalar times a unit at {r}")
        return edges


def level_depths(case):
    """Read the prime support of N and return the local matrix precisions."""
    p, N = int(case["p"]), int(case["N"])
    listed = [int(q) for q in case["levels"]]
    levels = sorted(set(listed) | {p})
    if listed != sorted(set(listed)) or N < 2 or any(not ZZ(r).is_prime() for r in levels):
        raise ValueError("levels must be distinct sorted primes of the conductor")
    depths = {}
    remaining = N
    for r in levels:
        exponent = 0
        while remaining % r == 0:
            remaining //= r
            exponent += 1
        if exponent == 0:
            raise ValueError("levels must divide the conductor")
        depths[r] = 3 if r == p else exponent
    if remaining != 1:
        raise ValueError("levels together with p must give the prime support of N")
    return depths


def cm_polynomial(D):
    if D % 4 == 0:
        fundamental = (D//4) % 4 in (2, 3) and ZZ(abs(D//4)).is_squarefree()
    else:
        fundamental = D % 4 == 1 and ZZ(abs(D)).is_squarefree()
    if D >= 0 or not fundamental:
        raise ValueError("D must be a negative fundamental discriminant")
    trace = D % 2
    return trace, (trace**2 - D)//4


def build(case, ell, directory, primes):
    """Build classes.json, q{prime}.json, and well{ell}.json in directory."""
    D, ell = int(case["D"]), int(ell)
    cm_polynomial(D)
    primes = tuple(dict.fromkeys(int(q) for q in primes))
    if any(q == ell or not ZZ(q).is_prime() for q in primes):
        raise ValueError("graph primes must be prime and different from ell")

    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=True)
    graph = BrandtGraph.from_case(case, ell)
    save(directory / "classes.json", graph.class_data(D))
    save(directory / f"well{ell}.json", graph.atkin_lehner())
    for prime in primes:
        rows = graph.hecke(prime)
        save(directory / f"q{prime}.json", rows)
        print("complete", prime, len(rows), flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("case", type=Path, help="JSON input")
    parser.add_argument("ell", type=int)
    parser.add_argument("directory", type=Path)
    parser.add_argument("primes", type=int, nargs="*")
    args = parser.parse_args()
    build(json.loads(args.case.read_text()), args.ell, args.directory, args.primes)
