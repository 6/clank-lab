"""Small-case Brandt completeness checker using independent Hom-lattice enumeration."""

import argparse
import json
from collections import Counter
from pathlib import Path

from sage.all import BrandtModule, set_random_seed


def check(condition, message):
    if not condition:
        raise ValueError(message)


def read(directory, name):
    return json.loads((directory / name).read_text())


def lattice_maps(ideals, degree):
    """Recover the class multiplicities from the degree shell of each Hom lattice."""
    norms = [ideal.norm() for ideal in ideals]
    counts = []
    for i, row in enumerate(ideals):
        multiplicities = Counter()
        all_lattices = set()
        for j, source in enumerate(ideals):
            hom = row.multiply_by_conjugate(source)
            norm = hom.norm()
            check(norm == norms[i] * norms[j], "Hom lattice norm")
            vectors = hom.quadratic_form().short_vector_list_up_to_length(degree + 1)[degree]
            seen = set()
            for v in vectors:
                alpha = sum(c * b for c, b in zip(v, hom.basis())) / norms[j]
                image = alpha * source
                check(alpha.reduced_norm() * norms[j] == degree * norms[i],
                      "wrong Hom degree")
                check(all(x in row for x in image.basis())
                      and all(degree*x in image for x in row.basis()),
                      "Hom image outside the required interval")
                seen.add(tuple(image.basis_matrix().list()))
            if seen:
                check(all_lattices.isdisjoint(seen), "two classes give the same Hom image")
                all_lattices.update(seen)
                multiplicities[j] = len(seen)
        expected = 1 if degree == ideals[0].quaternion_algebra().discriminant() else degree + 1
        check(len(all_lattices) == expected, f"incomplete Hom enumeration for degree {degree}, row {i}")
        counts.append(multiplicities)
    return counts


def theta_counts(ideals, degree):
    """Count norm-degree transports modulo the units of the source ideal.

    Maps with the same image differ by a unique left-order unit of the
    source. Counting all signs in numerator and denominator avoids storing
    the vectors in every smaller norm shell.
    """
    units = [J.multiply_by_conjugate(J).theta_series_vector(2)[1] for J in ideals]
    counts = []
    for I in ideals:
        row = Counter()
        for j, J in enumerate(ideals):
            H = I.multiply_by_conjugate(J)
            check(H.norm() == I.norm()*J.norm(), "Hom lattice norm")
            n = H.theta_series_vector(degree + 1)[degree]
            quotient, remainder = divmod(n, units[j])
            check(remainder == 0, "unit orbit size in a nonzero norm shell")
            if quotient:
                row[j] = int(quotient)
        counts.append(row)
    return counts


def image_line(flat, prime):
    a, b, c, d = [value % prime for value in flat]
    check((a*d-b*c) % prime == 0, "local image is not a line")
    x, y = (a, c) if (a, c) != (0, 0) else (b, d)
    check(x or y, "zero local image")
    return y * pow(x, -1, prime) % prime if x else prime


def verify_cm_transports(case, ell, classes, rows):
    """Identify each CM vertex's outgoing p-correspondence inside its exact Hom shell."""
    from brandt import BrandtGraph

    graph = BrandtGraph.from_case(case, ell)
    p = case["p"]
    levels = sorted(graph.depths)

    def encoded_key(j, edge):
        return (j, *(tuple(edge[f"p{r}"]) for r in levels))

    for i in {cm["index"] for cm in classes["cm"]}:
        row = graph.ideals[i]
        wanted = {encoded_key(edge["index"], edge) for edge in rows[i]}
        check(len(wanted) == p+1, "repeated serialized CM transport")
        found = {}
        for j, source in enumerate(graph.ideals):
            if not any(edge["index"] == j for edge in rows[i]):
                continue
            hom = row.multiply_by_conjugate(source)
            vectors = hom.quadratic_form().short_vector_list_up_to_length(p+1)[p]
            for v in vectors:
                alpha = sum(c*b for c, b in zip(v, hom.basis())) / source.norm()
                maps = graph.encode(graph.transport(i, j, alpha, p))
                # The Hom enumeration can choose only one representative of ±v.
                for sign in (1, -1):
                    signed = {f"p{r}": [sign*x % r**graph.depths[r] for x in maps[f"p{r}"]]
                              for r in levels}
                    key = encoded_key(j, signed)
                    if key in wanted:
                        image = tuple((alpha * source).basis_matrix().list())
                        if key in found and found[key] != image:
                            raise ValueError("CM transport identifies distinct exact lattices")
                        found[key] = image
        check(set(found) == wanted and len(set(found.values())) == p+1,
              "CM transport fails exact Hom-lattice comparison")


def verify(case, ell, directory, primes):
    set_random_seed(817)
    ideals = BrandtModule(ell).right_ideals()
    levels = sorted(set(case["levels"]) | {case["p"]})
    moduli = {}
    for prime in levels:
        power = prime
        while case["N"] % (power * prime) == 0:
            power *= prime
        moduli[prime] = prime**3 if prime == case["p"] else power
    classes = read(directory, "classes.json")
    check(classes["ell"] == ell and len(classes["units"]) == len(ideals), "class metadata")

    for degree in (ell, *primes):
        if degree == ell:
            edges = read(directory, f"well{ell}.json")
            check(all(isinstance(e, dict) for e in edges), "ramified edges must be flat")
            rows = [[edge] for edge in edges]
        else:
            rows = read(directory, f"q{degree}.json")
        check(len(rows) == len(ideals), f"wrong number of rows at degree {degree}")
        counts = theta_counts(ideals, degree)
        if degree <= 97:
            check(counts == lattice_maps(ideals, degree), "theta and image-lattice counts differ")
        for i, row in enumerate(rows):
            check(Counter(edge["index"] for edge in row) == counts[i],
                  f"Hom multiplicity mismatch at degree {degree}, row {i}")
            for edge in row:
                for prime in levels:
                    modulus = moduli[prime]
                    flat = edge[f"p{prime}"]
                    check(len(flat) == 4 and all(type(x) is int and 0 <= x < modulus for x in flat),
                          "local matrix format")
                    a, b, c, d = flat
                    det = a*d-b*c
                    check((det % prime == 0) == (degree == prime), "local determinant")
                    if degree == prime and modulus > prime:
                        check(det % prime**2 != 0, "local determinant valuation")
            if degree in levels:
                lines = {image_line(edge[f"p{degree}"], degree) for edge in row}
                check(lines == set(range(degree + 1)), f"flag cover mismatch in row {i}")
        if degree == case["p"]:
            verify_cm_transports(case, ell, classes, rows)
        print(f"Hom counts agree at {degree} in {len(rows)} rows", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("case", type=Path)
    parser.add_argument("ell", type=int)
    parser.add_argument("directory", type=Path)
    parser.add_argument("primes", nargs="*", type=int)
    args = parser.parse_args()
    verify(json.loads(args.case.read_text()), args.ell, args.directory, args.primes)
