"""Evaluate the geometric ring-class theta element in F_p[C_p].

The graph and the normalized eigenfunction are upstream inputs. In particular
this calculation certifies no dimension for the residual Hecke eigenspace.
All values are in the supplied normalization, even when the eigenspace has
more than one possible line. The exact ideal maps and embedding enumeration
are supplied by the graph builder. Here we verify their local consequences.

For h(D)=1 and O_K^×={±1}, the ring-class exact sequence identifies
Pic(O_{p^n}) with (O_K/p^n)^×/(Z/p^n)^×. At inert p the column module is
free of rank one over the unramified quadratic ring, and the stabilizer of
a primitive line is precisely the scalar units modulo p^n. Its preimage in
O_K,p^× is the group of units of Z_p + p^n O_K,p. At each split tame q^e,
the two roots of the CM polynomial stay distinct modulo q. In an eigenbasis
their difference is a unit, so an eigenvector with a unit coordinate has
zero other coordinate. This gives exactly two stable projective flags.

For m = q^e, the tame indices 0,...,m-1 stand for (1,s), and the indices
m,...,m+m/q-1 stand for (q(s-m),1). The flat eigenvector orders classes and
then these indices lexicographically in ascending prime order. At exponent
one the numbering is 0,...,q-1 followed by infinity, as in the old graph.

For larger class number, the local projective torus acts within each Pic(O_K)
coset of Pic(O_{p^n}). To extend this calculation, supply ordered coset
representatives for each local orientation and the ring-class multiplication
relations, including the p-power relations of lifts of Pic(O_K). Evaluate the
local ray fibre at every coset and label it using that coset representative
before projecting the global group ring. In particular, independently choosing
origins for the local fibres need not give the global theta element.
"""

import json
from itertools import product
from math import isqrt, prod
from pathlib import Path


CLASS_NUMBER_ONE = {-7, -8, -11, -19, -43, -67, -163}
PIN = "1/2 + 25/64*i + 1/32*j - 3/64*k"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read(directory, filename):
    return json.loads((directory / filename).read_text())


def prime(q):
    return type(q) is int and q >= 2 and all(q % d for d in range(2, isqrt(q) + 1))


def symbol(D, q):
    if q == 2:
        return 0 if D % 2 == 0 else (1 if D % 8 in (1, 7) else -1)
    value = pow(D % q, (q-1)//2, q)
    return -1 if value == q-1 else value


def matmul(m, n):
    a, b, c, d = m
    e, f, g, h = n
    return a*e+b*g, a*f+b*h, c*e+d*g, c*f+d*h


def adj(m):
    a, b, c, d = m
    return d, -b, -c, a


def det(m):
    a, b, c, d = m
    return a*d-b*c


def apply(m, v):
    a, b, c, d = m
    x, y = v
    return a*x+b*y, c*x+d*y


def chart(v, p, modulus):
    x, y = v
    if x % p:
        return 1, y*pow(x, -1, modulus) % modulus
    require(y % p != 0, "nonprimitive ray")
    return x*pow(y, -1, modulus) % modulus, 1


def slope(v, q):
    return line_index(v, q, q)


def line_index(v, q, modulus):
    x, y = chart(v, q, modulus)
    return y if x == 1 else modulus+x//q


def column(s, q, modulus):
    return (1, s) if s < modulus else (q*(s-modulus), 1)


def action(m, s, q, modulus):
    return line_index(apply(m, column(s, q, modulus)), q, modulus)


def stable(m, s, q, modulus):
    # The primitive column spans a direct summand. The wedge vanishes
    # exactly when its image lies in that summand, even for singular omega.
    x, y = column(s, q, modulus)
    u, v = apply(m, (x, y))
    return (x*v-y*u) % modulus == 0


def fingerprint(m, modulus):
    return tuple(x % modulus for x in m)


def projective(m, q, modulus):
    pivot = next((x for x in m if x % q), None)
    require(pivot is not None, "zero projective matrix")
    scale = pow(pivot, -1, modulus)
    return fingerprint((scale*x for x in m), modulus)


def scalar_power(m, exponent, modulus):
    value = (1, 0, 0, 1)
    while exponent:
        if exponent % 2:
            value = fingerprint(matmul(value, m), modulus)
        m = fingerprint(matmul(m, m), modulus)
        exponent //= 2
    a, b, c, d = value
    return a == d and b == c == 0


def generator(w, p):
    factors = [q for q in range(2, p+2) if (p+1) % q == 0 and prime(q)]
    a, b, c, d = w
    for shift in range(2*p):
        candidate = a+shift, b, c, d+shift
        if (not any(scalar_power(candidate, (p+1)//q, p) for q in factors)
                and not scalar_power(candidate, p+1, p*p)):
            return shift, candidate
    # The p shifts a=0,...,p-1 and infinity represent the entire tame torus.
    # Adding p to a lift multiplies it by 1+p/(a+w), which is nonscalar
    # modulo p^2, so a primitive tame lift works in one of the two passes.
    raise ValueError("no generator of the local projective torus")


def matrix(record, q, modulus):
    result = record[f"p{q}"]
    require(isinstance(result, list) and len(result) == 4
            and all(type(x) is int and 0 <= x < modulus for x in result),
            f"invalid matrix p{q}")
    return tuple(result)


def is_pin(case, ell):
    return (case["p"], case["D"], case["N"], ell, tuple(case["ainvs"])) == (
        19, -7, 817, 269, (0, 1, 1, 1, 6))


def precision(source, records, p, field, minimum):
    key = f"p{p}"
    observed = max(x for record in records for x in record[key])
    inferred = next((n for n in range(minimum, 4) if observed < p**n), 4)
    result = source.get(field, inferred)
    require(type(result) is int and inferred <= result <= 3, f"invalid {field}")
    return result


def evaluate(case, ell, directory):
    """Return the chosen coefficient vector and checks for every CM variant.

    Format: classes.json has all raw embeddings and all projective units,
    including the identity. Legacy unit lists may include both signs.
    Embeddings use a common generator of trace D % 2 (or omega_trace).
    Graph and embedding matrices at p have precision p^2 or p^3, while the
    eigenvector uses depth-one flags at p. Every tame matrix and flag uses
    modulus q^e, where q^e is the exact power of q in N. Matrix entries use
    least nonnegative residues. Optional classes.json fields p_depth,
    cm_p_depth and unit_p_depth declare precision when digits are inconclusive.
    """
    directory = Path(directory)
    D, p, ap, vdelta = (case[key] for key in ("D", "p", "ap", "vdelta"))
    levels = tuple(case["levels"])
    require(D in CLASS_NUMBER_ONE, "unsupported discriminant or class number > 1")
    require(prime(p) and p >= 5 and prime(ell), "requires prime p >= 5 and prime ell")
    require(levels == tuple(sorted(set(levels))) and p in levels
            and all(prime(q) for q in levels) and ell not in levels,
            "invalid level primes")
    remaining = case["N"]
    require(type(remaining) is int and remaining > 0, "invalid level")
    level_moduli = []
    for q in levels:
        modulus = 1
        while remaining % q == 0:
            modulus *= q
            remaining //= q
        require(modulus > 1 and (q != p or modulus == p), "invalid level exponent")
        level_moduli.append(modulus)
    require(remaining == 1, "level primes do not exhaust N")
    level_factors = tuple(zip(levels, level_moduli))
    tame_factors = tuple((q, m) for q, m in level_factors if q != p)
    flag_sizes = tuple(m+m//q for q, m in level_factors)
    require(symbol(D, p) == symbol(D, ell) == -1, "p and ell must be inert")
    tame = tuple(q for q in levels if q != p)
    require(all(symbol(D, q) == 1 for q in tame), "tame level must split")
    require(type(ap) is int and ap in (-1, 1) and type(vdelta) is int and vdelta > 0,
            "invalid a_p or vdelta")

    data = read(directory, "classes.json")
    raw_units, cm = data["units"], data["cm"]
    raw_rows = read(directory, f"q{p}.json")
    require(data["ell"] == ell and raw_units and cm and all(raw_units),
            "missing classes, units or CM embeddings")
    count = len(raw_units)
    require(len(raw_rows) == count, "wrong number of p-graph rows")
    require(all(len(row) == p+1 for row in raw_rows), "p-graph ray cover: missing or extra edge")
    depth = precision(data, [e for row in raw_rows for e in row], p, "p_depth", 2)
    cm_depth = precision(data, cm, p, "cm_p_depth", 2)
    unit_depth = precision(data, [u for row in raw_units for u in row],
                           p, "unit_p_depth", 1)
    moduli = [p**depth if q == p else m for q, m in level_factors]
    cm_moduli = [p**cm_depth if q == p else m for q, m in level_factors]
    unit_moduli = [p**unit_depth if q == p else m for q, m in level_factors]
    p_position = levels.index(p)

    units = []
    for row in raw_units:
        projective_reps = {}
        listed = set()
        for record in row:
            unit = tuple(matrix(record, q, m) for q, m in zip(levels, unit_moduli))
            require(unit not in listed, "repeated unit record")
            listed.add(unit)
            require(all(det(A) % m == 1 for A, m in zip(unit, unit_moduli)),
                    "nonunit in units")
            key = projective(unit[p_position], p, p)
            if key in projective_reps:
                negative = tuple(fingerprint((-x for x in A), m)
                                 for A, m in zip(unit, unit_moduli))
                require(negative == projective_reps[key], "inconsistent projective units")
            else:
                projective_reps[key] = unit
        group = list(projective_reps.values())
        keys = {tuple(projective(A, q, m) for A, (q, m) in zip(unit, level_factors))
                for unit in group}
        require(tuple((1, 0, 0, 1) for q in levels) in keys, "missing identity in units")
        for u in group:
            for v in group:
                require(tuple(projective(matmul(a, b), q, m)
                              for a, b, (q, m) in zip(u, v, level_factors)) in keys,
                        "unit action is not closed")
        units.append(group)

    rows = []
    for row in raw_rows:
        by_image = {}
        for edge in row:
            target = edge["index"]
            require(type(target) is int and 0 <= target < count, "invalid edge target")
            ms = [matrix(edge, q, m) for q, m in zip(levels, moduli)]
            a, b, c, d = ms[p_position]
            determinant = a*d-b*c
            require(determinant % p == 0 and determinant % (p*p) != 0,
                    "p-graph edge determinant must have valuation one")
            image = slope((a, c) if a % p or c % p else (b, d), p)
            require(image not in by_image, "p-graph ray cover: duplicate image")
            tm = [m for j, m in enumerate(ms) if j != p_position]
            require(all(det(m) % q for m, q in zip(tm, tame)),
                    "singular tame transport")
            by_image[image] = target, adj(ms[p_position]), tuple(map(adj, tm))
        rows.append(by_image)

    g = read(directory, "eigen.json")
    require(isinstance(g, list) and len(g) == count*prod(flag_sizes)
            and all(type(v) is int and 0 <= v < p for v in g)
            and next((v for v in g if v), 0) == 1, "eigen normalization or shape")

    sampled = {}

    def value(index, flags):
        state = (index, *flags)
        if state not in sampled:
            def lookup(local_flags):
                key = index
                for s, size in zip(local_flags, flag_sizes):
                    key = key*size+s
                return g[key]

            coefficient = lookup(flags)
            stabilizer = 0
            for unit in units[index]:
                moved = tuple(action(A, s, q, m)
                              for A, s, (q, m) in zip(unit, flags, level_factors))
                require(lookup(moved) == coefficient, "eigen values violate unit invariance")
                stabilizer += moved == flags
            require(stabilizer > 0 and len(units[index]) % stabilizer == 0,
                    "invalid terminal stabilizer")
            sampled[state] = coefficient, str(stabilizer)
        return sampled[state]

    def descend(index, flags, ray, n):
        modulus = p**n
        while modulus > p:
            target, inverse, transports = rows[index][slope(ray, p)]
            # The primitive line reduces to this index-p lattice's image.
            # Its coordinates there are adj(alpha) times the column divided
            # by p, up to the unit det(alpha)/p. One digit is lost per step.
            x, y = apply(inverse, ray)
            require(x % p == y % p == 0, "p-graph edge does not lift ray")
            modulus //= p
            ray = chart((x//p, y//p), p, modulus)
            flags = tuple(action(A, s, q, m)
                          for A, s, (q, m) in zip(transports, flags, tame_factors))
            index = target
        s = slope(ray, p)
        return value(index, flags[:p_position] + (s,) + flags[p_position:])

    trace = data.get("omega_trace", D % 2)
    require(type(trace) is int and (trace*trace-D) % 4 == 0, "invalid omega trace")
    norm = (trace*trace-D)//4
    by_class = {}
    names = set()
    for rec in cm:
        index, name = rec["index"], rec["omega"]
        require(type(index) is int and 0 <= index < count and isinstance(name, str)
                and name and (index, name) not in names, "duplicate or invalid embedding")
        names.add((index, name))
        ms = tuple(matrix(rec, q, m) for q, m in zip(levels, cm_moduli))
        require(all((m[0]+m[3]-trace) % modulus == 0
                    and (det(m)-norm) % modulus == 0 for m, modulus in zip(ms, cm_moduli)),
                "CM matrix has wrong trace or norm")
        by_class.setdefault(index, {})[name] = ms

    # Eichler's embedding count is 2 h(D), as ell is inert. The centralizer
    # of an embedding among the units is ±1. Conjugation swaps the two
    # orientations at ell, since the residue field at the division prime is
    # commutative and sees the two distinct roots. Both therefore lie in
    # the same maximal-order fibre. The count checks a gap in the raw list
    # conditional on its exact global elements and units being genuine.
    require(len(by_class) == 1, "CM embedding class cover")
    index, embeddings = next(iter(by_class.items()))
    require(len(embeddings) == 2*len(units[index]), "CM embedding count")
    full_local = {ms: name for name, ms in embeddings.items()}
    require(len(full_local) == len(embeddings), "duplicate CM matrix records")

    # A difference between two embedded generators of the same norm and
    # trace has norm at most |D| in the definite algebra. Congruence modulo
    # p^2 in the split left order forces its norm to be divisible by p^4.
    # Thus local p^2 conjugation pairing is exact for the supported D,p.
    conjugates = {}
    for name, ms in embeddings.items():
        conjugate = tuple(fingerprint((trace-m[0], -m[1], -m[2], trace-m[3]), k)
                          for m, k in zip(ms, cm_moduli))
        require(conjugate in full_local and full_local[conjugate] != name,
                "missing conjugate CM embedding")
        conjugates[name] = full_local[conjugate]

    # At legacy unit precision, a mod-p orbit can merge two exact orbits.
    # Retain every raw variant, marking the quotient only if disambiguated.
    local_moduli = [min(m, n) for m, n in zip(cm_moduli, unit_moduli)]
    local_names = {}
    for name, ms in embeddings.items():
        key = tuple(fingerprint(m, k) for m, k in zip(ms, local_moduli))
        local_names.setdefault(key, set()).add(name)
    unit_orbits = set()
    exact_quotient = True
    for name, ms in embeddings.items():
        matches = set()
        for unit in units[index]:
            key = tuple(fingerprint(matmul(matmul(u, m), adj(u)), k)
                        for u, m, k in zip(unit, ms, local_moduli))
            require(key in local_names, "CM embeddings are not closed under units")
            matches.update(local_names[key])
        require(len(matches) in (len(units[index]), len(embeddings)), "CM unit orbit size")
        if len(matches) == len(embeddings):
            exact_quotient = False
        else:
            unit_orbits.add(tuple(sorted(matches)))

    ray_counts = [(p+1)*p**n for n in range(depth)]
    variants = []
    for name, ms in sorted(embeddings.items()):
        a, _, c, _ = ms[p_position]
        # Inertness makes c a unit. When only the first two CM digits are
        # available, lift the basis (e_1, omega e_1) from its first column.
        # The lifted matrix has the same polynomial. Its labels agree
        # through depth two, which suffices for every norm check at depth three.
        modulus = p**depth
        b = (a*(trace-a)-norm)*pow(c, -1, modulus) % modulus
        shift, gen = generator((a, b, c, (trace-a) % modulus), p)
        stable_choices = [tuple(s for s in range(size) if stable(A, s, q, m))
                          for j, (A, (q, m), size) in enumerate(zip(ms, level_factors, flag_sizes))
                          if j != p_position]
        require(all(len(s) == 2 for s in stable_choices), "CM stable tame line cover")
        for flags in product(*stable_choices):
            histograms = []
            previous = None
            for n, size in enumerate(ray_counts, 1):
                modulus = p**n
                v = (1, 0)
                seen = set()
                values = []
                histogram = {}
                for _ in range(size):
                    require(v not in seen, "local generator repeats a ray")
                    seen.add(v)
                    a, stabilizer = descend(index, flags, v, n)
                    values.append(a)
                    histogram[stabilizer] = histogram.get(stabilizer, 0)+1
                    v = chart(apply(gen, v), p, modulus)
                require(v == (1, 0), "local generator does not close")
                histograms.append(histogram)
                if previous is None:
                    require(sum(values) % p == 0, "depth-one augmentation")
                else:
                    # Reduction of the same labelled generator orbit is
                    # reduction of exponents modulo the smaller orbit size.
                    # Check norm compatibility in every individual fibre.
                    block_size = len(previous)
                    for i, a in enumerate(previous):
                        require((sum(values[i::block_size])-ap*a) % p == 0,
                                f"depth-{n} norm compatibility")
                if n == 2:
                    # Values are supplied as evaluations on individual
                    # flags. Stabilizers are checked without weighting them.
                    # The projection sums each tame fibre, and the normalization
                    # at conductor p^2 is vdelta * a_p^(-2).
                    coeff = [vdelta*pow(ap, -2, p)*sum(values[i::p]) % p for i in range(p)]
                previous = values
            # In F_p[C_p], gamma^j=(1+X)^j=1+jX modulo X^2.
            moment = sum(j*c for j, c in enumerate(coeff)) % p
            # The ray charts have exactly size elements. Distinct orbit
            # elements prove transitivity. Changing base ray by gen^r
            # cyclically translates the coefficients and changes the moment
            # by -r times augmentation, which is zero by the norm checks.
            require(sum(coeff) % p == 0, "theta augmentation")
            variants.append(dict(index=index, omega=name, conjugate_omega=conjugates[name],
                                 tame_flags=list(flags), generator_shift=shift,
                                 coefficients=coeff, first_moment=moment,
                                 terminal_stabilizers=histograms))
    per_variant = {(v["omega"], tuple(v["tame_flags"])): v["coefficients"] for v in variants}
    for (name, flags), coeff in per_variant.items():
        conjugate = per_variant[conjugates[name], flags]
        require(conjugate == [coeff[-i % p] for i in range(p)], "CM conjugation on theta")

    selected = variants[0]
    pinned = is_pin(case, ell)
    if pinned:
        choices = [v for v in variants if (v["index"], v["omega"], v["tame_flags"],
                                             v["generator_shift"]) == (19, PIN, [22], 0)]
        require(len(choices) == 1, "missing pinned 817 CM coordinates")
        selected = choices[0]

    return dict(first_moment=selected["first_moment"], coefficients=selected["coefficients"],
                checks=dict(class_number=1, embedding_orbit_count=2,
                            embedding_records=len(embeddings),
                            unit_orbits=[list(orbit) for orbit in sorted(unit_orbits)]
                            if exact_quotient else None,
                            ray_counts=ray_counts, base_ray=[1, 0], tame_primes=list(tame),
                            conjugation_inverts=True, base_ray_moments_invariant=True,
                            augmentation=0, norm_compatible=True, pinned_817=pinned,
                            selected_variant=variants.index(selected), variants=variants))


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("case", type=Path)
    parser.add_argument("ell", type=int)
    parser.add_argument("directory", type=Path)
    parser.add_argument("certificate", type=Path, nargs="?")
    args = parser.parse_args()
    result = evaluate(json.loads(args.case.read_text()), args.ell, args.directory)
    if args.certificate is not None:
        expected = json.loads(args.certificate.read_text())
        require(json.dumps(expected["coefficients"]) == json.dumps(result["coefficients"]),
                "theta coefficients")
        require(json.dumps(expected, sort_keys=True) == json.dumps(result, sort_keys=True),
                "theta check data")
    print(json.dumps(result))
